import GolzHaghtalabYang2025Distortion.Theorem5
import GolzHaghtalabYang2025Distortion.EmpiricalCondorcet
import AppliedModelingLib.Learning.HumanFeedback.BradleyTerryFit
import AppliedModelingLib.Learning.HumanFeedback.PairwiseReportCounts

/-!
# Finite-report Borda selection for Theorem 12

The finite-sample sentence in Appendix E.2 concerns normalized Borda counts,
not an average of independent, already-normalized candidate scores.  This
module records the needed finite-report reduction: a strict population Borda
winner is selected with probability tending to one when iid reports have
calibrated expected win and comparison counts.  A report may contain any
within-user dependence; only reports from distinct users are iid.
-/

namespace GolzHaghtalabYang2025Distortion

open scoped BigOperators Topology

open AppliedModelingLib
open AppliedModelingLib.Probability
open AppliedModelingLib.Learning.HumanFeedback
open AppliedModelingLib.Alignment.Welfare

/-- The iid batch law for the finite user reports used by normalized Borda. -/
noncomputable def theorem12IidBordaReportBatchLaw
    {Report : Type*} [Fintype Report] [DecidableEq Report]
    (reportLaw : PMF Report) (horizon : ℕ) : PMF (Fin horizon → Report) :=
  pmfProduct (Fin horizon) Report reportLaw

/-- Aggregate Borda wins of one alternative over a finite report batch. -/
def theorem12EmpiricalBordaWins
    {Report Alternative : Type*} [Fintype Alternative]
    (wins : Alternative → Report → ℝ) (alternative : Alternative) {horizon : ℕ}
    (sample : Fin horizon → Report) : ℝ :=
  finiteIidScoreSum (wins alternative) sample

/-- Aggregate Borda comparison incidences of one alternative over a report batch. -/
def theorem12EmpiricalBordaIncidences
    {Report Alternative : Type*} [Fintype Alternative]
    (incidences : Alternative → Report → ℝ) (alternative : Alternative) {horizon : ℕ}
    (sample : Fin horizon → Report) : ℝ :=
  finiteIidScoreSum (incidences alternative) sample

/--
The source's normalized finite Borda score.  The zero-denominator convention
is harmless for the asymptotic result below and makes the score total at every
finite horizon.
-/
noncomputable def theorem12EmpiricalBordaScore
    {Report Alternative : Type*} [Fintype Alternative]
    (wins incidences : Alternative → Report → ℝ) (alternative : Alternative) {horizon : ℕ}
    (sample : Fin horizon → Report) : ℝ :=
  if theorem12EmpiricalBordaIncidences incidences alternative sample = 0 then 0
  else theorem12EmpiricalBordaWins wins alternative sample /
    theorem12EmpiricalBordaIncidences incidences alternative sample

/-- Failure of `winner` to be a strict normalized-count Borda winner. -/
abbrev theorem12IidEmpiricalBordaFailure
    {Report Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (wins incidences : Alternative → Report → ℝ) (winner : Alternative) {horizon : ℕ}
    (sample : Fin horizon → Report) : Prop :=
  ∃ ordinary : {ordinary : Alternative // ordinary ≠ winner},
    theorem12EmpiricalBordaScore wins incidences winner sample ≤
      theorem12EmpiricalBordaScore wins incidences ordinary.1 sample

/-- Summing a one-report affine Borda margin agrees with affine aggregate counts. -/
theorem theorem12_finiteIidScoreSum_win_sub_mul_incidence
    {Report Alternative : Type*} [Fintype Alternative]
    (wins incidences : Alternative → Report → ℝ) (alternative : Alternative) (threshold : ℝ)
    {horizon : ℕ} (sample : Fin horizon → Report) :
    finiteIidScoreSum (fun report => wins alternative report - threshold * incidences alternative report)
        sample =
      theorem12EmpiricalBordaWins wins alternative sample -
        threshold * theorem12EmpiricalBordaIncidences incidences alternative sample := by
  simp only [finiteIidScoreSum, theorem12EmpiricalBordaWins,
    theorem12EmpiricalBordaIncidences, Finset.sum_sub_distrib, Finset.mul_sum]

/-- Per-report win counts below incidence counts retain that order after aggregation. -/
theorem theorem12EmpiricalBordaWins_le_incidences
    {Report Alternative : Type*} [Fintype Alternative]
    (wins incidences : Alternative → Report → ℝ)
    (hwin_le_incidence : ∀ alternative report, wins alternative report ≤ incidences alternative report)
    (alternative : Alternative) {horizon : ℕ} (sample : Fin horizon → Report) :
    theorem12EmpiricalBordaWins wins alternative sample ≤
      theorem12EmpiricalBordaIncidences incidences alternative sample := by
  change finiteIidScoreSum (wins alternative) sample ≤ finiteIidScoreSum (incidences alternative) sample
  exact Finset.sum_le_sum fun index _ => hwin_le_incidence alternative (sample index)

/-- A zero aggregate incidence forces zero aggregate wins under the count bounds. -/
theorem theorem12EmpiricalBordaWins_eq_zero_of_incidences_eq_zero
    {Report Alternative : Type*} [Fintype Alternative]
    (wins incidences : Alternative → Report → ℝ)
    (hwin_nonneg : ∀ alternative report, 0 ≤ wins alternative report)
    (hwin_le_incidence : ∀ alternative report, wins alternative report ≤ incidences alternative report)
    (alternative : Alternative) {horizon : ℕ} (sample : Fin horizon → Report)
    (hincidences : theorem12EmpiricalBordaIncidences incidences alternative sample = 0) :
    theorem12EmpiricalBordaWins wins alternative sample = 0 := by
  have hnonneg : 0 ≤ theorem12EmpiricalBordaWins wins alternative sample := by
    change 0 ≤ finiteIidScoreSum (wins alternative) sample
    exact Finset.sum_nonneg fun index _ => hwin_nonneg alternative (sample index)
  have hle := theorem12EmpiricalBordaWins_le_incidences wins incidences hwin_le_incidence
    alternative sample
  linarith

/-- A low normalized score yields the nonpositive affine margin used for its tail bound. -/
theorem theorem12_empiricalBordaScore_le_imp_margin_nonpos
    {Report Alternative : Type*} [Fintype Alternative]
    (wins incidences : Alternative → Report → ℝ)
    (hwin_nonneg : ∀ alternative report, 0 ≤ wins alternative report)
    (hwin_le_incidence : ∀ alternative report, wins alternative report ≤ incidences alternative report)
    (alternative : Alternative) (threshold : ℝ)
    {horizon : ℕ} (sample : Fin horizon → Report)
    (hscore : theorem12EmpiricalBordaScore wins incidences alternative sample ≤ threshold) :
    finiteIidScoreSum
        (fun report => wins alternative report - threshold * incidences alternative report) sample ≤ 0 := by
  rw [theorem12_finiteIidScoreSum_win_sub_mul_incidence]
  unfold theorem12EmpiricalBordaScore at hscore
  by_cases hzero : theorem12EmpiricalBordaIncidences incidences alternative sample = 0
  · rw [if_pos hzero] at hscore
    rw [theorem12EmpiricalBordaWins_eq_zero_of_incidences_eq_zero wins incidences
      hwin_nonneg hwin_le_incidence alternative sample hzero, hzero]
    norm_num
  · rw [if_neg hzero] at hscore
    have hinc_nonneg : 0 ≤ theorem12EmpiricalBordaIncidences incidences alternative sample := by
      have hwin_nonneg_sum : 0 ≤ theorem12EmpiricalBordaWins wins alternative sample := by
        change 0 ≤ finiteIidScoreSum (wins alternative) sample
        exact Finset.sum_nonneg fun index _ => hwin_nonneg alternative (sample index)
      have hwin_le := theorem12EmpiricalBordaWins_le_incidences wins incidences
        hwin_le_incidence alternative sample
      linarith
    have hinc_pos : 0 < theorem12EmpiricalBordaIncidences incidences alternative sample :=
      lt_of_le_of_ne hinc_nonneg (Ne.symm hzero)
    have hmain := (div_le_iff₀ hinc_pos).mp hscore
    linarith

/-- A high normalized score yields the complementary nonpositive affine margin. -/
theorem theorem12_le_empiricalBordaScore_imp_margin_nonpos
    {Report Alternative : Type*} [Fintype Alternative]
    (wins incidences : Alternative → Report → ℝ)
    (hwin_nonneg : ∀ alternative report, 0 ≤ wins alternative report)
    (hwin_le_incidence : ∀ alternative report, wins alternative report ≤ incidences alternative report)
    (alternative : Alternative) (threshold : ℝ) (hthreshold : 0 < threshold)
    {horizon : ℕ} (sample : Fin horizon → Report)
    (hscore : threshold ≤ theorem12EmpiricalBordaScore wins incidences alternative sample) :
    finiteIidScoreSum
        (fun report => threshold * incidences alternative report - wins alternative report) sample ≤ 0 := by
  rw [show finiteIidScoreSum
      (fun report => threshold * incidences alternative report - wins alternative report) sample =
      threshold * theorem12EmpiricalBordaIncidences incidences alternative sample -
        theorem12EmpiricalBordaWins wins alternative sample by
    simp only [finiteIidScoreSum, theorem12EmpiricalBordaWins,
      theorem12EmpiricalBordaIncidences, Finset.sum_sub_distrib, Finset.mul_sum]]
  unfold theorem12EmpiricalBordaScore at hscore
  by_cases hzero : theorem12EmpiricalBordaIncidences incidences alternative sample = 0
  · rw [if_pos hzero] at hscore
    linarith
  · rw [if_neg hzero] at hscore
    have hinc_nonneg : 0 ≤ theorem12EmpiricalBordaIncidences incidences alternative sample := by
      have hwin_nonneg_sum : 0 ≤ theorem12EmpiricalBordaWins wins alternative sample := by
        change 0 ≤ finiteIidScoreSum (wins alternative) sample
        exact Finset.sum_nonneg fun index _ => hwin_nonneg alternative (sample index)
      have hwin_le := theorem12EmpiricalBordaWins_le_incidences wins incidences
        hwin_le_incidence alternative sample
      linarith
    have hinc_pos : 0 < theorem12EmpiricalBordaIncidences incidences alternative sample :=
      lt_of_le_of_ne hinc_nonneg (Ne.symm hzero)
    have hmain := (le_div_iff₀ hinc_pos).mp hscore
    linarith

/-- The midpoint between an ordinary and a proposed winning population score. -/
noncomputable def theorem12BordaMidpoint
    {Alternative : Type*} (populationScore : Alternative → ℝ)
    (winner ordinary : Alternative) : ℝ :=
  (populationScore winner + populationScore ordinary) / 2

/-- The winner-side affine margin at the corresponding population-score midpoint. -/
noncomputable def theorem12BordaWinnerMargin
    {Report Alternative : Type*} (wins incidences : Alternative → Report → ℝ)
    (populationScore : Alternative → ℝ) (winner ordinary : Alternative) (report : Report) : ℝ :=
  wins winner report - theorem12BordaMidpoint populationScore winner ordinary *
    incidences winner report

/-- The ordinary-side affine margin at the corresponding population-score midpoint. -/
noncomputable def theorem12BordaOrdinaryMargin
    {Report Alternative : Type*} (wins incidences : Alternative → Report → ℝ)
    (populationScore : Alternative → ℝ) (winner ordinary : Alternative) (report : Report) : ℝ :=
  theorem12BordaMidpoint populationScore winner ordinary * incidences ordinary report -
    wins ordinary report

/--
If a proposed winner fails to beat an ordinary alternative in normalized
finite Borda score, one of the two midpoint affine margins has nonpositive
aggregate score.
-/
theorem theorem12_iidEmpiricalBordaFailure_imp_exists_midpoint_tail
    {Report Alternative : Type*} [Fintype Report] [DecidableEq Report]
    [Fintype Alternative] [DecidableEq Alternative]
    (wins incidences : Alternative → Report → ℝ) (populationScore : Alternative → ℝ)
    (winner : Alternative)
    (hwin_nonneg : ∀ alternative report, 0 ≤ wins alternative report)
    (hwin_le_incidence : ∀ alternative report, wins alternative report ≤ incidences alternative report)
    (hscore_nonneg : ∀ alternative, 0 ≤ populationScore alternative)
    (hstrict : ∀ ordinary, ordinary ≠ winner → populationScore ordinary < populationScore winner)
    {horizon : ℕ} (sample : Fin horizon → Report)
    (hfailure : theorem12IidEmpiricalBordaFailure wins incidences winner sample) :
    ∃ key : Bool × {ordinary : Alternative // ordinary ≠ winner},
      finiteIidScoreSum
          (if key.1 then theorem12BordaWinnerMargin wins incidences populationScore winner key.2.1
            else theorem12BordaOrdinaryMargin wins incidences populationScore winner key.2.1)
          sample ≤ 0 := by
  rcases hfailure with ⟨ordinary, hfailure⟩
  let midpoint := theorem12BordaMidpoint populationScore winner ordinary.1
  have hwinner_pos : 0 < populationScore winner := by
    have hordinary_nonneg := hscore_nonneg ordinary.1
    have hstrict' := hstrict ordinary.1 ordinary.2
    linarith
  have hmidpoint_pos : 0 < midpoint := by
    dsimp [midpoint, theorem12BordaMidpoint]
    linarith [hscore_nonneg ordinary.1]
  by_cases hwinner_low :
      theorem12EmpiricalBordaScore wins incidences winner sample ≤ midpoint
  · refine ⟨(true, ordinary), ?_⟩
    simpa [midpoint, theorem12BordaWinnerMargin] using
      (theorem12_empiricalBordaScore_le_imp_margin_nonpos wins incidences hwin_nonneg
        hwin_le_incidence winner midpoint sample hwinner_low)
  · have hwinner_high : midpoint < theorem12EmpiricalBordaScore wins incidences winner sample :=
      lt_of_not_ge hwinner_low
    have hordinary_high : midpoint ≤
        theorem12EmpiricalBordaScore wins incidences ordinary.1 sample := by
      linarith
    refine ⟨(false, ordinary), ?_⟩
    simpa [midpoint, theorem12BordaOrdinaryMargin] using
      (theorem12_le_empiricalBordaScore_imp_margin_nonpos wins incidences hwin_nonneg
        hwin_le_incidence ordinary.1 midpoint hmidpoint_pos sample hordinary_high)

/-- The finite normalized-Borda failure probability is bounded by midpoint margin tails. -/
theorem theorem12_iidEmpiricalBordaFailure_le_sum_midpoint_tails
    {Report Alternative : Type*} [Fintype Report] [DecidableEq Report]
    [Fintype Alternative] [DecidableEq Alternative]
    (reportLaw : PMF Report) (wins incidences : Alternative → Report → ℝ)
    (populationScore : Alternative → ℝ) (winner : Alternative)
    (hwin_nonneg : ∀ alternative report, 0 ≤ wins alternative report)
    (hwin_le_incidence : ∀ alternative report, wins alternative report ≤ incidences alternative report)
    (hscore_nonneg : ∀ alternative, 0 ≤ populationScore alternative)
    (hstrict : ∀ ordinary, ordinary ≠ winner → populationScore ordinary < populationScore winner)
    (horizon : ℕ) :
    pmfProb (theorem12IidBordaReportBatchLaw reportLaw horizon)
      (fun sample => theorem12IidEmpiricalBordaFailure wins incidences winner sample) ≤
      ∑ key : Bool × {ordinary : Alternative // ordinary ≠ winner},
        finiteIidScoreLeftTailProb reportLaw
          (if key.1 then theorem12BordaWinnerMargin wins incidences populationScore winner key.2.1
            else theorem12BordaOrdinaryMargin wins incidences populationScore winner key.2.1)
          0 horizon := by
  classical
  let margin : Bool × {ordinary : Alternative // ordinary ≠ winner} → Report → ℝ :=
    fun key => if key.1 then
      theorem12BordaWinnerMargin wins incidences populationScore winner key.2.1
    else theorem12BordaOrdinaryMargin wins incidences populationScore winner key.2.1
  let bad : (Bool × {ordinary : Alternative // ordinary ≠ winner}) →
      (Fin horizon → Report) → Prop :=
    fun key sample => finiteIidScoreSum (margin key) sample ≤ 0
  calc
    pmfProb (theorem12IidBordaReportBatchLaw reportLaw horizon)
        (fun sample => theorem12IidEmpiricalBordaFailure wins incidences winner sample) ≤
      pmfProb (theorem12IidBordaReportBatchLaw reportLaw horizon)
        (fun sample => ∃ key, bad key sample) := by
          apply pmfProb_le_of_imp
          intro sample hfailure
          simpa [bad, margin] using
            (theorem12_iidEmpiricalBordaFailure_imp_exists_midpoint_tail wins incidences
              populationScore winner hwin_nonneg hwin_le_incidence hscore_nonneg hstrict sample
              hfailure)
    _ ≤ ∑ key : Bool × {ordinary : Alternative // ordinary ≠ winner},
        finiteIidScoreLeftTailProb reportLaw
          (if key.1 then theorem12BordaWinnerMargin wins incidences populationScore winner key.2.1
            else theorem12BordaOrdinaryMargin wins incidences populationScore winner key.2.1)
          0 horizon := by
          have hunion := pmfProb_exists_mem_le_sum
            (μ := theorem12IidBordaReportBatchLaw reportLaw horizon)
            (s := Finset.univ) (p := bad)
          simpa [bad, margin, theorem12IidBordaReportBatchLaw, finiteIidScoreLeftTailProb] using hunion

/-- Calibrated strict population Borda scores give positive winner-side midpoint means. -/
theorem theorem12_bordaWinnerMargin_pmfExp_pos
    {Report Alternative : Type*} [Fintype Report] [DecidableEq Report]
    [Fintype Alternative] [DecidableEq Alternative]
    (reportLaw : PMF Report) (wins incidences : Alternative → Report → ℝ)
    (populationScore : Alternative → ℝ) (winner ordinary : Alternative)
    (hcalibrated : ∀ alternative,
      pmfExp reportLaw (wins alternative) =
        populationScore alternative * pmfExp reportLaw (incidences alternative))
    (hincidences_pos : ∀ alternative, 0 < pmfExp reportLaw (incidences alternative))
    (hstrict : populationScore ordinary < populationScore winner) :
    0 < pmfExp reportLaw
      (theorem12BordaWinnerMargin wins incidences populationScore winner ordinary) := by
  have hrewrite :
      pmfExp reportLaw
          (theorem12BordaWinnerMargin wins incidences populationScore winner ordinary) =
        (populationScore winner - theorem12BordaMidpoint populationScore winner ordinary) *
          pmfExp reportLaw (incidences winner) := by
    unfold theorem12BordaWinnerMargin
    rw [pmfExp_sub, pmfExp_const_mul, hcalibrated]
    ring
  rw [hrewrite]
  apply mul_pos
  · unfold theorem12BordaMidpoint
    linarith
  · exact hincidences_pos winner

/-- Calibrated strict population Borda scores give positive ordinary-side midpoint means. -/
theorem theorem12_bordaOrdinaryMargin_pmfExp_pos
    {Report Alternative : Type*} [Fintype Report] [DecidableEq Report]
    [Fintype Alternative] [DecidableEq Alternative]
    (reportLaw : PMF Report) (wins incidences : Alternative → Report → ℝ)
    (populationScore : Alternative → ℝ) (winner ordinary : Alternative)
    (hcalibrated : ∀ alternative,
      pmfExp reportLaw (wins alternative) =
        populationScore alternative * pmfExp reportLaw (incidences alternative))
    (hincidences_pos : ∀ alternative, 0 < pmfExp reportLaw (incidences alternative))
    (hstrict : populationScore ordinary < populationScore winner) :
    0 < pmfExp reportLaw
      (theorem12BordaOrdinaryMargin wins incidences populationScore winner ordinary) := by
  have hrewrite :
      pmfExp reportLaw
          (theorem12BordaOrdinaryMargin wins incidences populationScore winner ordinary) =
        (theorem12BordaMidpoint populationScore winner ordinary - populationScore ordinary) *
          pmfExp reportLaw (incidences ordinary) := by
    unfold theorem12BordaOrdinaryMargin
    rw [pmfExp_sub, pmfExp_const_mul, hcalibrated]
    ring
  rw [hrewrite]
  apply mul_pos
  · unfold theorem12BordaMidpoint
    linarith
  · exact hincidences_pos ordinary

/--
For finite iid reports, calibrated normalized Borda counts select every strict
population winner with probability tending to one.  This is the finite-sample
bridge used by Theorem 12 after its concrete one-comparison report law is
shown to be calibrated.
-/
theorem theorem12_iidEmpiricalBordaFailure_tendsto_zero_of_calibrated_strict_winner
    {Report Alternative : Type*} [Fintype Report] [DecidableEq Report]
    [Fintype Alternative] [DecidableEq Alternative]
    (reportLaw : PMF Report) (wins incidences : Alternative → Report → ℝ)
    (populationScore : Alternative → ℝ) (winner : Alternative)
    (hwin_nonneg : ∀ alternative report, 0 ≤ wins alternative report)
    (hwin_le_incidence : ∀ alternative report, wins alternative report ≤ incidences alternative report)
    (hscore_nonneg : ∀ alternative, 0 ≤ populationScore alternative)
    (hcalibrated : ∀ alternative,
      pmfExp reportLaw (wins alternative) =
        populationScore alternative * pmfExp reportLaw (incidences alternative))
    (hincidences_pos : ∀ alternative, 0 < pmfExp reportLaw (incidences alternative))
    (hstrict : ∀ ordinary, ordinary ≠ winner → populationScore ordinary < populationScore winner) :
    Filter.Tendsto
      (fun horizon => pmfProb (theorem12IidBordaReportBatchLaw reportLaw horizon)
        (fun sample => theorem12IidEmpiricalBordaFailure wins incidences winner sample))
      Filter.atTop (𝓝 0) := by
  let margin : Bool × {ordinary : Alternative // ordinary ≠ winner} → Report → ℝ :=
    fun key => if key.1 then
      theorem12BordaWinnerMargin wins incidences populationScore winner key.2.1
    else theorem12BordaOrdinaryMargin wins incidences populationScore winner key.2.1
  have hmargin_pos : ∀ key, 0 < pmfExp reportLaw (margin key) := by
    intro key
    rcases key with ⟨side, ordinary⟩
    cases side
    · simpa [margin] using theorem12_bordaOrdinaryMargin_pmfExp_pos reportLaw wins incidences
        populationScore winner ordinary.1 hcalibrated hincidences_pos
        (hstrict ordinary.1 ordinary.2)
    · simpa [margin] using theorem12_bordaWinnerMargin_pmfExp_pos reportLaw wins incidences
        populationScore winner ordinary.1 hcalibrated hincidences_pos
        (hstrict ordinary.1 ordinary.2)
  have htail : ∀ key,
      Filter.Tendsto
        (fun horizon => finiteIidScoreLeftTailProb reportLaw (margin key) 0 horizon)
        Filter.atTop (𝓝 0) := by
    intro key
    obtain ⟨rate, hrate, hbound⟩ :=
      finiteIidScoreLeftTail_exists_pos_expUpperBoundWithConst_of_pmfExp_pos
        reportLaw (margin key) (hmargin_pos key)
    exact hbound.tendsto_zero_of_pos_rate hrate
  let tailSum : ℕ → ℝ := fun horizon =>
    ∑ key : Bool × {ordinary : Alternative // ordinary ≠ winner},
      finiteIidScoreLeftTailProb reportLaw (margin key) 0 horizon
  have htailSum : Filter.Tendsto tailSum Filter.atTop (𝓝 0) := by
    simpa [tailSum] using
      tendsto_finset_sum (Finset.univ : Finset (Bool × {ordinary : Alternative // ordinary ≠ winner}))
        (fun key _ => htail key)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds htailSum ?_ ?_
  · filter_upwards with horizon
    exact pmfProb_nonneg (theorem12IidBordaReportBatchLaw reportLaw horizon)
      (fun sample => theorem12IidEmpiricalBordaFailure wins incidences winner sample)
  · filter_upwards with horizon
    simpa [tailSum, margin] using
      (theorem12_iidEmpiricalBordaFailure_le_sum_midpoint_tails reportLaw wins incidences
        populationScore winner hwin_nonneg hwin_le_incidence hscore_nonneg hstrict horizon)

/-- A real Bernoulli report outcome with success probability in `[0,1]`. -/
noncomputable def theorem12BernoulliReport (probability : ℝ)
    (hnonneg : 0 ≤ probability) (hle_one : probability ≤ 1) : PMF Bool :=
  PMF.bernoulli ⟨probability, hnonneg⟩ (by
    change probability ≤ (1 : ℝ)
    exact hle_one)

/-- Expected true-indicator of the source's real Bernoulli report. -/
theorem theorem12_pmfExp_bernoulli_true
    (probability : ℝ) (hnonneg : 0 ≤ probability) (hle_one : probability ≤ 1) :
    pmfExp (theorem12BernoulliReport probability hnonneg hle_one)
      (fun outcome => if outcome then (1 : ℝ) else 0) = probability := by
  simp [pmfExp, theorem12BernoulliReport, PMF.bernoulli_apply]
  rfl

/-- Expected false-indicator of the source's real Bernoulli report. -/
theorem theorem12_pmfExp_bernoulli_false
    (probability : ℝ) (hnonneg : 0 ≤ probability) (hle_one : probability ≤ 1) :
    pmfExp (theorem12BernoulliReport probability hnonneg hle_one)
      (fun outcome => if outcome then (0 : ℝ) else 1) = 1 - probability := by
  simp [pmfExp, theorem12BernoulliReport, PMF.bernoulli_apply]
  rw [NNReal.coe_sub]
  · rfl
  · change probability ≤ (1 : ℝ)
    exact hle_one

/-- Expectation of an arbitrary real-valued function of one source Bernoulli
comparison outcome. -/
theorem theorem12_pmfExp_bernoulli_apply
    (probability : ℝ) (hnonneg : 0 ≤ probability) (hle_one : probability ≤ 1)
    (value : Bool → ℝ) :
    pmfExp (theorem12BernoulliReport probability hnonneg hle_one) value =
      probability * value true + (1 - probability) * value false := by
  simp [pmfExp, theorem12BernoulliReport, PMF.bernoulli_apply]
  rw [NNReal.coe_sub]
  · change probability * value true + (1 - probability) * value false =
      probability * value true + (1 - probability) * value false
    rfl
  · change probability ≤ (1 : ℝ)
    exact hle_one

/--
One source observation: two independently sampled alternatives and a binary
comparison outcome whose success probability is the aggregated pairwise
preference.  With one comparison per user this is exactly the marginal law of
the source's user-then-pair sampling experiment.
-/
noncomputable def theorem12OneComparisonReportLaw
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (sampling : PMF Alternative) (preference : PairwisePreference PUnit Alternative) :
    PMF ((Alternative × Alternative) × Bool) :=
  sampling.bind fun first =>
    sampling.bind fun second =>
      (theorem12BernoulliReport
        (preference.prob PUnit.unit first second)
        (preference.nonneg PUnit.unit first second)
        (preference.le_one PUnit.unit first second)).map
          (fun outcome => ((first, second), outcome))

/-- Under full candidate support and strictly interior pairwise preferences,
every direct-true ordered report atom has positive mass in the source's
one-comparison report law. -/
theorem theorem12OneComparisonReportLaw_directTrue_pos
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (sampling : PMF Alternative) (preference : PairwisePreference PUnit Alternative)
    (winner loser : Alternative)
    (hsampling : ∀ alternative, 0 < (sampling alternative).toReal)
    (hpreference : ∀ first second,
      0 < preference.prob PUnit.unit first second) :
    0 < (theorem12OneComparisonReportLaw sampling preference
      ((winner, loser), true)).toReal := by
  classical
  have hwinner : winner ∈ sampling.support := by
    rw [PMF.mem_support_iff]
    exact ne_of_gt (ENNReal.toReal_pos_iff.mp (hsampling winner)).1
  have hloser : loser ∈ sampling.support := by
    rw [PMF.mem_support_iff]
    exact ne_of_gt (ENNReal.toReal_pos_iff.mp (hsampling loser)).1
  have htrue : true ∈
      (theorem12BernoulliReport
        (preference.prob PUnit.unit winner loser)
        (preference.nonneg PUnit.unit winner loser)
        (preference.le_one PUnit.unit winner loser)).support := by
    rw [theorem12BernoulliReport, PMF.mem_support_bernoulli_iff]
    simp only [Bool.cond_true]
    apply ne_of_gt
    change 0 < preference.prob PUnit.unit winner loser
    exact hpreference winner loser
  have hinner : ((winner, loser), true) ∈
      (sampling.bind fun second =>
        (theorem12BernoulliReport
          (preference.prob PUnit.unit winner second)
          (preference.nonneg PUnit.unit winner second)
          (preference.le_one PUnit.unit winner second)).map
            (fun outcome => ((winner, second), outcome))).support := by
    rw [PMF.mem_support_bind_iff]
    refine ⟨loser, hloser, ?_⟩
    rw [PMF.mem_support_map_iff]
    exact ⟨true, htrue, rfl⟩
  have houter : ((winner, loser), true) ∈
      (sampling.bind fun first =>
        sampling.bind fun second =>
          (theorem12BernoulliReport
            (preference.prob PUnit.unit first second)
            (preference.nonneg PUnit.unit first second)
            (preference.le_one PUnit.unit first second)).map
              (fun outcome => ((first, second), outcome))).support := by
    rw [PMF.mem_support_bind_iff]
    exact ⟨winner, hwinner, hinner⟩
  have hsupported : ((winner, loser), true) ∈
      (theorem12OneComparisonReportLaw sampling preference).support := by
    simpa [theorem12OneComparisonReportLaw] using houter
  exact ENNReal.toReal_pos
    ((PMF.mem_support_iff _ _).mp hsupported)
    ((theorem12OneComparisonReportLaw sampling preference).apply_ne_top _)

/--
The population log likelihood of a literal one-comparison report under a
candidate logistic score.  The expectation is over the same ordered displays
and Boolean outcomes as the finite count dataset; diagonal displays are
retained in the report law but contribute zero to this objective.
-/
noncomputable def theorem12OneComparisonExpectedRawLogLikelihood
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (sampling : PMF Alternative) (preference : PairwisePreference PUnit Alternative)
    (score : PairwiseCountDataset.ScoreVector Alternative) : ℝ :=
  pmfExp (theorem12OneComparisonReportLaw sampling preference)
    (PairwiseCountDataset.binaryReportLogLikelihoodTerm Real.sigmoid score)

/--
The literal report likelihood has the expected ordered-pair cross-entropy
form.  In particular, the false outcome is accounted for as the reversed
directed win, rather than being dropped or replaced by a balanced design.
-/
theorem theorem12OneComparisonExpectedRawLogLikelihood_eq
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (sampling : PMF Alternative) (preference : PairwisePreference PUnit Alternative)
    (score : PairwiseCountDataset.ScoreVector Alternative) :
    theorem12OneComparisonExpectedRawLogLikelihood sampling preference score =
      pmfPairExp sampling sampling (fun first second =>
        if first = second then 0 else
          preference.prob PUnit.unit first second *
              Real.log (Real.sigmoid (score first - score second)) +
            (1 - preference.prob PUnit.unit first second) *
              Real.log (Real.sigmoid (score second - score first))) := by
  unfold theorem12OneComparisonExpectedRawLogLikelihood theorem12OneComparisonReportLaw
  rw [pmfExp_bind]
  apply pmfExp_congr
  intro first
  rw [pmfExp_bind]
  apply pmfExp_congr
  intro second
  rw [pmfExp_map]
  rw [theorem12_pmfExp_bernoulli_apply]
  by_cases hsame : first = second
  · subst second
    rw [PairwiseCountDataset.binaryReportLogLikelihoodTerm_diagonal,
      PairwiseCountDataset.binaryReportLogLikelihoodTerm_diagonal]
    simp
  · rw [PairwiseCountDataset.binaryReportLogLikelihoodTerm_direct_true
      Real.sigmoid score first second hsame]
    rw [PairwiseCountDataset.binaryReportLogLikelihoodTerm_reverse_false
      Real.sigmoid score second first (Ne.symm hsame)]
    simp [hsame, PairwiseCountDataset.randomUtilityWinProbability]

/--
The population logistic fit objective with diagonal displays removed.  This is
the exact population counterpart of the finite count likelihood, whose
dataset has zero diagonal by construction.
-/
noncomputable def theorem12OneComparisonOffDiagonalFitObjective
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (sampling : PMF Alternative) (preference : PairwisePreference PUnit Alternative)
    (score : PairwiseCountDataset.ScoreVector Alternative) : ℝ :=
  pmfPairExp sampling sampling (fun first second =>
    if first = second then 0 else
      preference.prob PUnit.unit first second *
        Real.log (Real.sigmoid (score first - score second)))

/--
Each literal report contributes one oriented win, while the off-diagonal
population objective counts both ordered orientations.  Their expectations
therefore differ by the exact constant factor two.
-/
theorem theorem12OneComparisonExpectedRawLogLikelihood_eq_two_offDiagonalFitObjective
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (sampling : PMF Alternative) (preference : PairwisePreference PUnit Alternative)
    (score : PairwiseCountDataset.ScoreVector Alternative) :
    theorem12OneComparisonExpectedRawLogLikelihood sampling preference score =
      2 * theorem12OneComparisonOffDiagonalFitObjective sampling preference score := by
  rw [theorem12OneComparisonExpectedRawLogLikelihood_eq]
  let term : Alternative → Alternative → ℝ := fun first second =>
    if first = second then 0 else
      preference.prob PUnit.unit first second *
        Real.log (Real.sigmoid (score first - score second))
  have hterm : ∀ first second,
      (if first = second then 0 else
          preference.prob PUnit.unit first second *
              Real.log (Real.sigmoid (score first - score second)) +
            (1 - preference.prob PUnit.unit first second) *
              Real.log (Real.sigmoid (score second - score first))) =
        term first second + term second first := by
    intro first second
    by_cases hsame : first = second
    · subst second
      simp [term]
    · rw [if_neg hsame]
      have hcomplement := preference.complementary PUnit.unit first second
      dsimp [term]
      rw [if_neg hsame, if_neg (Ne.symm hsame)]
      have hreverse : 1 - preference.prob PUnit.unit first second =
          preference.prob PUnit.unit second first := by
        linarith
      rw [hreverse]
  change pmfPairExp sampling sampling _ = 2 *
    pmfPairExp sampling sampling term
  rw [show (fun first second =>
      if first = second then 0 else
        preference.prob PUnit.unit first second *
            Real.log (Real.sigmoid (score first - score second)) +
          (1 - preference.prob PUnit.unit first second) *
            Real.log (Real.sigmoid (score second - score first))) =
      fun first second => term first second + term second first by
        funext first second
        exact hterm first second]
  rw [pmfPairExp_add, pmfPairExp_swap sampling term]
  ring

/--
The diagonal part of the full population Bradley--Terry objective.  It is a
constant in the candidate score because every diagonal score difference is
zero; the finite count likelihood correctly omits this constant.
-/
noncomputable def theorem12OneComparisonDiagonalFitConstant
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (sampling : PMF Alternative) (preference : PairwisePreference PUnit Alternative) : ℝ :=
  pmfPairExp sampling sampling (fun first second =>
    if first = second then
      preference.prob PUnit.unit first second * Real.log (Real.sigmoid 0)
    else 0)

/--
Deleting diagonal displays from the population objective changes it only by
the score-independent diagonal constant above.  This is the exact bridge from
the literal finite count likelihood to the paper's full population fit
objective.
-/
theorem bradleyTerryFitObjective_eq_offDiagonalFitObjective_add_diagonalConstant
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (sampling : PMF Alternative) (preference : PairwisePreference PUnit Alternative)
    (score : PairwiseCountDataset.ScoreVector Alternative) :
    bradleyTerryFitObjective preference sampling score =
      theorem12OneComparisonOffDiagonalFitObjective sampling preference score +
        theorem12OneComparisonDiagonalFitConstant sampling preference := by
  unfold bradleyTerryFitObjective theorem12OneComparisonOffDiagonalFitObjective
    theorem12OneComparisonDiagonalFitConstant
  rw [← pmfPairExp_add]
  unfold pmfPairExp
  apply pmfExp_congr
  intro first
  apply pmfExp_congr
  intro second
  by_cases hsame : first = second
  · subst second
    simp
  · simp [hsame]

/--
The literal off-diagonal population likelihood and the usual full
Bradley--Terry population likelihood have exactly the same global maximizers.
-/
theorem theorem12_offDiagonalFit_globalMax_iff_bradleyTerryFit_globalMax
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (sampling : PMF Alternative) (preference : PairwisePreference PUnit Alternative)
    (score : PairwiseCountDataset.ScoreVector Alternative) :
    (∀ candidate,
      theorem12OneComparisonOffDiagonalFitObjective sampling preference candidate ≤
        theorem12OneComparisonOffDiagonalFitObjective sampling preference score) ↔
      (∀ candidate,
        bradleyTerryFitObjective preference sampling candidate ≤
          bradleyTerryFitObjective preference sampling score) := by
  constructor
  · intro h candidate
    rw [bradleyTerryFitObjective_eq_offDiagonalFitObjective_add_diagonalConstant,
      bradleyTerryFitObjective_eq_offDiagonalFitObjective_add_diagonalConstant]
    simpa [add_comm] using
      add_le_add_right (h candidate)
        (theorem12OneComparisonDiagonalFitConstant sampling preference)
  · intro h candidate
    have hcandidate := h candidate
    rw [bradleyTerryFitObjective_eq_offDiagonalFitObjective_add_diagonalConstant,
      bradleyTerryFitObjective_eq_offDiagonalFitObjective_add_diagonalConstant] at hcandidate
    exact le_of_add_le_add_right hcandidate

/-- Comparison incidences assigned to an alternative in one ordered report. -/
def theorem12OneComparisonIncidences
    {Alternative : Type*} [DecidableEq Alternative]
    (alternative : Alternative) : ((Alternative × Alternative) × Bool) → ℝ
  | ((first, second), _) =>
      (if first = alternative then 1 else 0) + if second = alternative then 1 else 0

/-- Borda wins assigned to an alternative in one ordered binary comparison report. -/
def theorem12OneComparisonWins
    {Alternative : Type*} [DecidableEq Alternative]
    (alternative : Alternative) : ((Alternative × Alternative) × Bool) → ℝ
  | ((first, second), outcome) =>
      (if first = alternative ∧ outcome then 1 else 0) +
        if second = alternative ∧ ¬ outcome then 1 else 0

/-- One source report has nonnegative Borda wins. -/
theorem theorem12OneComparisonWins_nonneg
    {Alternative : Type*} [DecidableEq Alternative]
    (alternative : Alternative) (report : (Alternative × Alternative) × Bool) :
    0 ≤ theorem12OneComparisonWins alternative report := by
  rcases report with ⟨⟨first, second⟩, outcome⟩
  by_cases hfirst : first = alternative <;> by_cases hsecond : second = alternative <;>
    cases outcome <;> simp [theorem12OneComparisonWins, hfirst, hsecond]

/-- A single Borda win count never exceeds its associated comparison incidences. -/
theorem theorem12OneComparisonWins_le_incidences
    {Alternative : Type*} [DecidableEq Alternative]
    (alternative : Alternative) (report : (Alternative × Alternative) × Bool) :
    theorem12OneComparisonWins alternative report ≤ theorem12OneComparisonIncidences alternative report := by
  rcases report with ⟨⟨first, second⟩, outcome⟩
  by_cases hfirst : first = alternative <;> by_cases hsecond : second = alternative <;>
    cases outcome <;> simp [theorem12OneComparisonWins, theorem12OneComparisonIncidences,
      hfirst, hsecond]

/-- Finite PMF expectation of an equality indicator is its atom mass. -/
theorem theorem12_pmfExp_eq_indicator
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (sampling : PMF Alternative) (alternative : Alternative) :
    pmfExp sampling (fun drawn => if drawn = alternative then (1 : ℝ) else 0) =
      (sampling alternative).toReal := by
  classical
  simp [pmfExp]

/-- Multiplying by an equality indicator restricts a finite expectation to one atom. -/
theorem theorem12_pmfExp_eq_indicator_mul
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (sampling : PMF Alternative) (alternative : Alternative) (value : Alternative → ℝ) :
    pmfExp sampling (fun drawn =>
      (if drawn = alternative then (1 : ℝ) else 0) * value drawn) =
      (sampling alternative).toReal * value alternative := by
  classical
  simp [pmfExp]

/-- The expected number of comparison incidences is twice the sampling mass. -/
theorem theorem12OneComparisonIncidences_pmfExp
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (sampling : PMF Alternative) (preference : PairwisePreference PUnit Alternative)
    (alternative : Alternative) :
    pmfExp (theorem12OneComparisonReportLaw sampling preference)
      (theorem12OneComparisonIncidences alternative) = 2 * (sampling alternative).toReal := by
  calc
    pmfExp (theorem12OneComparisonReportLaw sampling preference)
        (theorem12OneComparisonIncidences alternative) =
      pmfExp sampling (fun first => pmfExp sampling (fun second =>
        pmfExp (theorem12BernoulliReport
          (preference.prob PUnit.unit first second)
          (preference.nonneg PUnit.unit first second)
          (preference.le_one PUnit.unit first second))
          (fun outcome => theorem12OneComparisonIncidences alternative ((first, second), outcome)))) := by
        unfold theorem12OneComparisonReportLaw
        rw [pmfExp_bind]
        apply pmfExp_congr
        intro first
        rw [pmfExp_bind]
        apply pmfExp_congr
        intro second
        rw [pmfExp_map]
    _ = pmfExp sampling (fun first => pmfExp sampling (fun second =>
        (if first = alternative then (1 : ℝ) else 0) +
          if second = alternative then 1 else 0)) := by
        apply pmfExp_congr
        intro first
        apply pmfExp_congr
        intro second
        have hconst :
            (fun outcome : Bool => theorem12OneComparisonIncidences alternative
              ((first, second), outcome)) =
              fun _ => (if first = alternative then (1 : ℝ) else 0) +
                if second = alternative then 1 else 0 := by
              funext outcome
              rfl
        rw [hconst, pmfExp_const]
    _ = pmfExp sampling (fun first =>
        (if first = alternative then (1 : ℝ) else 0) + (sampling alternative).toReal) := by
        apply pmfExp_congr
        intro first
        rw [pmfExp_add, pmfExp_const, theorem12_pmfExp_eq_indicator]
    _ = 2 * (sampling alternative).toReal := by
        rw [pmfExp_add, theorem12_pmfExp_eq_indicator, pmfExp_const]
        ring

/-- The expected Borda wins in one report equal two sampling masses times the Borda score. -/
theorem theorem12OneComparisonWins_pmfExp
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (sampling : PMF Alternative) (preference : PairwisePreference PUnit Alternative)
    (alternative : Alternative) :
    pmfExp (theorem12OneComparisonReportLaw sampling preference)
      (theorem12OneComparisonWins alternative) =
        2 * (sampling alternative).toReal * pairwiseBordaScore sampling preference alternative := by
  let probability : Alternative → Alternative → ℝ :=
    fun first second => preference.prob PUnit.unit first second
  have hinner : ∀ first second,
      pmfExp (theorem12BernoulliReport (probability first second)
          (preference.nonneg PUnit.unit first second)
          (preference.le_one PUnit.unit first second))
        (fun outcome => theorem12OneComparisonWins alternative ((first, second), outcome)) =
        (if first = alternative then probability first second else 0) +
          if second = alternative then 1 - probability first second else 0 := by
    intro first second
    by_cases hfirst : first = alternative <;> by_cases hsecond : second = alternative
    · subst first
      subst second
      rw [show (fun outcome => theorem12OneComparisonWins alternative ((alternative, alternative), outcome)) =
          fun outcome => (if outcome then (1 : ℝ) else 0) + if outcome then 0 else 1 by
            funext outcome
            cases outcome <;> simp [theorem12OneComparisonWins]]
      rw [pmfExp_add, theorem12_pmfExp_bernoulli_true,
        theorem12_pmfExp_bernoulli_false]
      simp
    · subst first
      have hfun :
          (fun outcome => theorem12OneComparisonWins alternative ((alternative, second), outcome)) =
            fun outcome => if outcome then (1 : ℝ) else 0 := by
          funext outcome
          simp [theorem12OneComparisonWins, hsecond]
      rw [hfun, theorem12_pmfExp_bernoulli_true]
      simp [hsecond]
    · subst second
      have hfun :
          (fun outcome => theorem12OneComparisonWins alternative ((first, alternative), outcome)) =
            fun outcome => if outcome then (0 : ℝ) else 1 := by
          funext outcome
          cases outcome <;> simp [theorem12OneComparisonWins, hfirst]
      rw [hfun, theorem12_pmfExp_bernoulli_false]
      simp [hfirst]
    · have hfun :
          (fun outcome => theorem12OneComparisonWins alternative ((first, second), outcome)) =
            fun _ => 0 := by
          funext outcome
          simp [theorem12OneComparisonWins, hfirst, hsecond]
      rw [hfun, pmfExp_const]
      simp [hfirst, hsecond]
  calc
    pmfExp (theorem12OneComparisonReportLaw sampling preference)
        (theorem12OneComparisonWins alternative) =
      pmfExp sampling (fun first => pmfExp sampling (fun second =>
        pmfExp (theorem12BernoulliReport (probability first second)
          (preference.nonneg PUnit.unit first second)
          (preference.le_one PUnit.unit first second))
          (fun outcome => theorem12OneComparisonWins alternative ((first, second), outcome)))) := by
        unfold theorem12OneComparisonReportLaw
        rw [pmfExp_bind]
        apply pmfExp_congr
        intro first
        rw [pmfExp_bind]
        apply pmfExp_congr
        intro second
        rw [pmfExp_map]
    _ = pmfExp sampling (fun first => pmfExp sampling (fun second =>
        (if first = alternative then probability first second else 0) +
          if second = alternative then 1 - probability first second else 0)) := by
        apply pmfExp_congr
        intro first
        apply pmfExp_congr
        intro second
        exact hinner first second
    _ = pmfExp sampling (fun first =>
        (if first = alternative then (1 : ℝ) else 0) * pairwiseBordaScore sampling preference first +
          (sampling alternative).toReal * probability alternative first) := by
        apply pmfExp_congr
        intro first
        rw [pmfExp_add]
        congr 1
        · by_cases hfirst : first = alternative
          · subst first
            simp [pairwiseBordaScore, probability]
          · simp [hfirst]
        · rw [show
            pmfExp sampling (fun second =>
              if second = alternative then 1 - probability first second else 0) =
              (sampling alternative).toReal * (1 - probability first alternative) by
              simpa only [ite_mul, one_mul, zero_mul] using theorem12_pmfExp_eq_indicator_mul sampling alternative
                (fun second => 1 - probability first second)]
          have hcomplement := preference.complementary PUnit.unit first alternative
          change (sampling alternative).toReal * (1 - probability first alternative) = _
          rw [show 1 - probability first alternative = probability alternative first by
            dsimp [probability]
            linarith]
    _ = 2 * (sampling alternative).toReal * pairwiseBordaScore sampling preference alternative := by
        rw [pmfExp_add, theorem12_pmfExp_eq_indicator_mul, pmfExp_const_mul]
        change (sampling alternative).toReal * pairwiseBordaScore sampling preference alternative +
            (sampling alternative).toReal *
              pmfExp sampling (fun first => preference.prob PUnit.unit alternative first) = _
        rw [show pmfExp sampling (fun first => preference.prob PUnit.unit alternative first) =
            pairwiseBordaScore sampling preference alternative by rfl]
        ring

/--
The source's one-comparison-per-user Borda experiment selects any strict
population Borda winner with probability tending to one, provided every
alternative is sampled with positive probability.
-/
theorem theorem12_oneComparison_iidBordaFailure_tendsto_zero_of_strictBordaWinner
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (sampling : PMF Alternative) (preference : PairwisePreference PUnit Alternative)
    (winner : Alternative) (hsampling_pos : ∀ alternative, 0 < (sampling alternative).toReal)
    (hstrict : ∀ ordinary, ordinary ≠ winner →
      pairwiseBordaScore sampling preference ordinary < pairwiseBordaScore sampling preference winner) :
    Filter.Tendsto
      (fun horizon =>
        pmfProb (theorem12IidBordaReportBatchLaw
          (theorem12OneComparisonReportLaw sampling preference) horizon)
          (fun sample => theorem12IidEmpiricalBordaFailure theorem12OneComparisonWins
            theorem12OneComparisonIncidences winner sample))
      Filter.atTop (𝓝 0) := by
  apply theorem12_iidEmpiricalBordaFailure_tendsto_zero_of_calibrated_strict_winner
    (theorem12OneComparisonReportLaw sampling preference)
    theorem12OneComparisonWins theorem12OneComparisonIncidences
    (pairwiseBordaScore sampling preference) winner
  · intro alternative report
    exact theorem12OneComparisonWins_nonneg alternative report
  · intro alternative report
    exact theorem12OneComparisonWins_le_incidences alternative report
  · intro alternative
    exact pmfExp_nonneg_of_forall_nonneg sampling _
      (fun opponent => preference.nonneg PUnit.unit alternative opponent)
  · intro alternative
    rw [theorem12OneComparisonWins_pmfExp, theorem12OneComparisonIncidences_pmfExp]
    ring
  · intro alternative
    rw [theorem12OneComparisonIncidences_pmfExp]
    exact mul_pos (by norm_num) (hsampling_pos alternative)
  · exact hstrict

/--
Finite-sample completion of the three-candidate Appendix-E.2 construction.
For every strict sub-bound below Eq. (10), its literal unit-interval instance
has a low-welfare `c` that becomes the unique normalized-count Borda winner
with probability tending to one under the source's one-comparison-per-user
experiment.
-/
theorem theorem12_threeAlternative_iidBorda_lower_bound
    {beta gamma q : ℝ} (hbeta : 0 < beta) (hgamma : 0 < gamma) (hgamma_lt_one : gamma < 1)
    (hq : q < theorem12Eq10Coefficient beta gamma) :
    ∃ (epsilon : ℝ) (hepsilon : 0 < epsilon) (hepsilon_lt_half : epsilon < (1 : ℝ) / 2)
      (sampling : PMF (Fin 3)),
      epsilon ^ 2 < 1 - epsilon ∧
        UnitIntervalUtilityProfile (theorem12Utility epsilon (epsilon ^ 2) gamma) ∧
        q <
          populationAverageUtility
            (theorem12Population beta epsilon gamma hbeta hepsilon (by linarith)
              hgamma hgamma_lt_one)
            (theorem12Utility epsilon (epsilon ^ 2) gamma) (0 : Fin 3) /
          populationAverageUtility
            (theorem12Population beta epsilon gamma hbeta hepsilon (by linarith)
              hgamma hgamma_lt_one)
            (theorem12Utility epsilon (epsilon ^ 2) gamma) (2 : Fin 3) ∧
        Filter.Tendsto
          (fun horizon =>
            pmfProb (theorem12IidBordaReportBatchLaw
              (theorem12OneComparisonReportLaw sampling
                (populationBradleyTerryPreference
                  (theorem12Population beta epsilon gamma hbeta hepsilon (by linarith)
                    hgamma hgamma_lt_one)
                  (theorem12Utility epsilon (epsilon ^ 2) gamma) beta)) horizon)
              (fun sample => theorem12IidEmpiricalBordaFailure theorem12OneComparisonWins
                theorem12OneComparisonIncidences (2 : Fin 3) sample))
          Filter.atTop (𝓝 0) := by
  obtain ⟨epsilon, hepsilon, hepsilon_lt_half, sampling, hepsilonZero_lt, hunit, hsupport,
    hscoreA, hscoreB, hratio⟩ :=
    theorem12_threeAlternative_populationBorda_lower_bound hbeta hgamma hgamma_lt_one hq
  have hepsilon_lt_one : epsilon < 1 := by linarith
  let population := theorem12Population beta epsilon gamma hbeta hepsilon hepsilon_lt_one
    hgamma hgamma_lt_one
  let utility := theorem12Utility epsilon (epsilon ^ 2) gamma
  let preference := populationBradleyTerryPreference population utility beta
  refine ⟨epsilon, hepsilon, hepsilon_lt_half, sampling, hepsilonZero_lt, hunit, ?_, ?_⟩
  · simpa [population, utility] using hratio
  · apply theorem12_oneComparison_iidBordaFailure_tendsto_zero_of_strictBordaWinner
      sampling preference (2 : Fin 3) hsupport
    intro ordinary hordinary
    fin_cases ordinary
    · simpa [population, utility, preference] using hscoreA
    · simpa [population, utility, preference] using hscoreB
    · exact (hordinary rfl).elim

/--
Finite-sample completion of Appendix-E.2's candidate-splitting argument.  The
source construction supplies, for every `m ≥ 3`, an `m`-alternative
unit-interval instance whose low-welfare `c` becomes the unique
normalized-count Borda winner with probability tending to one.
-/
theorem theorem12_all_m_iidBorda_lower_bound
    {beta gamma q : ℝ} (hbeta : 0 < beta) (hgamma : 0 < gamma) (hgamma_lt_one : gamma < 1)
    (hq : q < theorem12Eq10Coefficient beta gamma) (m : ℕ) (hm : 3 ≤ m) :
    ∃ (epsilon : ℝ) (hepsilon : 0 < epsilon) (hepsilon_lt_half : epsilon < (1 : ℝ) / 2)
      (sampling : PMF (Fin 3 ⊕ Fin (m - 3))),
      epsilon ^ 2 < 1 - epsilon ∧ Fintype.card (Fin 3 ⊕ Fin (m - 3)) = m ∧
        let collapse := theorem12CloneCollapse (1 : Fin 3) (m - 3)
        let splitUtility := theorem12SplitUtility (theorem12Utility epsilon (epsilon ^ 2) gamma)
          collapse
        let population := theorem12Population beta epsilon gamma hbeta hepsilon (by linarith)
          hgamma hgamma_lt_one
        let preference := populationBradleyTerryPreference population splitUtility beta
        UnitIntervalUtilityProfile splitUtility ∧
          PMFFullSupport sampling ∧
          q <
            populationAverageUtility population splitUtility (Sum.inl (0 : Fin 3)) /
              populationAverageUtility population splitUtility (Sum.inl (2 : Fin 3)) ∧
          Filter.Tendsto
            (fun horizon =>
              pmfProb (theorem12IidBordaReportBatchLaw
                (theorem12OneComparisonReportLaw sampling preference) horizon)
                (fun sample => theorem12IidEmpiricalBordaFailure theorem12OneComparisonWins
                  theorem12OneComparisonIncidences (Sum.inl (2 : Fin 3)) sample))
            Filter.atTop (𝓝 0) := by
  obtain ⟨epsilon, hepsilon, hepsilon_lt_half, sampling, hepsilonZero_lt, hcard, hunit,
    hsupport, hwinning, hratio⟩ :=
    theorem12_populationBorda_lower_bound_all_m hbeta hgamma hgamma_lt_one hq m hm
  have hepsilon_lt_one : epsilon < 1 := by linarith
  let collapse := theorem12CloneCollapse (1 : Fin 3) (m - 3)
  let splitUtility := theorem12SplitUtility (theorem12Utility epsilon (epsilon ^ 2) gamma) collapse
  let population := theorem12Population beta epsilon gamma hbeta hepsilon hepsilon_lt_one
    hgamma hgamma_lt_one
  let preference := populationBradleyTerryPreference population splitUtility beta
  refine ⟨epsilon, hepsilon, hepsilon_lt_half, sampling, hepsilonZero_lt, hcard, ?_⟩
  dsimp only
  refine ⟨hunit, hsupport, ?_, ?_⟩
  · simpa [collapse, splitUtility, population] using hratio
  · apply theorem12_oneComparison_iidBordaFailure_tendsto_zero_of_strictBordaWinner
      sampling preference (Sum.inl (2 : Fin 3)) hsupport
    simpa [collapse, splitUtility, population, preference] using hwinning

end GolzHaghtalabYang2025Distortion
