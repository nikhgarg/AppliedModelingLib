import GolzHaghtalabYang2025Distortion.Theorem3D2Iid

/-!
# Source population margins for the multi-comparison branch of Theorem 3

This module begins the source-to-report bridge for Appendix E.3.  A comparison
draw first samples the paper's two-type population and then applies the
Bradley--Terry choice law.  The elementary result below records the strict
expected signed margin of every ordinary alternative over the hidden special
alternative when `ξ > 1`.
-/

namespace GolzHaghtalabYang2025Distortion

open AppliedModelingLib
open AppliedModelingLib.Alignment.Welfare

/-- The population-level Bradley--Terry outcome law for one labelled pair. -/
noncomputable def theorem3PopulationComparisonOutcomeLaw
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (beta epsilon xi : ℝ) (hbeta : 0 < beta) (hepsilon : 0 < epsilon)
    (special : Alternative) (pair : Alternative × Alternative) : PMF Bool :=
  let preference := populationBradleyTerryPreference
    (theorem3TwoTypePopulation beta epsilon hbeta hepsilon)
    (theorem3ManyAlternativeUtility epsilon xi special) beta
  PMF.bernoulli
    ⟨preference.prob PUnit.unit.{1} pair.1 pair.2,
      preference.nonneg PUnit.unit.{1} pair.1 pair.2⟩
    (preference.le_one PUnit.unit.{1} pair.1 pair.2)

/--
Signed contribution of a labelled comparison to the ordinary-versus-special
Condorcet margin.  A positive value means that `ordinary` beats `special`.
-/
def theorem3OrdinarySpecialComparisonMargin
    {Alternative : Type*} [DecidableEq Alternative]
    (special ordinary : Alternative) : ((Alternative × Alternative) × Bool) → ℝ
  | ((first, second), outcome) =>
      if first = ordinary ∧ second = special then
        if outcome then 1 else -1
      else if first = special ∧ second = ordinary then
        if outcome then -1 else 1
      else 0

/-- A Bernoulli outcome with success probability `p` has signed mean `2p - 1`. -/
theorem theorem3_bernoulli_signedMean
    (p : NNReal) (hp : p ≤ 1) :
    pmfExp (PMF.bernoulli p hp) (fun outcome : Bool => if outcome then (1 : ℝ) else -1) =
      2 * p - 1 := by
  simp [pmfExp, PMF.bernoulli_apply]
  rw [NNReal.coe_sub hp]
  norm_num
  ring

/--
For the directed pair `(ordinary, special)`, the source's `ξ > 1` perturbation
has strictly positive expected signed margin.
-/
theorem theorem3_ordinarySpecial_margin_pos_at_forward_pair
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    {beta epsilon xi : ℝ} (hbeta : 0 < beta) (hepsilon : 0 < epsilon) (hxi : 1 < xi)
    (special ordinary : Alternative) (hordinary : ordinary ≠ special) :
    0 < pmfExp
      (theorem3PopulationComparisonOutcomeLaw beta epsilon xi hbeta hepsilon special
        (ordinary, special))
      (fun outcome => theorem3OrdinarySpecialComparisonMargin special ordinary
        ((ordinary, special), outcome)) := by
  let preference := populationBradleyTerryPreference
    (theorem3TwoTypePopulation beta epsilon hbeta hepsilon)
    (theorem3ManyAlternativeUtility epsilon xi special) beta
  have hwin : (1 : ℝ) / 2 < preference.prob PUnit.unit.{1} ordinary special := by
    simpa [preference] using
      theorem3ManyAlternative_ordinary_vs_special_gt_half_of_one_lt_xi
        hbeta hepsilon hxi special ordinary hordinary
  unfold theorem3PopulationComparisonOutcomeLaw
  dsimp
  simp only [theorem3OrdinarySpecialComparisonMargin, if_pos, and_self]
  rw [theorem3_bernoulli_signedMean]
  change 0 < 2 * preference.prob PUnit.unit ordinary special - 1
  linarith

/-- Every labelled pair has a nonnegative expected contribution to the source margin. -/
theorem theorem3_ordinarySpecial_margin_nonneg_at_pair
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    {beta epsilon xi : ℝ} (hbeta : 0 < beta) (hepsilon : 0 < epsilon) (hxi : 1 < xi)
    (special ordinary : Alternative) (hordinary : ordinary ≠ special)
    (pair : Alternative × Alternative) :
    0 ≤ pmfExp
      (theorem3PopulationComparisonOutcomeLaw beta epsilon xi hbeta hepsilon special pair)
      (fun outcome => theorem3OrdinarySpecialComparisonMargin special ordinary (pair, outcome)) := by
  by_cases hforward : pair = (ordinary, special)
  · subst pair
    exact (theorem3_ordinarySpecial_margin_pos_at_forward_pair
      hbeta hepsilon hxi special ordinary hordinary).le
  by_cases hreverse : pair = (special, ordinary)
  · subst pair
    let preference := populationBradleyTerryPreference
      (theorem3TwoTypePopulation beta epsilon hbeta hepsilon)
      (theorem3ManyAlternativeUtility epsilon xi special) beta
    have hlose : preference.prob PUnit.unit.{1} special ordinary < (1 : ℝ) / 2 := by
      simpa [preference] using
        theorem3ManyAlternative_special_vs_ordinary_lt_half_of_one_lt_xi
          hbeta hepsilon hxi special ordinary hordinary
    unfold theorem3PopulationComparisonOutcomeLaw
    dsimp
    have hnegated :
        (fun outcome : Bool => theorem3OrdinarySpecialComparisonMargin special ordinary
          ((special, ordinary), outcome)) =
          fun outcome => - (if outcome then (1 : ℝ) else -1) := by
      funext outcome
      cases outcome <;> norm_num [theorem3OrdinarySpecialComparisonMargin, hordinary]
    rw [hnegated, pmfExp_neg, theorem3_bernoulli_signedMean]
    change 0 ≤ -(2 * preference.prob PUnit.unit special ordinary - 1)
    linarith
  have hne_forward : ¬ (pair.1 = ordinary ∧ pair.2 = special) := by
    intro h
    apply hforward
    exact Prod.ext h.1 h.2
  have hne_reverse : ¬ (pair.1 = special ∧ pair.2 = ordinary) := by
    intro h
    apply hreverse
    exact Prod.ext h.1 h.2
  unfold theorem3PopulationComparisonOutcomeLaw
  dsimp
  simp [theorem3OrdinarySpecialComparisonMargin, hne_forward, hne_reverse]

/--
One random labelled comparison from the source population, retaining both the
pair label and the Bradley--Terry outcome.
-/
noncomputable def theorem3ManyAlternativeOneComparisonLawXi
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (pairSampling : PMF (Alternative × Alternative))
    (beta epsilon xi : ℝ) (hbeta : 0 < beta) (hepsilon : 0 < epsilon)
    (special : Alternative) : PMF ((Alternative × Alternative) × Bool) :=
  pairSampling.bind fun pair =>
    (theorem3PopulationComparisonOutcomeLaw beta epsilon xi hbeta hepsilon special pair).map
      (fun outcome => (pair, outcome))

/--
When the directed pair `(ordinary, special)` has positive sampling mass, one
source comparison has a strictly positive ordinary-versus-special expected
margin.  The reverse orientation only contributes additional nonnegative
margin, so no symmetry assumption on pair sampling is needed here.
-/
theorem theorem3_oneComparison_expected_ordinarySpecial_margin_pos
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    {beta epsilon xi : ℝ} (hbeta : 0 < beta) (hepsilon : 0 < epsilon) (hxi : 1 < xi)
    (pairSampling : PMF (Alternative × Alternative))
    (special ordinary : Alternative) (hordinary : ordinary ≠ special)
    (hpair : 0 < (pairSampling (ordinary, special)).toReal) :
    0 < pmfExp
      (theorem3ManyAlternativeOneComparisonLawXi pairSampling beta epsilon xi hbeta hepsilon
        special)
      (theorem3OrdinarySpecialComparisonMargin special ordinary) := by
  unfold theorem3ManyAlternativeOneComparisonLawXi
  rw [pmfExp_bind]
  apply cutoff_lt_pmfExp_of_all_ge_exists_gt _ _ 0
  · intro pair
    rw [pmfExp_map]
    exact theorem3_ordinarySpecial_margin_nonneg_at_pair
      hbeta hepsilon hxi special ordinary hordinary pair
  · refine ⟨(ordinary, special), hpair, ?_⟩
    rw [pmfExp_map]
    exact theorem3_ordinarySpecial_margin_pos_at_forward_pair
      hbeta hepsilon hxi special ordinary hordinary

/--
A finite report in the correlated-sampling extension of Appendix E.3.  Its
comparisons are deliberately allowed to be perfectly correlated; the report
contains `d` copies of one labelled Bradley--Terry comparison.
-/
noncomputable def theorem3RepeatedComparisonReportLaw
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (pairSampling : PMF (Alternative × Alternative))
    (beta epsilon xi : ℝ) (hbeta : 0 < beta) (hepsilon : 0 < epsilon)
    (special : Alternative) (d : ℕ) : PMF (Fin d → ((Alternative × Alternative) × Bool)) :=
  (theorem3ManyAlternativeOneComparisonLawXi pairSampling beta epsilon xi hbeta hepsilon
    special).map (fun comparison _ => comparison)

/-- The aggregate ordinary-versus-special margin in one finite user report. -/
def theorem3ReportedOrdinarySpecialMargin
    {Alternative : Type*} [DecidableEq Alternative] {d : ℕ}
    (special ordinary : Alternative) (report : Fin d → ((Alternative × Alternative) × Bool)) : ℝ :=
  ∑ comparisonIndex : Fin d,
    theorem3OrdinarySpecialComparisonMargin special ordinary (report comparisonIndex)

/--
The correlated report construction retains a strictly positive aggregate
ordinary-versus-special mean whenever at least one comparison is reported.
-/
theorem theorem3_repeatedReport_expected_ordinarySpecial_margin_pos
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    {beta epsilon xi : ℝ} (hbeta : 0 < beta) (hepsilon : 0 < epsilon) (hxi : 1 < xi)
    (pairSampling : PMF (Alternative × Alternative))
    (special ordinary : Alternative) (hordinary : ordinary ≠ special)
    (hpair : 0 < (pairSampling (ordinary, special)).toReal)
    (d : ℕ) (hd : 0 < d) :
    0 < pmfExp
      (theorem3RepeatedComparisonReportLaw pairSampling beta epsilon xi hbeta hepsilon special d)
      (theorem3ReportedOrdinarySpecialMargin special ordinary) := by
  let oneLaw := theorem3ManyAlternativeOneComparisonLawXi pairSampling beta epsilon xi hbeta
    hepsilon special
  let oneMargin := theorem3OrdinarySpecialComparisonMargin special ordinary
  have honeMean : 0 < pmfExp oneLaw oneMargin := by
    exact theorem3_oneComparison_expected_ordinarySpecial_margin_pos
      hbeta hepsilon hxi pairSampling special ordinary hordinary hpair
  calc
    pmfExp
        (theorem3RepeatedComparisonReportLaw pairSampling beta epsilon xi hbeta hepsilon special d)
        (theorem3ReportedOrdinarySpecialMargin special ordinary)
      = pmfExp oneLaw (fun comparison => ∑ _ : Fin d, oneMargin comparison) := by
          rw [theorem3RepeatedComparisonReportLaw, pmfExp_map]
          rfl
    _ = pmfExp oneLaw (fun comparison => (d : ℝ) * oneMargin comparison) := by
          apply pmfExp_congr
          intro comparison
          simp [Finset.sum_const, nsmul_eq_mul]
    _ = (d : ℝ) * pmfExp oneLaw oneMargin := by
          exact pmfExp_const_mul oneLaw (d : ℝ) oneMargin
    _ > 0 := by
          exact mul_pos (by exact_mod_cast hd) honeMean

/--
The expected aggregate margin is positive for any finite report law whose
comparison coordinates have the source one-comparison marginal.  This is the
precise bridge that permits arbitrary correlation within a user's report.
-/
theorem theorem3_report_expected_ordinarySpecial_margin_pos_of_coordinate_law
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    {beta epsilon xi : ℝ} (hbeta : 0 < beta) (hepsilon : 0 < epsilon) (hxi : 1 < xi)
    (pairSampling : PMF (Alternative × Alternative))
    (special ordinary : Alternative) (hordinary : ordinary ≠ special)
    (hpair : 0 < (pairSampling (ordinary, special)).toReal)
    (d : ℕ) (hd : 0 < d)
    (reportLaw : PMF (Fin d → ((Alternative × Alternative) × Bool)))
    (hcoordinate : ∀ comparisonIndex : Fin d,
      reportLaw.map (fun report => report comparisonIndex) =
        theorem3ManyAlternativeOneComparisonLawXi pairSampling beta epsilon xi hbeta hepsilon
          special) :
    0 < pmfExp reportLaw (theorem3ReportedOrdinarySpecialMargin special ordinary) := by
  let oneLaw := theorem3ManyAlternativeOneComparisonLawXi pairSampling beta epsilon xi hbeta
    hepsilon special
  let oneMargin := theorem3OrdinarySpecialComparisonMargin special ordinary
  have honeMean : 0 < pmfExp oneLaw oneMargin := by
    exact theorem3_oneComparison_expected_ordinarySpecial_margin_pos
      hbeta hepsilon hxi pairSampling special ordinary hordinary hpair
  change 0 < pmfExp reportLaw (fun report =>
    ∑ comparisonIndex : Fin d, oneMargin (report comparisonIndex))
  rw [pmfExp_univ_sum]
  have hcoordinateMean : ∀ comparisonIndex : Fin d,
      pmfExp reportLaw (fun report => oneMargin (report comparisonIndex)) =
        pmfExp oneLaw oneMargin := by
    intro comparisonIndex
    calc
      pmfExp reportLaw (fun report => oneMargin (report comparisonIndex)) =
          pmfExp (reportLaw.map (fun report => report comparisonIndex)) oneMargin := by
            exact (pmfExp_map reportLaw (fun report => report comparisonIndex) oneMargin).symm
      _ = pmfExp oneLaw oneMargin := by
            rw [hcoordinate comparisonIndex]
  calc
    ∑ comparisonIndex : Fin d,
        pmfExp reportLaw (fun report => oneMargin (report comparisonIndex)) =
      ∑ _ : Fin d, pmfExp oneLaw oneMargin := by
        apply Finset.sum_congr rfl
        intro comparisonIndex _
        exact hcoordinateMean comparisonIndex
    _ = (d : ℝ) * pmfExp oneLaw oneMargin := by
        simp [Finset.sum_const, nsmul_eq_mul]
    _ > 0 := by
        exact mul_pos (by exact_mod_cast hd) honeMean

/--
Source-facing `d ≥ 2` endpoint for arbitrary within-user report dependence.
For each alternative-set size, the law of every comparison coordinate is the
two-type Bradley--Terry marginal from Appendix E.3; the joint law of the `d`
coordinates is otherwise unrestricted.  IID sampling occurs only across user
reports.  These source primitives imply the empirical Condorcet certificate
and hence the paper's asymptotic lower bound.
-/
theorem theorem3_d2_asymptotic_lower_bound_of_sourceReportMarginals
    {beta : ℝ} (hbeta : 0 < beta) (d : ℕ) (hd : 2 ≤ d)
    (pairSampling : ∀ n : ℕ, PMF (Fin (n + 3) × Fin (n + 3)))
    (hpair : ∀ n (ordinary : Fin (n + 3)), ordinary ≠ (0 : Fin (n + 3)) →
      0 < (pairSampling n (ordinary, 0)).toReal)
    (reportLaw : ∀ n : ℕ,
      PMF (Fin d → ((Fin (n + 3) × Fin (n + 3)) × Bool)))
    (hcoordinate : ∀ n (comparisonIndex : Fin d),
      (reportLaw n).map (fun report => report comparisonIndex) =
        theorem3ManyAlternativeOneComparisonLawXi (pairSampling n) beta
          (theorem3D2DiagonalEpsilon n) (theorem3D2DiagonalXi n) hbeta
          (theorem3D2DiagonalEpsilon_pos n) (0 : Fin (n + 3)))
    (rule : ∀ n horizon,
      (Fin horizon → (Fin d → ((Fin (n + 3) × Fin (n + 3)) × Bool))) →
        PMF (Fin (n + 3)))
    (hcriterion : ∀ n horizon,
      theorem3ProbabilisticCondorcetLoserCriterion (rule n horizon)
        (fun observation alternative =>
          theorem3IidEmpiricalStrictCondorcetLoser
            (fun ordinary => theorem3ReportedOrdinarySpecialMargin alternative ordinary)
            alternative observation))
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
  refine theorem3_d2_asymptotic_lower_bound_of_iid_positive_margins hbeta reportLaw
    (fun _n special ordinary => theorem3ReportedOrdinarySpecialMargin special ordinary)
    rule hcriterion ?_ delta hdelta
  intro n ordinary
  exact theorem3_report_expected_ordinarySpecial_margin_pos_of_coordinate_law
    hbeta (theorem3D2DiagonalEpsilon_pos n) (theorem3D2DiagonalXi_bounds n).1
    (pairSampling n) (0 : Fin (n + 3)) ordinary.1 ordinary.2
    (hpair n ordinary.1 ordinary.2) d (lt_of_lt_of_le (by norm_num) hd)
    (reportLaw n) (hcoordinate n)

/--
Concrete `d ≥ 2` source endpoint for the correlated-report extension described
in §5.  Each iid user report contains `d` perfectly correlated copies of a
single labelled comparison; this is permitted by the paper's generalized
within-user report model.  Positive mass on every ordinary-versus-special
pair yields the source's large-market distortion lower bound for every rule
satisfying the probabilistic Condorcet-loser criterion.
-/
theorem theorem3_d2_asymptotic_lower_bound_repeatedComparisonReports
    {beta : ℝ} (hbeta : 0 < beta) (d : ℕ) (hd : 2 ≤ d)
    (pairSampling : ∀ n : ℕ, PMF (Fin (n + 3) × Fin (n + 3)))
    (hpair : ∀ n (ordinary : Fin (n + 3)), ordinary ≠ (0 : Fin (n + 3)) →
      0 < (pairSampling n (ordinary, 0)).toReal)
    (rule : ∀ n horizon,
      (Fin horizon → (Fin d → ((Fin (n + 3) × Fin (n + 3)) × Bool))) →
        PMF (Fin (n + 3)))
    (hcriterion : ∀ n horizon,
      theorem3ProbabilisticCondorcetLoserCriterion (rule n horizon)
        (fun observation alternative =>
          theorem3IidEmpiricalStrictCondorcetLoser
            (fun ordinary => theorem3ReportedOrdinarySpecialMargin alternative ordinary)
            alternative observation))
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
              (theorem3IidUserReportBatchLaw
                (theorem3RepeatedComparisonReportLaw (pairSampling n) beta
                  (theorem3D2DiagonalEpsilon n) (theorem3D2DiagonalXi n) hbeta
                  (theorem3D2DiagonalEpsilon_pos n) (0 : Fin (n + 3)) d)
                horizon)
              (rule n horizon)) := by
  refine theorem3_d2_asymptotic_lower_bound_of_iid_positive_margins hbeta
    (fun n => theorem3RepeatedComparisonReportLaw (pairSampling n) beta
      (theorem3D2DiagonalEpsilon n) (theorem3D2DiagonalXi n) hbeta
      (theorem3D2DiagonalEpsilon_pos n) (0 : Fin (n + 3)) d)
    (fun _n special ordinary => theorem3ReportedOrdinarySpecialMargin special ordinary)
    rule hcriterion ?_ delta hdelta
  intro n ordinary
  exact theorem3_repeatedReport_expected_ordinarySpecial_margin_pos
    hbeta (theorem3D2DiagonalEpsilon_pos n) (theorem3D2DiagonalXi_bounds n).1
    (pairSampling n) (0 : Fin (n + 3)) ordinary.1 ordinary.2
    (hpair n ordinary.1 ordinary.2) d (lt_of_lt_of_le (by norm_num) hd)

end GolzHaghtalabYang2025Distortion
