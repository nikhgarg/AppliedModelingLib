import GHKR22BiasBounties.DistributionalPaperInterface

/-!
# Proof endpoints for the arbitrary-distribution interface

Each theorem below has exactly the type of its transparent source-facing
specification in `DistributionalPaperInterface.lean`.
-/

namespace GHKR22BiasBounties

/-- Checked arbitrary-population endpoint for Definition 1. -/
theorem definition1_measure_subgroups : definition1_measure_subgroupsSpec := by
  intro X Y _ _ law _ group _
  rfl

/-- Checked arbitrary-population endpoint for Definition 2. -/
theorem definition2_measure_modelLoss : definition2_measure_modelLossSpec := by
  intro X Y _ _ law _ loss _ model _ group _
  exact ⟨rfl, rfl⟩

/-- Checked arbitrary-population endpoint for the repaired Definition 3. -/
theorem definition3_measure_aeBayesOptimal :
    definition3_measure_aeBayesOptimalSpec := by
  intro X Y _ _ featureLaw _ labels _ loss _ current _
  rfl

/-- Checked arbitrary-population endpoint for Definition 5. -/
theorem definition5_measure_approxBayesOptimal :
    definition5_measure_approxBayesOptimalSpec := by
  intro X Y _ _ law _ loss _ certificates _ epsilon current _
  constructor
  · rfl
  · intro hpositive
    constructor
    · intro happ pair hpair
      exact (measureApproxBayesOptimal_pair_iff_source law loss epsilon current
        pair.2 pair.1 (hpositive pair hpair)).1 (happ pair hpair)
    · intro hsource pair hpair
      exact (measureApproxBayesOptimal_pair_iff_source law loss epsilon current
        pair.2 pair.1 (hpositive pair hpair)).2 (hsource pair hpair)

/-- Checked arbitrary-population endpoint for Definition 7. -/
theorem definition7_measure_certificate : definition7_measure_certificateSpec := by
  intro X Y _ _ law _ loss _ current _ group _ replacement _ mu Delta
  rfl

/-- Checked arbitrary-population endpoint for Theorem 8. -/
theorem theorem8_measure_certificate_characterization :
    theorem8_measure_certificate_characterizationSpec := by
  intro X Y _ _ law _ loss _ certificates hmeasurable epsilon hepsilon current _
  exact theorem8_measure_certificate_iff_not_approxBayesOptimal law loss
    certificates (fun pair hpair ↦ (hmeasurable pair hpair).1) epsilon
      hepsilon current

/-- Checked arbitrary-population endpoint for Theorem 9. -/
theorem theorem9_measure_listUpdate_progress_endpoint :
    theorem9_measure_listUpdate_progressSpec := by
  intro X Y _ _ law _ loss hloss current replacement hcurrent hreplacement
    group hgroup mu Delta hcertificate
  exact theorem9_measure_listUpdate_progress hloss hcurrent hreplacement hgroup
    hcertificate

/-- Checked arbitrary-population endpoint for Theorem 10. -/
theorem theorem10_measure_update_count_endpoint :
    theorem10_measure_update_countSpec := by
  intro X Y _ _ law _ loss hloss epsilon hepsilon initial updates hvalid
  exact theorem10_measure_update_count law hloss epsilon hepsilon initial updates
    hvalid

/-- Checked arbitrary-population endpoint for corrected Theorem 11. -/
theorem theorem11_measure_adaptive_certificate_checker :
    theorem11_measure_adaptive_certificate_checkerSpec := by
  intro X Y _ _ law _ loss hloss epsilon hepsilon n U hcount strategy hstrategy
  exact theorem11_measure_adaptive_certificateCheckerRun law hloss epsilon
    hepsilon n U hcount strategy hstrategy

/-- Checked arbitrary-population endpoint for corrected Theorem 12. -/
theorem theorem12_measure_falsifyAndUpdate :
    theorem12_measure_falsifyAndUpdateSpec := by
  intro X Y _ _ law _ loss hloss epsilon hepsilon n U hcount initial hinitial
    strategy hstrategy
  exact theorem12_measure_adaptive_falsifyAndUpdate law hloss epsilon hepsilon
    n U hcount initial hinitial strategy hstrategy

/-- Checked arbitrary-population endpoint for corrected Remark 13. -/
theorem remark13_measure_logarithmic_submission_dependence :
    remark13_measure_logarithmic_submission_dependenceSpec := by
  intro X Y _ _ law _ loss hloss U K family hfamily epsilon hepsilon n hcount
  exact remark13_measure_sparse_adaptive_failure_bound law hloss U K family
    hfamily epsilon hepsilon n hcount

/-- Checked arbitrary-population endpoint for corrected Theorem 14. -/
theorem theorem14_measure_monotoneBounty_endpoint :
    theorem14_measure_monotoneBountySpec := by
  intro X Y _ _ law _ loss hloss epsilon hepsilon n U hcount initial hinitial
    strategy hstrategy
  exact theorem14_measure_monotoneBounty law hloss epsilon hepsilon n U hcount
    initial hinitial strategy hstrategy

/-- Checked arbitrary-population endpoint for Lemma 15. -/
theorem lemma15_measure_vc_uniform_convergence_endpoint :
    lemma15_measure_vc_uniform_convergenceSpec := by
  intro X _ law _ current hcurrent G H hGmeasurable hHmeasurable dG dH hvcG
    hvcH n hcount hdimension delta hdelta hupdateEvents hcurrentEvents
  exact measureLemma15_vc_uniform_convergence law hcurrent G H hGmeasurable
    hHmeasurable dG dH hvcG hvcH n hcount hdimension delta hdelta
    hupdateEvents hcurrentEvents

/-- Checked arbitrary-population endpoint for Theorem 16. -/
theorem theorem16_measure_trainByOpt : theorem16_measure_trainByOptSpec := by
  intro X _ law _ G H hGmeasurable hHmeasurable C hcontained hCmeasurable
    dG dH hvcG hvcH epsilon hepsilon blockSize hcount hdimension oracle
    horacle initial hinitial delta hdelta hradius hupdateEvents hcurrentEvents
    hpairMeasurable
  exact measureTheorem16_trainByOpt_sourceRounded law G H hGmeasurable
    hHmeasurable C hcontained hCmeasurable dG dH hvcG hvcH epsilon hepsilon
    hcount hdimension oracle horacle hinitial delta hdelta hradius
    hupdateEvents hcurrentEvents hpairMeasurable

/-- Checked arbitrary-population endpoint for Definition 18. -/
theorem definition18_measure_costSensitiveMinimizer :
    definition18_measure_costSensitiveMinimizerSpec := by
  intro X _ law _ current _ K pStar _
  rfl

/-- Checked arbitrary-population endpoint for Theorem 20. -/
theorem theorem20_measure_ternary_cost_sensitive_reduction :
    theorem20_measure_ternary_cost_sensitive_reductionSpec := by
  intro X _ law _ current hcurrent K pStar hKmeasurable hmin
  exact measureTheorem20_costSensitive_minimizer_is_certificate_maximizer law
    hcurrent K pStar hKmeasurable hmin

/-- Checked arbitrary-population endpoint for Lemma 21. -/
theorem lemma21_measure_group_erm_reduction :
    lemma21_measure_group_erm_reductionSpec := by
  intro X _ law _ current hcurrent group hgroup H hHmeasurable hStar herm
  exact measureLemma21_groupERM_maximizes_fixed_group law hcurrent hgroup H
    hHmeasurable hStar herm

/-- Checked arbitrary-population endpoint for corrected Lemma 22. -/
theorem lemma22_measure_disagreement_erm_reduction :
    lemma22_measure_disagreement_erm_reductionSpec := by
  intro X _ law _ current replacement hcurrent hreplacement G hGmeasurable
    gStar herm
  exact measureLemma22_disagreementERM_maximizes_fixed_model law hcurrent
    hreplacement G hGmeasurable gStar herm

/-- Checked arbitrary-population endpoint for corrected Algorithm 6. -/
theorem algorithm6_measure_twoGapCoordinateAscent :
    algorithm6_measure_twoGapCoordinateAscentSpec := by
  intro X _ law current epsilon G H oracle pair hpair
  constructor
  · exact measureEpsilonCoordinatewiseLocal_of_step_eq_none law current epsilon
      oracle pair hpair
  · intro next hstep
    exact ⟨measurePairAdmissible_of_step_eq_some law current epsilon oracle pair
        next hpair hstep,
      measureCoordinateAscentStep_improves law current epsilon oracle pair next
        hstep⟩

/-- Checked arbitrary-population endpoint for corrected Theorem 23. -/
theorem theorem23_measure_coordinate_ascent :
    theorem23_measure_coordinate_ascentSpec := by
  constructor
  · intro X _ law _ current hcurrent G H hGmeasurable hHmeasurable epsilon
      hepsilon oracle initial hinitial hpositive
    exact measureTheorem23_coordinateAscent_sourceRounded_positive_certificate
      law hcurrent G H hGmeasurable hHmeasurable epsilon hepsilon oracle initial
      hinitial hpositive
  constructor
  · intro X _ law _ current hcurrent epsilon hepsilon initial updates hsequence
      hinitialGroup hinitialModel hfinalGroup hfinalModel
    exact measureTheorem23_coordinate_update_bound law hcurrent epsilon hepsilon
      initial updates hsequence hinitialGroup hinitialModel hfinalGroup
      hfinalModel
  · exact measureCoordinateAscentFuel_rounds

end GHKR22BiasBounties
