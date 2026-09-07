import GHKR22BiasBounties.DistributionalProofInterface
import GHKR22BiasBounties.PaperInterface

/-!
# Proof Interface: An Algorithmic Framework for Bias Bounties

This file contains exact-type proof endpoints for the transparent propositions
in `PaperInterface.lean`. It is not a human semantic-review surface: one source
claim is reviewed once, against its expanded `...Spec : Prop` declaration.
-/

namespace GHKR22BiasBounties

/-- Checked endpoint for Definition 1. -/
theorem definition1_subgroups : definition1_subgroupsSpec := by
  intro X Y _ _ _ _ law g
  rfl

/-- Checked endpoint for Definition 2. -/
theorem definition2_modelLoss : definition2_modelLossSpec := by
  intro X Y _ _ _ _ law loss f g
  exact ⟨rfl, rfl⟩

/-- Checked endpoint for Definition 3. -/
theorem definition3_bayesOptimal : definition3_bayesOptimalSpec := by
  intro X Y _ _ _ _ law loss f
  rfl

/-- Checked endpoint for Definition 5, including its positive-mass source
bridge. -/
theorem definition5_approxBayesOptimal : definition5_approxBayesOptimalSpec := by
  intro X Y _ _ _ _ law loss certificates epsilon f
  constructor
  · rfl
  · intro hpositive
    constructor
    · intro happ pair hpair
      exact (approxBayesOptimal_pair_iff_source law loss epsilon f pair.2 pair.1
        (hpositive pair hpair)).1 (happ pair hpair)
    · intro hsource pair hpair
      exact (approxBayesOptimal_pair_iff_source law loss epsilon f pair.2 pair.1
        (hpositive pair hpair)).2 (hsource pair hpair)

/-- Checked endpoint for Definition 7. -/
theorem definition7_certificate : definition7_certificateSpec := by
  intro X Y _ _ _ _ law loss f g h mu Delta
  rfl

/-- Checked endpoint for Observation 4. -/
theorem observation4_bayes_groupwise : observation4_bayes_groupwiseSpec := by
  intro X Y _ _ _ _ law loss f
  exact observation4_bayesOptimal_iff_groupwiseOptimal law loss f

/-- Checked audit endpoint for the arbitrary-distribution failure of printed
Observation 4. -/
theorem observation4_arbitraryDistribution_counterexample :
    observation4_arbitraryDistribution_counterexampleSpec :=
  observation4_arbitraryDistribution_pointwise_iff_counterexample

/-- Checked endpoint for the corrected almost-everywhere arbitrary-distribution
form of Observation 4. -/
theorem observation4_arbitraryDistribution_ae :
    observation4_arbitraryDistribution_aeSpec := by
  intro X Y _ _ featureLaw _ labels _ loss hloss current hcurrent
  exact observation4_kernelAEModelwiseOptimal_iff_groupwiseOptimal
    featureLaw labels loss hloss current hcurrent

/-- Checked endpoint for Theorem 8. -/
theorem theorem8_certificate_characterization :
    theorem8_certificate_characterizationSpec := by
  intro X Y _ _ _ _ law loss certificates epsilon hepsilon f
  exact theorem8_certificate_iff_not_approxBayesOptimal
    law loss certificates epsilon hepsilon f

/-- Checked endpoint for Algorithm 1. -/
theorem algorithm1_listUpdate : algorithm1_listUpdateSpec := by
  intro X Y f g h x
  rfl

/-- Checked endpoint for Theorem 9. -/
theorem theorem9_listUpdate_progress_endpoint :
    theorem9_listUpdate_progressSpec := by
  intro X Y _ _ _ _ law loss f g h mu Delta hcert
  exact theorem9_listUpdate_progress hcert

/-- Checked endpoint for Theorem 10. -/
theorem theorem10_update_count : theorem10_update_countSpec := by
  intro X Y _ _ _ _ law loss epsilon hepsilon initial updates hvalid
  exact theorem10_update_count_le_loss_div
    law loss epsilon hepsilon initial updates hvalid

/-- Checked endpoint for the certificate-optimization objective. -/
theorem certificateOptimizationObjective :
    certificateOptimizationObjectiveSpec := by
  intro X Y n loss sample current candidates chosen
  rfl

/-- Checked endpoint for Algorithm 2. -/
theorem algorithm2_certificateChecker : algorithm2_certificateCheckerSpec := by
  intro X Y n epsilon loss sample submission
  exact ⟨certificateCheckerDecision_eq_accepted_iff epsilon loss sample submission,
    certificateCheckerDecision_eq_rejected_iff epsilon loss sample submission⟩

/-- Checked endpoint for corrected Theorem 11. -/
theorem theorem11_adaptive_certificate_checker :
    theorem11_adaptive_certificate_checkerSpec := by
  intro X Y _ _ _ _ law loss epsilon hepsilon n U hcount strategy
  exact theorem11_adaptive_certificateCheckerRun
    law loss epsilon hepsilon n U hcount strategy

/-- Checked endpoint for Algorithm 3. -/
theorem algorithm3_falsifyAndUpdate : algorithm3_falsifyAndUpdateSpec := by
  intro X Y n epsilon loss sample state proposal
  unfold falsifyAndUpdateStep
  cases certificateCheckerDecision epsilon loss sample
      (proposalSubmission state proposal) <;> simp

/-- Checked endpoint for Theorem 12. -/
theorem theorem12_falsifyAndUpdate : theorem12_falsifyAndUpdateSpec := by
  intro X Y _ _ _ _ law loss epsilon hepsilon n U hcount initial strategy
  exact theorem12_adaptive_falsifyAndUpdate
    law loss epsilon hepsilon n U hcount initial strategy

/-- Checked endpoint for corrected Remark 13. -/
theorem remark13_logarithmic_submission_dependence :
    remark13_logarithmic_submission_dependenceSpec := by
  intro X Y _ _ _ _ law loss U K family epsilon n hcount hepsilon
  exact remark13_sparse_adaptive_failure_bound
    law loss U K family epsilon n hcount hepsilon

/-- Checked endpoint for corrected whole-process Algorithm 4. -/
theorem algorithm4_monotoneBounty : algorithm4_monotoneBountySpec := by
  constructor
  · intro X Y n epsilon loss sample U initial strategy
    rfl
  constructor
  · intro X Y initial U strategy transcript decision
    dsimp
    refine ⟨rfl,
      monotoneBountyStateFromTranscript_append_singleton initial U strategy
        transcript decision, ?_, ?_, ?_⟩
    · intro candidate rest hremaining
      cases rest <;> simp [monotoneBountyStepCore, hremaining]
    · intro hrepairs hexternal
      simp [monotoneBountyStepCore, hrepairs, hexternal]
    · intro candidate rest hremaining
      cases rest <;> simp [monotoneBountyStepCore, hremaining]
  · intro epsilon U
    rfl

/-- Checked endpoint for corrected whole-process Theorem 14. -/
theorem theorem14_monotoneBounty_endpoint : theorem14_monotoneBountySpec := by
  intro X Y _ _ _ _ law loss epsilon hepsilon n U hcount initial strategy
  exact theorem14_monotoneBounty law loss epsilon hepsilon n U hcount initial
    strategy

/-- Checked endpoint for Lemma 15's VC statement. -/
theorem lemma15_vc_uniform_convergence_endpoint :
    lemma15_vc_uniform_convergenceSpec := by
  intro X _ _ law current G H dG dH hvcG hvcH n hcount hdimension
    delta hdelta
  exact lemma15_vc_uniform_convergence law current G H dG dH hvcG hvcH
    n hcount hdimension delta hdelta

/-- Checked endpoint for the corrected complete Algorithm 5 semantics. -/
theorem algorithm5_trainByOpt : algorithm5_trainByOptSpec := by
  constructor
  · intro X Y n loss C epsilon oracle initial _
    constructor
    · intro trace
      rfl
    · intro rounds trace
      rfl
  · intro epsilon _hepsilon
    rfl

/-- Checked endpoint for Theorem 16. -/
theorem theorem16_trainByOpt : theorem16_trainByOptSpec := by
  intro X _ _ law G H C hcontained dG dH hvcG hvcH epsilon hepsilon
    blockSize hcount hdimension oracle horacle initial delta hdelta hradius
  exact theorem16_trainByOpt_sourceRounded law G H C hcontained dG dH hvcG hvcH
    epsilon hepsilon hcount hdimension oracle horacle initial delta hdelta hradius

/-- Checked endpoint for Definition 17. -/
theorem definition17_derivedCertificate : definition17_derivedCertificateSpec := by
  intro X p x
  exact ⟨rfl, rfl⟩

/-- Checked endpoint for Definition 18. -/
theorem definition18_costSensitiveMinimizer :
    definition18_costSensitiveMinimizerSpec := by
  intro X _ _ law current K pStar
  rfl

/-- Checked endpoint for Definition 19. -/
theorem definition19_inducedCost : definition19_inducedCostSpec := by
  intro X current datum prediction
  exact inducedCost_cases current datum prediction

/-- Checked endpoint for Theorem 20. -/
theorem theorem20_ternary_cost_sensitive_reduction :
    theorem20_ternary_cost_sensitive_reductionSpec := by
  intro X _ _ law current K pStar hmin
  exact theorem20_costSensitive_minimizer_is_certificate_maximizer
    law current K pStar hmin

/-- Checked endpoint for Lemma 21. -/
theorem lemma21_group_erm_reduction : lemma21_group_erm_reductionSpec := by
  intro X _ _ law current g H hStar herm
  exact lemma21_groupERM_maximizes_fixed_group law current g H hStar herm

/-- Checked endpoint for corrected Lemma 22. -/
theorem lemma22_disagreement_erm_reduction :
    lemma22_disagreement_erm_reductionSpec := by
  intro X _ _ law current replacement G gStar herm
  exact lemma22_disagreementERM_maximizes_fixed_model
    law current replacement G gStar herm

/-- Checked endpoint for corrected Algorithm 6. -/
theorem algorithm6_twoGapCoordinateAscent :
    algorithm6_twoGapCoordinateAscentSpec := by
  intro X _ _ law current epsilon G H oracle pair hpair
  constructor
  · exact epsilonCoordinatewiseLocal_of_coordinateAscentStep_eq_none
      law current epsilon oracle pair hpair
  · intro next hstep
    exact ⟨pairAdmissible_of_coordinateAscentStep_eq_some
        law current epsilon oracle pair next hpair hstep,
      coordinateAscentStep_improves law current epsilon oracle pair next hstep⟩

/-- Checked endpoint for corrected Theorem 23. -/
theorem theorem23_coordinate_ascent : theorem23_coordinate_ascentSpec := by
  constructor
  · intro X _ _ law current epsilon hepsilon G H oracle fuel hbudget initial
      hinitial
    exact theorem23_coordinateAscentLoop_total
      law current epsilon hepsilon oracle fuel hbudget initial hinitial
  constructor
  · intro X _ _ law current epsilon hepsilon initial updates hsequence
    exact theorem23_coordinate_update_bound
      law current epsilon hepsilon initial updates hsequence
  constructor
  · intro X _ _ law current pair hpositive
    exact local_pair_certificate_of_positive_objective law current pair hpositive
  · intro X _ _ law current epsilon hepsilon G H oracle fuel hbudget initial
      hinitial hpositive
    exact theorem23_coordinateAscentLoop_positive_certificate law current
      epsilon hepsilon oracle fuel hbudget initial hinitial hpositive

/-- Checked endpoint for the printed Theorem 23 counterexample. -/
theorem theorem23_source_claim_counterexample :
    theorem23_source_claim_counterexampleSpec :=
  theorem23_local_optimum_without_positive_certificate

/-! ## Exact endpoints for the canonical source-result surface -/

theorem source_observation4 : source_observation4Spec :=
  observation4_arbitraryDistribution_ae

theorem source_theorem8 : source_theorem8Spec :=
  theorem8_measure_certificate_characterization

theorem source_theorem9 : source_theorem9Spec :=
  theorem9_measure_listUpdate_progress_endpoint

theorem source_theorem10 : source_theorem10Spec :=
  theorem10_measure_update_count_endpoint

theorem source_theorem11 : source_theorem11Spec :=
  theorem11_measure_adaptive_certificate_checker

theorem source_theorem12 : source_theorem12Spec :=
  theorem12_measure_falsifyAndUpdate

theorem source_remark13 : source_remark13Spec :=
  remark13_measure_logarithmic_submission_dependence

theorem source_theorem14 : source_theorem14Spec :=
  theorem14_measure_monotoneBounty_endpoint

theorem source_lemma15 : source_lemma15Spec :=
  lemma15_measure_vc_uniform_convergence_endpoint

theorem source_theorem16 : source_theorem16Spec :=
  theorem16_measure_trainByOpt

theorem source_theorem20 : source_theorem20Spec :=
  theorem20_measure_ternary_cost_sensitive_reduction

theorem source_lemma21 : source_lemma21Spec :=
  lemma21_measure_group_erm_reduction

theorem source_lemma22 : source_lemma22Spec :=
  lemma22_measure_disagreement_erm_reduction

theorem source_algorithm6_twoGapCoordinateAscent :
    source_algorithm6_twoGapCoordinateAscentSpec :=
  algorithm6_measure_twoGapCoordinateAscent

theorem source_theorem23 : source_theorem23Spec :=
  theorem23_measure_coordinate_ascent

end GHKR22BiasBounties
