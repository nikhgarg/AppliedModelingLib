import LG21TestOptionalPolicies.ObservedAccessAllProtocolD6OutputBridge

/-!
# Conditional output kernels for the LG21 observed-access source model

This module transports a literal a.e. output identity and a proved source
joint-law factorization into a conditional output-kernel identity.  It is
deliberately independent of protocol names: callers must supply the actual
output, its measurability, the joint factorization, and the on-path identity.

The resulting equality is almost everywhere in the base-profile marginal.
Regular conditional distributions have no canonical values on null fibres.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib AppliedModelingLib.Probability MeasureTheory ProbabilityTheory

/-- An a.e. output identity transports a proved `(base, score)`
factorization to the output's regular conditional distribution given the
base. -/
theorem conditional_output_kernel_of_joint_factorization
    {Omega Base Score Output : Type*}
    [MeasurableSpace Omega] [MeasurableSpace Base] [MeasurableSpace Score]
    [MeasurableSpace Output] [StandardBorelSpace Output] [Nonempty Output]
    (law : Measure Omega) [IsFiniteMeasure law]
    (base : Omega -> Base) (score : Omega -> Score) (output : Omega -> Output)
    (scoreKernel : Kernel Base Score) [IsMarkovKernel scoreKernel]
    (estimate : Base × Score -> Output) (hestimate : Measurable estimate)
    (hbase : Measurable base) (hscore : Measurable score)
    (hfactor : law.map (fun omega => (base omega, score omega)) =
      law.map base ⊗ₘ scoreKernel)
    (houtput : output =ᵐ[law]
      fun omega => estimate (base omega, score omega)) :
    condDistrib output base law =ᵐ[law.map base]
      (Kernel.id ×ₖ scoreKernel).map estimate := by
  have hpair : Measurable (fun pair : Base × Score =>
      (pair.1, estimate pair)) :=
    measurable_fst.prodMk hestimate
  have hprodMap : Measurable (Prod.map (id : Base -> Base) estimate) :=
    measurable_id.prodMap hestimate
  have hsource : Measurable (fun omega =>
      (base omega, score omega)) := hbase.prodMk hscore
  let canonicalOutput : Omega -> Output := fun omega =>
    estimate (base omega, score omega)
  have hcanonicalOutput : Measurable canonicalOutput :=
    hestimate.comp hsource
  have hjoint : law.map (fun omega => (base omega, canonicalOutput omega)) =
      law.map base ⊗ₘ (Kernel.id ×ₖ scoreKernel).map estimate := by
    calc
      law.map (fun omega =>
          (base omega, canonicalOutput omega)) =
          (law.map (fun omega => (base omega, score omega))).map
            (fun pair : Base × Score => (pair.1, estimate pair)) := by
            change law.map (fun omega =>
              (base omega, estimate (base omega, score omega))) = _
            symm
            exact Measure.map_map hpair hsource
      _ = (law.map base ⊗ₘ scoreKernel).map
          (fun pair : Base × Score => (pair.1, estimate pair)) := by
            rw [hfactor]
      _ = law.map base ⊗ₘ (Kernel.id ×ₖ scoreKernel).map estimate := by
        rw [Measure.compProd_map hestimate,
          Measure.compProd_eq_comp_prod,
          Measure.compProd_eq_comp_prod]
        rw [Measure.map_comp _ _ hpair,
          Measure.map_comp _ _ hprodMap]
        congr 1
        ext publicBase target htarget
        rw [Kernel.map_apply' _ hpair publicBase htarget,
          Kernel.id_prod_apply' scoreKernel publicBase (hpair htarget),
          Kernel.map_apply' _ hprodMap publicBase htarget,
          Kernel.id_prod_apply' (Kernel.id ×ₖ scoreKernel) publicBase
            (hprodMap htarget)]
        have hinnerTarget : MeasurableSet
            (Prod.mk publicBase ⁻¹'
              (Prod.map (id : Base -> Base) estimate ⁻¹' target)) := by
          exact (measurable_const.prodMk measurable_id) (hprodMap htarget)
        rw [Kernel.id_prod_apply' scoreKernel publicBase hinnerTarget]
        rfl
  have hcanonical : condDistrib canonicalOutput base law =ᵐ[law.map base]
      (Kernel.id ×ₖ scoreKernel).map estimate :=
    condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
      hbase hcanonicalOutput hjoint
  rw [condDistrib_congr_left houtput]
  exact hcanonical

/-- The literal Gaussian source specialization.  Once a protocol proves that
its actual output is the all-report PBO estimator almost everywhere, this
identifies its conditional output kernel without assuming fairness. -/
theorem lg21ContinuousGaussianAccessPopulation_actualOutput_conditionalKernel_eq_d6
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean) (baseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (hfullBaseFactorization :
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature =
        baseLaw ⊗ₘ gaussianLocationKernel
          baseMean hbaseMean baseVariance.toNNReal)
    (actualOutput : Bool × (ℝ × (Feature -> ℝ)) -> ℝ) :
    let S : LG21GaussianPBOResamplingSource
        (LG21NonTestFeature Feature testFeature -> ℝ) :=
      { baseLaw := baseLaw
        baseLaw_isProbability := inferInstance
        posteriorBaseMean := baseMean
        posteriorBaseMean_measurable := hbaseMean
        posteriorBaseVariance := baseVariance.toNNReal
        posteriorBaseVariance_pos := by
          rw [NNReal.coe_pos, Real.toNNReal_pos]
          exact hbaseVariance
        testNoiseVariance := M.noiseVariance testFeature
        testNoiseVariance_pos := htestNoiseVariance }
    letI : IsProbabilityMeasure
        (lg21ContinuousGaussianAccessPopulationLaw M) :=
      lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
    letI : IsFiniteMeasure
        (lg21ContinuousGaussianAccessPopulationLaw M) := ⟨by simp⟩
    (actualOutput =ᵐ[lg21ContinuousGaussianAccessPopulationLaw M]
      fun student => lg21D6GaussianPBOEstimate S
        (lg21ContinuousPopulationBase testFeature student,
          lg21ContinuousPopulationFeature testFeature student)) ->
    condDistrib actualOutput (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousGaussianAccessPopulationLaw M) =ᵐ[
        (lg21ContinuousGaussianAccessPopulationLaw M).map
          (lg21ContinuousPopulationBase testFeature)]
        lg21D6ActualAccessEstimateKernel S := by
  intro S hactualOutput
  let law := lg21ContinuousGaussianAccessPopulationLaw M
  let sourceBase := lg21ContinuousPopulationBase testFeature
  let sourceScore := lg21ContinuousPopulationFeature testFeature
  letI : IsProbabilityMeasure law :=
    lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
  letI : IsFiniteMeasure law := ⟨by simp⟩
  letI : IsMarkovKernel (lg21D6ConditionalGaussianTestKernel S) :=
    lg21D6ConditionalGaussianTestKernel_isMarkov S
  have hbase : Measurable sourceBase :=
    lg21ContinuousPopulationBase_measurable testFeature
  have hscore : Measurable sourceScore := by
    change Measurable fun student : Bool × (ℝ × (Feature -> ℝ)) =>
      student.2.1 + student.2.2 testFeature
    exact (measurable_fst.comp measurable_snd).add
      ((measurable_pi_apply testFeature).comp
        (measurable_snd.comp measurable_snd))
  have hfactor : law.map (fun student =>
      (sourceBase student, sourceScore student)) =
      law.map sourceBase ⊗ₘ lg21D6ConditionalGaussianTestKernel S := by
    have hjoint :=
      lg21ContinuousGaussianAccessPopulation_fullBaseScoreLaw_eq_d6
        M haccess testFeature baseLaw baseMean hbaseMean baseVariance
        hbaseVariance htestNoiseVariance hfullBaseFactorization
    have hbaseLaw :=
      lg21ContinuousGaussianAccessPopulation_baseLaw_eq_of_factorization
        M haccess testFeature baseLaw baseMean hbaseMean baseVariance
        hbaseVariance htestNoiseVariance hfullBaseFactorization
    change law.map (fun student => (sourceBase student, sourceScore student)) =
      law.map sourceBase ⊗ₘ lg21D6ConditionalGaussianTestKernel S
    rw [hjoint, hbaseLaw]
    rfl
  change actualOutput =ᵐ[law]
      (fun student => lg21D6GaussianPBOEstimate S
        (sourceBase student, sourceScore student)) at hactualOutput
  exact conditional_output_kernel_of_joint_factorization
    law sourceBase sourceScore actualOutput
    (lg21D6ConditionalGaussianTestKernel S) (lg21D6GaussianPBOEstimate S)
    (lg21D6GaussianPBOEstimate_measurable S) hbase hscore
    hfactor hactualOutput

/-- A literal access output that is the Definition 6 estimator almost
everywhere is observably fair (up to null base fibres) against the literal
no-access resampling policy, and has the same demographic output law.  The
premise is an output identity, not a supplied fairness or output-law equality.
-/
theorem lg21ContinuousGaussianAccessPopulation_actualOutput_observableAndDemographicFair_of_d6_ae
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true})
    (hnoAccess : 0 < M.accessLaw {false}) (testFeature : Feature)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean) (baseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (hfullBaseFactorization :
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature =
        baseLaw ⊗ₘ gaussianLocationKernel
          baseMean hbaseMean baseVariance.toNNReal)
    (actualOutput : Bool × (ℝ × (Feature -> ℝ)) -> ℝ) :
    let S : LG21GaussianPBOResamplingSource
        (LG21NonTestFeature Feature testFeature -> ℝ) :=
      { baseLaw := baseLaw
        baseLaw_isProbability := inferInstance
        posteriorBaseMean := baseMean
        posteriorBaseMean_measurable := hbaseMean
        posteriorBaseVariance := baseVariance.toNNReal
        posteriorBaseVariance_pos := by
          rw [NNReal.coe_pos, Real.toNNReal_pos]
          exact hbaseVariance
        testNoiseVariance := M.noiseVariance testFeature
        testNoiseVariance_pos := htestNoiseVariance }
    letI : IsProbabilityMeasure
        (lg21ContinuousGaussianAccessPopulationLaw M) :=
      lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
    letI : IsFiniteMeasure
        (lg21ContinuousGaussianAccessPopulationLaw M) := ⟨by simp⟩
    (actualOutput =ᵐ[lg21ContinuousGaussianAccessPopulationLaw M]
      fun student => lg21D6GaussianPBOEstimate S
        (lg21ContinuousPopulationBase testFeature student,
          lg21ContinuousPopulationFeature testFeature student)) ->
    (condDistrib actualOutput (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousGaussianAccessPopulationLaw M) =ᵐ[
        (lg21ContinuousGaussianAccessPopulationLaw M).map
          (lg21ContinuousPopulationBase testFeature)]
        lg21D6NoAccessResamplingEstimateKernel S) ∧
      ((lg21ContinuousGaussianAccessPopulationLaw M).map actualOutput =
        Measure.bind
          ((lg21ContinuousGaussianNoAccessPopulationLaw M).map
            (lg21ContinuousPopulationBase testFeature))
          (lg21D6NoAccessResamplingEstimateKernel S)) := by
  intro S hactualOutput
  let accessLaw := lg21ContinuousGaussianAccessPopulationLaw M
  let noAccessLaw := lg21ContinuousGaussianNoAccessPopulationLaw M
  let observation : Bool × (ℝ × (Feature -> ℝ)) ->
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ :=
    fun student =>
      (lg21ContinuousPopulationBase testFeature student,
        lg21ContinuousPopulationFeature testFeature student)
  letI : IsProbabilityMeasure accessLaw :=
    lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
  letI : IsFiniteMeasure accessLaw := ⟨by simp⟩
  have hbase : Measurable (lg21ContinuousPopulationBase testFeature) :=
    lg21ContinuousPopulationBase_measurable testFeature
  have hscore : Measurable
      (lg21ContinuousPopulationFeature (Feature := Feature) testFeature) := by
    change Measurable fun student : Bool × (ℝ × (Feature -> ℝ)) =>
      student.2.1 + student.2.2 testFeature
    exact (measurable_fst.comp measurable_snd).add
      ((measurable_pi_apply testFeature).comp
        (measurable_snd.comp measurable_snd))
  have hobservation : Measurable observation := hbase.prodMk hscore
  have hactualOutput' : actualOutput =ᵐ[accessLaw]
      fun student => lg21D6GaussianPBOEstimate S (observation student) := by
    simpa [accessLaw, observation] using hactualOutput
  have hconditionalD6 :
      condDistrib actualOutput (lg21ContinuousPopulationBase testFeature) accessLaw =ᵐ[
        accessLaw.map (lg21ContinuousPopulationBase testFeature)]
        lg21D6ActualAccessEstimateKernel S := by
    simpa [accessLaw] using
      (lg21ContinuousGaussianAccessPopulation_actualOutput_conditionalKernel_eq_d6
        M haccess testFeature baseLaw baseMean hbaseMean baseVariance
        hbaseVariance htestNoiseVariance hfullBaseFactorization actualOutput
        hactualOutput)
  have hconditional :
      condDistrib actualOutput (lg21ContinuousPopulationBase testFeature) accessLaw =ᵐ[
        accessLaw.map (lg21ContinuousPopulationBase testFeature)]
        lg21D6NoAccessResamplingEstimateKernel S := by
    filter_upwards [hconditionalD6] with publicBase hkernel
    exact hkernel.trans (lg21D6GaussianPBOResampling_observably_fair S publicBase)
  refine ⟨by simpa [accessLaw] using hconditional, ?_⟩
  have hd6Demographic :=
    lg21ContinuousGaussianPopulation_d6AccessOutput_eq_noAccessResampling
      M haccess hnoAccess testFeature baseLaw baseMean hbaseMean baseVariance
      hbaseVariance htestNoiseVariance hfullBaseFactorization
  calc
    (lg21ContinuousGaussianAccessPopulationLaw M).map actualOutput =
        accessLaw.map (fun student =>
          lg21D6GaussianPBOEstimate S (observation student)) := by
          exact Measure.map_congr hactualOutput'
    _ = (accessLaw.map observation).map (lg21D6GaussianPBOEstimate S) := by
      rw [Measure.map_map (lg21D6GaussianPBOEstimate_measurable S) hobservation]
      rfl
    _ = Measure.bind
        (noAccessLaw.map (lg21ContinuousPopulationBase testFeature))
        (lg21D6NoAccessResamplingEstimateKernel S) := by
      simpa [accessLaw, noAccessLaw, observation] using hd6Demographic
    _ = Measure.bind
        ((lg21ContinuousGaussianNoAccessPopulationLaw M).map
          (lg21ContinuousPopulationBase testFeature))
        (lg21D6NoAccessResamplingEstimateKernel S) := by
      rfl

/-- The common literal observed-access endpoint for Theorem 4.4.  The action
collapse and on-path PBO identity are used only to derive the a.e. D6 output
identity; fairness is then obtained from the source Gaussian experiment. -/
theorem lg21ContinuousGaussianAccessPopulation_observedAccessOutput_observableAndDemographicFair_of_all_take_report_and_pbo
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true})
    (hnoAccess : 0 < M.accessLaw {false}) (testFeature : Feature)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean) (baseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (hfullBaseFactorization :
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature =
        baseLaw ⊗ₘ gaussianLocationKernel
          baseMean hbaseMean baseVariance.toNNReal)
    (action : Bool × (ℝ × (Feature -> ℝ)) -> LG21AccessAction)
    (reportedPayoff : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ -> ℝ)
    (noReportPayoff : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hall : ∀ᵐ student ∂lg21ContinuousGaussianAccessPopulationLaw M,
      action student = LG21AccessAction.takeAndReport)
    (hreportedPBO : LG21ObservedAccessAllReportPBO
      (lg21ContinuousGaussianAccessPopulationLaw M)
      (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationFeature testFeature)
      (lg21ContinuousPopulationSkill (Feature := Feature)) reportedPayoff) :
    let S : LG21GaussianPBOResamplingSource
        (LG21NonTestFeature Feature testFeature -> ℝ) :=
      { baseLaw := baseLaw
        baseLaw_isProbability := inferInstance
        posteriorBaseMean := baseMean
        posteriorBaseMean_measurable := hbaseMean
        posteriorBaseVariance := baseVariance.toNNReal
        posteriorBaseVariance_pos := by
          rw [NNReal.coe_pos, Real.toNNReal_pos]
          exact hbaseVariance
        testNoiseVariance := M.noiseVariance testFeature
        testNoiseVariance_pos := htestNoiseVariance }
    letI : IsProbabilityMeasure
        (lg21ContinuousGaussianAccessPopulationLaw M) :=
      lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
    letI : IsFiniteMeasure
        (lg21ContinuousGaussianAccessPopulationLaw M) := ⟨by simp⟩
    let actualOutput := lg21ObservedAccessActualOutput
      (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationFeature testFeature)
      action reportedPayoff noReportPayoff
    (condDistrib actualOutput (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousGaussianAccessPopulationLaw M) =ᵐ[
        (lg21ContinuousGaussianAccessPopulationLaw M).map
          (lg21ContinuousPopulationBase testFeature)]
        lg21D6NoAccessResamplingEstimateKernel S) ∧
      ((lg21ContinuousGaussianAccessPopulationLaw M).map actualOutput =
        Measure.bind
          ((lg21ContinuousGaussianNoAccessPopulationLaw M).map
            (lg21ContinuousPopulationBase testFeature))
          (lg21D6NoAccessResamplingEstimateKernel S)) := by
  intro S actualOutput
  letI : IsProbabilityMeasure
      (lg21ContinuousGaussianAccessPopulationLaw M) :=
    lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
  letI : IsFiniteMeasure
      (lg21ContinuousGaussianAccessPopulationLaw M) := ⟨by simp⟩
  have hactualOutput : actualOutput =ᵐ[
      lg21ContinuousGaussianAccessPopulationLaw M]
      fun student => lg21D6GaussianPBOEstimate S
        (lg21ContinuousPopulationBase testFeature student,
          lg21ContinuousPopulationFeature testFeature student) := by
    simpa [actualOutput] using
      (lg21ContinuousGaussianAccessPopulation_actualOutput_eq_d6_ae_of_all_take_report_and_pbo
        M haccess testFeature baseLaw baseMean hbaseMean baseVariance
        hbaseVariance htestNoiseVariance hfullBaseFactorization action
        reportedPayoff noReportPayoff hall hreportedPBO)
  simpa [actualOutput] using
    (lg21ContinuousGaussianAccessPopulation_actualOutput_observableAndDemographicFair_of_d6_ae
      M haccess hnoAccess testFeature baseLaw baseMean hbaseMean baseVariance
      hbaseVariance htestNoiseVariance hfullBaseFactorization actualOutput
      hactualOutput)

end

end LG21TestOptionalPolicies
