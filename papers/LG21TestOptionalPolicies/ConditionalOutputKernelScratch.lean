import LG21TestOptionalPolicies.ObservedAccessAllProtocolD6OutputBridge

namespace LG21TestOptionalPolicies

open AppliedModelingLib AppliedModelingLib.Probability MeasureTheory ProbabilityTheory

#guard_msgs(drop info) in
#check condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
#guard_msgs(drop info) in
#check condDistrib_congr_left
#guard_msgs(drop info) in
#check condDistrib_comp
#guard_msgs(drop info) in
#check Measure.compProd_map
#guard_msgs(drop info) in
#check Measure.compProd_eq_comp_prod
#guard_msgs(drop info) in
#check Measure.map_comp
#guard_msgs(drop info) in
#check Kernel.id
#guard_msgs(drop info) in
#check Kernel.prodMkLeft
#guard_msgs(drop info) in
#check Kernel.prodMkRight
#guard_msgs(drop info) in
#check Kernel.id_prod_apply'
#guard_msgs(drop info) in
#check Kernel.map_apply'
#guard_msgs(drop info) in
#check Kernel.ext
#guard_msgs(drop info) in
#check Kernel.ext_iff

theorem conditional_output_kernel_of_joint_factorization
    {Omega Base Score Output : Type*}
    [MeasurableSpace Omega] [MeasurableSpace Base] [MeasurableSpace Score]
    [MeasurableSpace Output] [StandardBorelSpace Output] [Nonempty Output]
    (law : Measure Omega) [IsFiniteMeasure law]
    (base : Omega -> Base) (score : Omega -> Score) (output : Omega -> Output)
    (scoreKernel : Kernel Base Score) [IsMarkovKernel scoreKernel]
    (estimate : Base × Score -> Output) (hestimate : Measurable estimate)
    (hbase : Measurable base) (hscore : Measurable score)
    (houtput_measurable : Measurable output)
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
  have houtputPair :
      law.map (fun omega => (base omega, output omega)) =
        law.map (fun omega =>
          (base omega, estimate (base omega, score omega))) := by
    apply Measure.map_congr
    filter_upwards [houtput] with omega homega
    rw [homega]
  have hjoint : law.map (fun omega => (base omega, output omega)) =
      law.map base ⊗ₘ (Kernel.id ×ₖ scoreKernel).map estimate := by
    rw [houtputPair]
    calc
      law.map (fun omega =>
          (base omega, estimate (base omega, score omega))) =
          (law.map (fun omega => (base omega, score omega))).map
            (fun pair : Base × Score => (pair.1, estimate pair)) := by
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
  exact condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    hbase houtput_measurable hjoint

theorem continuous_source_actual_output_conditional_kernel
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
    (actualOutput : Bool × (ℝ × (Feature -> ℝ)) -> ℝ)
    (hactualOutput_measurable : Measurable actualOutput) :
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
    hactualOutput_measurable hfactor hactualOutput

end LG21TestOptionalPolicies
