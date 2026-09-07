import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalForwardPoisson

/-!
# Lemma 1: a coupled Poisson-thinning construction

This file constructs the stochastic bridge used in Lemma 1 rather than taking
the thinned observed path as an assumption.  For a detection probability
strictly between zero and one, the sample space carries independent canonical
Poisson processes for observed and discarded incidents.  Their pointwise sum
is the latent process.  The construction proves that the latent process is a
homogeneous Poisson process at the original incident rate and proves the exact
joint interval-count factorization that expresses conditional binomial
thinning.

The endpoint `p = 1` is handled separately below by identifying the observed
and latent processes.  The paper-facing result also separates the `p = 0`
case, where the displayed observed rate is zero, from the positive-probability
case in which the observed path is packaged as a positive-rate Poisson
process.  Thus neither weak probability bound is silently strengthened.
-/

namespace LBG24SpatialUnderreporting

open Filter MeasureTheory ProbabilityTheory
open AppliedModelingLib.Probability.PoissonProcess
open scoped ENNReal NNReal ProbabilityTheory

noncomputable section

namespace Lemma1MarkedPoissonThinning

/-- The canonical path type used for each independent Poisson component. -/
abbrev Path := ℕ → ℝ

/-- Independent families remain independent after pairing the corresponding
coordinates on a product probability space. -/
private theorem iIndepFun_pair_prod
    {ι Ω₁ Ω₂ α β : Type*}
    [Fintype ι]
    [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure Ω₁} {ν : Measure Ω₂}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : ι → Ω₁ → α} {Y : ι → Ω₂ → β}
    (hX : iIndepFun X μ) (hY : iIndepFun Y ν)
    (mX : ∀ i, Measurable (X i)) (mY : ∀ i, Measurable (Y i)) :
    iIndepFun (fun i z => (X i z.1, Y i z.2)) (μ.prod ν) := by
  classical
  let XV : Ω₁ → (ι → α) := fun ω i => X i ω
  let YV : Ω₂ → (ι → β) := fun ω i => Y i ω
  have mXV : Measurable XV := measurable_pi_lambda _ mX
  have mYV : Measurable YV := measurable_pi_lambda _ mY
  have hmapX : μ.map XV = Measure.pi (fun i => μ.map (X i)) :=
    (iIndepFun_iff_map_fun_eq_pi_map
      (fun i => (mX i).aemeasurable)).mp hX
  have hmapY : ν.map YV = Measure.pi (fun i => ν.map (Y i)) :=
    (iIndepFun_iff_map_fun_eq_pi_map
      (fun i => (mY i).aemeasurable)).mp hY
  apply (iIndepFun_iff_map_fun_eq_pi_map
    (fun i => ((mX i).comp measurable_fst).prodMk
      ((mY i).comp measurable_snd) |>.aemeasurable)).mpr
  let e := MeasurableEquiv.arrowProdEquivProdArrow α β ι
  calc
    (μ.prod ν).map (fun z i => (X i z.1, Y i z.2)) =
        (μ.prod ν).map (e.symm ∘ Prod.map XV YV) := by
      congr 1
    _ = ((μ.prod ν).map (Prod.map XV YV)).map e.symm := by
      exact (Measure.map_map e.symm.measurable
        (mXV.comp measurable_fst |>.prodMk
          (mYV.comp measurable_snd))).symm
    _ = ((μ.map XV).prod (ν.map YV)).map e.symm := by
      rw [Measure.map_prod_map μ ν mXV mYV]
    _ = ((Measure.pi (fun i => μ.map (X i))).prod
          (Measure.pi (fun i => ν.map (Y i)))).map e.symm := by
      rw [hmapX, hmapY]
    _ = Measure.pi (fun i => (μ.map (X i)).prod (ν.map (Y i))) := by
      exact (measurePreserving_arrowProdEquivProdArrow α β ι
        (fun i => μ.map (X i)) (fun i => ν.map (Y i))).symm.map_eq
    _ = Measure.pi (fun i =>
          (μ.prod ν).map (fun z => (X i z.1, Y i z.2))) := by
      congr 1
      funext i
      simpa [Prod.map] using Measure.map_prod_map μ ν (mX i) (mY i)

/-- Pull a finite independent family back along a measure-preserving map. -/
private theorem iIndepFun_comp_measurePreserving
    {Ω S ι : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    [Fintype ι] {P : Measure Ω} {μ : Measure S}
    [IsProbabilityMeasure P] [IsProbabilityMeasure μ]
    {Y : Ω → S} (hY : MeasurePreserving Y P μ)
    {A : ι → Type*} {mA : ∀ i, MeasurableSpace (A i)}
    (Z : ∀ i, S → A i) (hZ : ∀ i, Measurable (Z i))
    (hZindep : iIndepFun Z μ) :
    iIndepFun (fun i => Z i ∘ Y) P := by
  rw [iIndepFun_iff_map_fun_eq_pi_map
    (fun i => ((hZ i).comp hY.measurable).aemeasurable)]
  change P.map ((fun x i => Z i x) ∘ Y) =
    Measure.pi (fun i => P.map (Z i ∘ Y))
  rw [← Measure.map_map (measurable_pi_iff.2 hZ) hY.measurable,
    hY.map_eq,
    (iIndepFun_iff_map_fun_eq_pi_map
      (fun i => (hZ i).aemeasurable)).mp hZindep]
  congr 2
  funext i
  rw [← Measure.map_map (hZ i) hY.measurable, hY.map_eq]

/-- Product-space lift of a forward Poisson process along a coordinate map. -/
private def pullbackForwardProcess
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    {P : Measure Ω} {μ : Measure S}
    [IsProbabilityMeasure P] [IsProbabilityMeasure μ]
    (H : ForwardHomogeneousPoissonCountingProcessByLaw S μ)
    (Y : Ω → S) (hY : MeasurePreserving Y P μ) :
    ForwardHomogeneousPoissonCountingProcessByLaw Ω P where
  isProbability := inferInstance
  rate := H.rate
  rate_pos := H.rate_pos
  count := fun t => H.count t ∘ Y
  count_measurable := fun t => (H.count_measurable t).comp hY.measurable
  count_zero_ae := hY.quasiMeasurePreserving.ae H.count_zero_ae
  count_mono_ae := hY.quasiMeasurePreserving.ae H.count_mono_ae
  hasIndepIncrements := by
    intro n t ht
    exact iIndepFun_comp_measurePreserving hY
      (fun (i : Fin n) s =>
        H.count (t i.succ) s - H.count (t i.castSucc) s)
      (fun (i : Fin n) => (H.count_measurable (t i.succ)).sub
        (H.count_measurable (t i.castSucc)))
      (H.hasIndepIncrements n t ht)
  increment_hasLaw := by
    intro s t hst
    simpa [Function.comp_def] using
      (H.increment_hasLaw hst).comp hY.hasLaw

/-- Observed-component rate. -/
def observedRate (incidentRate detectionProbability : ℝ) : ℝ :=
  incidentRate * detectionProbability

/-- Discarded-component rate. -/
def discardedRate (incidentRate detectionProbability : ℝ) : ℝ :=
  incidentRate * (1 - detectionProbability)

/-- The canonical observed-component law. -/
def observedMeasure (incidentRate detectionProbability : ℝ) : Measure Path :=
  exponentialInterarrivalMeasure
    (observedRate incidentRate detectionProbability)

/-- The canonical discarded-component law. -/
def discardedMeasure (incidentRate detectionProbability : ℝ) : Measure Path :=
  exponentialInterarrivalMeasure
    (discardedRate incidentRate detectionProbability)

/-- Product law carrying independent observed and discarded processes. -/
def productMeasure (incidentRate detectionProbability : ℝ) :
    Measure (Path × Path) :=
  (observedMeasure incidentRate detectionProbability).prod
    (discardedMeasure incidentRate detectionProbability)

private theorem observedRate_pos
    {incidentRate detectionProbability : ℝ}
    (hincident : 0 < incidentRate) (hdetection : 0 < detectionProbability) :
    0 < observedRate incidentRate detectionProbability := by
  exact mul_pos hincident hdetection

private theorem discardedRate_pos
    {incidentRate detectionProbability : ℝ}
    (hincident : 0 < incidentRate) (hdetection_lt : detectionProbability < 1) :
    0 < discardedRate incidentRate detectionProbability := by
  exact mul_pos hincident (sub_pos.mpr hdetection_lt)

/-- The observed canonical process, lifted to the first product coordinate. -/
def observedProcess
    (incidentRate detectionProbability : ℝ)
    (hincident : 0 < incidentRate) (hdetection : 0 < detectionProbability)
    (hdetection_lt : detectionProbability < 1) :
    ForwardHomogeneousPoissonCountingProcessByLaw (Path × Path)
      (productMeasure incidentRate detectionProbability) := by
  letI : IsProbabilityMeasure
      (observedMeasure incidentRate detectionProbability) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure
      (observedRate_pos hincident hdetection)
  letI : IsProbabilityMeasure
      (exponentialInterarrivalMeasure
        (observedRate incidentRate detectionProbability)) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure
      (observedRate_pos hincident hdetection)
  letI : IsProbabilityMeasure
      (discardedMeasure incidentRate detectionProbability) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure
      (discardedRate_pos hincident hdetection_lt)
  letI : IsProbabilityMeasure
      (productMeasure incidentRate detectionProbability) := by
    unfold productMeasure
    infer_instance
  let H := canonicalForwardHomogeneousPoissonCountingProcessByLaw
    (observedRate_pos hincident hdetection)
  exact pullbackForwardProcess H Prod.fst measurePreserving_fst

/-- The discarded canonical process, lifted to the second product coordinate. -/
def discardedProcess
    (incidentRate detectionProbability : ℝ)
    (hincident : 0 < incidentRate) (hdetection : 0 < detectionProbability)
    (hdetection_lt : detectionProbability < 1) :
    ForwardHomogeneousPoissonCountingProcessByLaw (Path × Path)
      (productMeasure incidentRate detectionProbability) := by
  letI : IsProbabilityMeasure
      (observedMeasure incidentRate detectionProbability) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure
      (observedRate_pos hincident hdetection)
  letI : IsProbabilityMeasure
      (discardedMeasure incidentRate detectionProbability) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure
      (discardedRate_pos hincident hdetection_lt)
  letI : IsProbabilityMeasure
      (exponentialInterarrivalMeasure
        (discardedRate incidentRate detectionProbability)) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure
      (discardedRate_pos hincident hdetection_lt)
  letI : IsProbabilityMeasure
      (productMeasure incidentRate detectionProbability) := by
    unfold productMeasure
    infer_instance
  let H := canonicalForwardHomogeneousPoissonCountingProcessByLaw
    (discardedRate_pos hincident hdetection_lt)
  exact pullbackForwardProcess H Prod.snd measurePreserving_snd

/-- The latent count is the sum of observed and discarded component counts. -/
def latentCount
    (incidentRate detectionProbability : ℝ)
    (hincident : 0 < incidentRate) (hdetection : 0 < detectionProbability)
    (hdetection_lt : detectionProbability < 1) :
    ℝ≥0 → (Path × Path) → ℕ :=
  fun t z =>
    (observedProcess incidentRate detectionProbability hincident hdetection
      hdetection_lt).count t z +
    (discardedProcess incidentRate detectionProbability hincident hdetection
      hdetection_lt).count t z

/-- The product of the observed and discarded Poisson masses is the latent
Poisson mass times the conditional binomial thinning mass. -/
theorem countLikelihood_observed_mul_discarded_eq
    (mean detectionProbability : ℝ) (observed discarded : ℕ) :
    countLikelihood 1 (mean * detectionProbability) observed *
        countLikelihood 1 (mean * (1 - detectionProbability)) discarded =
      countLikelihood 1 mean (observed + discarded) *
        binomialThinningMass detectionProbability
          (observed + discarded) observed := by
  rw [countLikelihood_mul_binomialThinningMass_add_eq]
  simp only [countLikelihood, one_mul]
  have hExp : Real.exp (-mean) =
      Real.exp (-(mean * detectionProbability)) *
        Real.exp (-(mean * (1 - detectionProbability))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hExp]
  ring

/-- Rate/exposure version of the observed/discarded factorization. -/
theorem countLikelihood_split_rate_eq
    (incidentRate exposure detectionProbability : ℝ)
    (observed discarded : ℕ) :
    countLikelihood (incidentRate * detectionProbability) exposure observed *
        countLikelihood (incidentRate * (1 - detectionProbability)) exposure
          discarded =
      countLikelihood incidentRate exposure (observed + discarded) *
        binomialThinningMass detectionProbability
          (observed + discarded) observed := by
  calc
    countLikelihood (incidentRate * detectionProbability) exposure observed *
          countLikelihood (incidentRate * (1 - detectionProbability)) exposure
            discarded =
        countLikelihood 1
              ((incidentRate * exposure) * detectionProbability) observed *
          countLikelihood 1
              ((incidentRate * exposure) * (1 - detectionProbability))
              discarded := by
      have hObservedMean :
          (incidentRate * detectionProbability) * exposure =
            (incidentRate * exposure) * detectionProbability := by
        ring
      have hDiscardedMean :
          (incidentRate * (1 - detectionProbability)) * exposure =
            (incidentRate * exposure) * (1 - detectionProbability) := by
        ring
      simp only [countLikelihood, one_mul, hObservedMean, hDiscardedMean]
    _ = countLikelihood 1 (incidentRate * exposure)
          (observed + discarded) *
        binomialThinningMass detectionProbability
          (observed + discarded) observed :=
      countLikelihood_observed_mul_discarded_eq
        (incidentRate * exposure) detectionProbability observed discarded
    _ = countLikelihood incidentRate exposure (observed + discarded) *
        binomialThinningMass detectionProbability
          (observed + discarded) observed := by
      congr 1
      simp [countLikelihood]

/-- For `0 < p < 1`, the pointwise sum of the independent observed and
discarded canonical processes is a forward homogeneous Poisson process at the
original incident rate. -/
def latentProcess
    (incidentRate detectionProbability : ℝ)
    (hincident : 0 < incidentRate) (hdetection : 0 < detectionProbability)
    (hdetection_lt : detectionProbability < 1) :
    ForwardHomogeneousPoissonCountingProcessByLaw (Path × Path)
      (productMeasure incidentRate detectionProbability) := by
  let hObservedRate := observedRate_pos hincident hdetection
  let hDiscardedRate := discardedRate_pos hincident hdetection_lt
  letI : IsProbabilityMeasure
      (observedMeasure incidentRate detectionProbability) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure hObservedRate
  letI : IsProbabilityMeasure
      (discardedMeasure incidentRate detectionProbability) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure hDiscardedRate
  letI : IsProbabilityMeasure
      (exponentialInterarrivalMeasure
        (observedRate incidentRate detectionProbability)) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure hObservedRate
  letI : IsProbabilityMeasure
      (exponentialInterarrivalMeasure
        (discardedRate incidentRate detectionProbability)) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure hDiscardedRate
  letI : IsProbabilityMeasure
      (productMeasure incidentRate detectionProbability) := by
    unfold productMeasure
    infer_instance
  let HO := canonicalForwardHomogeneousPoissonCountingProcessByLaw hObservedRate
  let HD := canonicalForwardHomogeneousPoissonCountingProcessByLaw hDiscardedRate
  let O := observedProcess incidentRate detectionProbability hincident hdetection
    hdetection_lt
  let D := discardedProcess incidentRate detectionProbability hincident hdetection
    hdetection_lt
  let C : ℝ≥0 → (Path × Path) → ℕ :=
    fun t z => O.count t z + D.count t z
  refine
    { isProbability := inferInstance
      rate := incidentRate
      rate_pos := hincident
      count := C
      count_measurable := ?_
      count_zero_ae := ?_
      count_mono_ae := ?_
      hasIndepIncrements := ?_
      increment_hasLaw := ?_ }
  · intro t
    exact (O.count_measurable t).add (D.count_measurable t)
  · filter_upwards [O.count_zero_ae, D.count_zero_ae] with z hO hD
    change O.count 0 z + D.count 0 z = 0
    simp [hO, hD]
  · filter_upwards [O.count_mono_ae, D.count_mono_ae] with z hO hD
    intro s t hst
    change O.count s z + D.count s z ≤ O.count t z + D.count t z
    exact Nat.add_le_add (hO hst) (hD hst)
  · intro n t ht
    let X : Fin n → Path → ℕ := fun i ω =>
      HO.count (t i.succ) ω - HO.count (t i.castSucc) ω
    let Y : Fin n → Path → ℕ := fun i ω =>
      HD.count (t i.succ) ω - HD.count (t i.castSucc) ω
    have hX : iIndepFun X
        (observedMeasure incidentRate detectionProbability) := by
      simpa [X, HO, observedMeasure] using HO.hasIndepIncrements n t ht
    have hY : iIndepFun Y
        (discardedMeasure incidentRate detectionProbability) := by
      simpa [Y, HD, discardedMeasure] using HD.hasIndepIncrements n t ht
    have mX : ∀ i, Measurable (X i) := fun i =>
      (HO.count_measurable (t i.succ)).sub
        (HO.count_measurable (t i.castSucc))
    have mY : ∀ i, Measurable (Y i) := fun i =>
      (HD.count_measurable (t i.succ)).sub
        (HD.count_measurable (t i.castSucc))
    have hPair : iIndepFun (fun i z => (X i z.1, Y i z.2))
        (productMeasure incidentRate detectionProbability) := by
      simpa [productMeasure] using iIndepFun_pair_prod hX hY mX mY
    have hPairOD : iIndepFun
        (fun (i : Fin n) z =>
          (O.count (t i.succ) z - O.count (t i.castSucc) z,
            D.count (t i.succ) z - D.count (t i.castSucc) z))
        (productMeasure incidentRate detectionProbability) := by
      simpa [X, Y, O, D, observedProcess, discardedProcess,
        pullbackForwardProcess, Function.comp_def] using hPair
    have hSum : iIndepFun
        (fun (i : Fin n) z =>
          (O.count (t i.succ) z - O.count (t i.castSucc) z) +
            (D.count (t i.succ) z - D.count (t i.castSucc) z))
        (productMeasure incidentRate detectionProbability) := by
      simpa [Function.comp_def] using hPairOD.comp
        (fun (_ : Fin n) => fun q : ℕ × ℕ => q.1 + q.2)
        (fun (_ : Fin n) => measurable_fst.add measurable_snd)
    have hEq : ∀ i : Fin n,
        (fun z =>
          (O.count (t i.succ) z - O.count (t i.castSucc) z) +
            (D.count (t i.succ) z - D.count (t i.castSucc) z)) =ᵐ[
          productMeasure incidentRate detectionProbability]
        (fun z => C (t i.succ) z - C (t i.castSucc) z) := by
      intro i
      filter_upwards [O.count_mono_ae, D.count_mono_ae] with z hO hD
      simp only [C]
      change
        (O.count (t i.succ) z - O.count (t i.castSucc) z) +
            (D.count (t i.succ) z - D.count (t i.castSucc) z) =
          (O.count (t i.succ) z + D.count (t i.succ) z) -
            (O.count (t i.castSucc) z + D.count (t i.castSucc) z)
      have hOt := hO (ht (Fin.castSucc_le_succ i))
      have hDt := hD (ht (Fin.castSucc_le_succ i))
      change O.count (t i.castSucc) z ≤ O.count (t i.succ) z at hOt
      change D.count (t i.castSucc) z ≤ D.count (t i.succ) z at hDt
      omega
    exact (iIndepFun_congr hEq).mp hSum
  · intro s t hst
    let exposure : ℝ := (t : ℝ) - (s : ℝ)
    have hexposure : 0 ≤ exposure :=
      sub_nonneg.mpr (NNReal.coe_le_coe.mpr hst)
    let X : Path × Path → ℕ := O.intervalCount s t
    let Y : Path × Path → ℕ := D.intervalCount s t
    let S : Path × Path → ℕ := fun z => X z + Y z
    have mX : Measurable X :=
      O.measurable_intervalCount s t
    have mY : Measurable Y :=
      D.measurable_intervalCount s t
    have mS : Measurable S := mX.add mY
    have hIndep : IndepFun X Y
        (productMeasure incidentRate detectionProbability) := by
      change
        (fun z : Path × Path =>
            HO.intervalCount s t z.1) ⟂ᵢ[
              productMeasure incidentRate detectionProbability]
          (fun z : Path × Path => HD.intervalCount s t z.2)
      simpa [productMeasure] using indepFun_prod
        (HO.measurable_intervalCount s t)
        (HD.measurable_intervalCount s t)
    have hJoint : ∀ a b : ℕ,
        (productMeasure incidentRate detectionProbability).real
            ({z | X z = a} ∩ {z | Y z = b}) =
          countLikelihood 1
              (observedRate incidentRate detectionProbability * exposure) a *
            countLikelihood 1
              (discardedRate incidentRate detectionProbability * exposure) b := by
      intro a b
      simp only [measureReal_def]
      change
        ((productMeasure incidentRate detectionProbability)
          (X ⁻¹' {a} ∩ Y ⁻¹' {b})).toReal = _
      rw [hIndep.measure_inter_preimage_eq_mul {a} {b}
        (measurableSet_singleton a) (measurableSet_singleton b),
        ENNReal.toReal_mul]
      change
        (productMeasure incidentRate detectionProbability).real
              {z | X z = a} *
            (productMeasure incidentRate detectionProbability).real
              {z | Y z = b} = _
      rw [O.intervalCount_prob hst a, D.intervalCount_prob hst b]
      change
        countLikelihood (observedRate incidentRate detectionProbability)
              exposure a *
            countLikelihood (discardedRate incidentRate detectionProbability)
              exposure b = _
      simp only [countLikelihood, one_mul]
    have hSumMass (n : ℕ) :
        (productMeasure incidentRate detectionProbability).real
            {z | S z = n} =
          countLikelihood incidentRate exposure n := by
      have h := pair_count_sum_real_eq_countLikelihood_add
        mX.aemeasurable mY.aemeasurable hJoint n
      change (productMeasure incidentRate detectionProbability).real
          {z | S z = n} = _
      calc
        (productMeasure incidentRate detectionProbability).real
            {z | S z = n} =
            countLikelihood 1
              (observedRate incidentRate detectionProbability * exposure +
                discardedRate incidentRate detectionProbability * exposure) n := h
        _ = countLikelihood incidentRate exposure n := by
          have hmean :
              observedRate incidentRate detectionProbability * exposure +
                  discardedRate incidentRate detectionProbability * exposure =
                incidentRate * exposure := by
            simp only [observedRate, discardedRate]
            ring
          simp only [countLikelihood, one_mul, hmean]
    have hSumLaw : HasLaw S
        (poissonMeasure
          (rateExposureParam incidentRate exposure
            (mul_nonneg hincident.le hexposure)))
        (productMeasure incidentRate detectionProbability) := by
      refine ⟨mS.aemeasurable, ?_⟩
      apply (MeasureTheory.ext_iff_measureReal_singleton).mpr
      intro n
      calc
        (Measure.map S
            (productMeasure incidentRate detectionProbability)).real {n} =
            (productMeasure incidentRate detectionProbability).real
              {z | S z = n} := by
          simp only [measureReal_def]
          rw [Measure.map_apply mS (measurableSet_singleton n)]
          rfl
        _ = countLikelihood incidentRate exposure n := hSumMass n
        _ = (poissonMeasure
              (rateExposureParam incidentRate exposure
                (mul_nonneg hincident.le hexposure))).real {n} :=
          countLikelihood_eq_poissonMeasure_real_singleton
            (mul_nonneg hincident.le hexposure) n
    have hActualEq :
        (fun z => C t z - C s z) =ᵐ[
          productMeasure incidentRate detectionProbability] S := by
      filter_upwards [O.count_mono_ae, D.count_mono_ae] with z hO hD
      simp only [C]
      change
        (O.count t z + D.count t z) - (O.count s z + D.count s z) =
          (O.count t z - O.count s z) + (D.count t z - D.count s z)
      have hOt := hO hst
      have hDt := hD hst
      change O.count s z ≤ O.count t z at hOt
      change D.count s z ≤ D.count t z at hDt
      omega
    simpa [exposure] using hSumLaw.congr hActualEq

@[simp] theorem latentProcess_rate
    (incidentRate detectionProbability : ℝ)
    (hincident : 0 < incidentRate) (hdetection : 0 < detectionProbability)
    (hdetection_lt : detectionProbability < 1) :
    (latentProcess incidentRate detectionProbability hincident hdetection
      hdetection_lt).rate = incidentRate := rfl

@[simp] theorem latentProcess_count
    (incidentRate detectionProbability : ℝ)
    (hincident : 0 < incidentRate) (hdetection : 0 < detectionProbability)
    (hdetection_lt : detectionProbability < 1)
    (t : ℝ≥0) (z : Path × Path) :
    (latentProcess incidentRate detectionProbability hincident hdetection
        hdetection_lt).count t z =
      (observedProcess incidentRate detectionProbability hincident hdetection
          hdetection_lt).count t z +
        (discardedProcess incidentRate detectionProbability hincident hdetection
          hdetection_lt).count t z := rfl

@[simp] theorem observedProcess_rate
    (incidentRate detectionProbability : ℝ)
    (hincident : 0 < incidentRate) (hdetection : 0 < detectionProbability)
    (hdetection_lt : detectionProbability < 1) :
    (observedProcess incidentRate detectionProbability hincident hdetection
      hdetection_lt).rate = incidentRate * detectionProbability := rfl

@[simp] theorem discardedProcess_rate
    (incidentRate detectionProbability : ℝ)
    (hincident : 0 < incidentRate) (hdetection : 0 < detectionProbability)
    (hdetection_lt : detectionProbability < 1) :
    (discardedProcess incidentRate detectionProbability hincident hdetection
      hdetection_lt).rate = incidentRate * (1 - detectionProbability) := rfl

/--
Source-faithful process model for independent incident reporting.  The latent
path is already a homogeneous Poisson process.  The observed path is only
assumed measurable, zero based, and monotone.  Independence of observed
increments is *not* a field: it is derived from independence of the marked
latent/observed increment pairs.  The joint interval law states the actual
conditional binomial marking identity.
-/
structure MarkedPoissonReportingProcess
    (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) where
  /-- Latent incident arrivals. -/
  latentProcess : ForwardHomogeneousPoissonCountingProcessByLaw Ω P
  /-- Common independent reporting probability. -/
  detectionProbability : ℝ
  detectionProbability_nonnegative : 0 ≤ detectionProbability
  detectionProbability_le_one : detectionProbability ≤ 1
  /-- Count of reported incidents. -/
  observedCount : ℝ≥0 → Ω → ℕ
  observedCount_measurable : ∀ t, Measurable (observedCount t)
  observedCount_zero_ae : ∀ᵐ ω ∂P, observedCount 0 ω = 0
  observedCount_mono_ae : ∀ᵐ ω ∂P, Monotone fun t => observedCount t ω
  /-- Marked increment pairs on disjoint ordered intervals are independent. -/
  intervalPairs_independent :
    ∀ (n : ℕ) (t : Fin (n + 1) → ℝ≥0) (_ht : Monotone t),
      iIndepFun
        (fun (i : Fin n) ω =>
          (latentProcess.count (t i.succ) ω -
              latentProcess.count (t i.castSucc) ω,
            observedCount (t i.succ) ω -
              observedCount (t i.castSucc) ω)) P
  /-- Exact joint PMF: latent Poisson count times conditional Binomial marks. -/
  interval_joint_mass :
    ∀ {s t : ℝ≥0} (_hst : s ≤ t) (latent observed : ℕ),
      P.real
          ({ω : Ω |
              latentProcess.intervalCount s t ω = latent} ∩
            {ω : Ω |
              observedCount t ω - observedCount s ω = observed}) =
        countLikelihood latentProcess.rate ((t : ℝ) - (s : ℝ)) latent *
          binomialThinningMass detectionProbability latent observed

namespace MarkedPoissonReportingProcess

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

private theorem canonicalSplit_intervalPairs_independent
    (incidentRate detectionProbability : ℝ)
    (hincident : 0 < incidentRate) (hdetection : 0 < detectionProbability)
    (hdetection_lt : detectionProbability < 1) :
    ∀ (n : ℕ) (t : Fin (n + 1) → ℝ≥0) (_ht : Monotone t),
      iIndepFun
        (fun (i : Fin n) z =>
          ((Lemma1MarkedPoissonThinning.latentProcess incidentRate
                detectionProbability hincident hdetection
                hdetection_lt).count (t i.succ) z -
              (Lemma1MarkedPoissonThinning.latentProcess incidentRate
                detectionProbability hincident hdetection
                hdetection_lt).count (t i.castSucc) z,
            (observedProcess incidentRate detectionProbability hincident hdetection
                hdetection_lt).count (t i.succ) z -
              (observedProcess incidentRate detectionProbability hincident hdetection
                hdetection_lt).count (t i.castSucc) z))
        (productMeasure incidentRate detectionProbability) := by
  let hObservedRate := observedRate_pos hincident hdetection
  let hDiscardedRate := discardedRate_pos hincident hdetection_lt
  letI : IsProbabilityMeasure
      (observedMeasure incidentRate detectionProbability) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure hObservedRate
  letI : IsProbabilityMeasure
      (discardedMeasure incidentRate detectionProbability) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure hDiscardedRate
  letI : IsProbabilityMeasure
      (exponentialInterarrivalMeasure
        (observedRate incidentRate detectionProbability)) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure hObservedRate
  letI : IsProbabilityMeasure
      (exponentialInterarrivalMeasure
        (discardedRate incidentRate detectionProbability)) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure hDiscardedRate
  letI : IsProbabilityMeasure
      (productMeasure incidentRate detectionProbability) := by
    unfold productMeasure
    infer_instance
  let HO := canonicalForwardHomogeneousPoissonCountingProcessByLaw hObservedRate
  let HD := canonicalForwardHomogeneousPoissonCountingProcessByLaw hDiscardedRate
  let O := observedProcess incidentRate detectionProbability hincident hdetection
    hdetection_lt
  let D := discardedProcess incidentRate detectionProbability hincident hdetection
    hdetection_lt
  let L := Lemma1MarkedPoissonThinning.latentProcess incidentRate
    detectionProbability hincident hdetection hdetection_lt
  intro n t ht
  let X : Fin n → Path → ℕ := fun i ω =>
    HO.count (t i.succ) ω - HO.count (t i.castSucc) ω
  let Y : Fin n → Path → ℕ := fun i ω =>
    HD.count (t i.succ) ω - HD.count (t i.castSucc) ω
  have hX : iIndepFun X
      (observedMeasure incidentRate detectionProbability) := by
    simpa [X, HO, observedMeasure] using HO.hasIndepIncrements n t ht
  have hY : iIndepFun Y
      (discardedMeasure incidentRate detectionProbability) := by
    simpa [Y, HD, discardedMeasure] using HD.hasIndepIncrements n t ht
  have mX : ∀ i, Measurable (X i) := fun i =>
    (HO.count_measurable (t i.succ)).sub
      (HO.count_measurable (t i.castSucc))
  have mY : ∀ i, Measurable (Y i) := fun i =>
    (HD.count_measurable (t i.succ)).sub
      (HD.count_measurable (t i.castSucc))
  have hPair : iIndepFun (fun i z => (X i z.1, Y i z.2))
      (productMeasure incidentRate detectionProbability) := by
    simpa [productMeasure] using iIndepFun_pair_prod hX hY mX mY
  have hPairOD : iIndepFun
      (fun (i : Fin n) z =>
        (O.count (t i.succ) z - O.count (t i.castSucc) z,
          D.count (t i.succ) z - D.count (t i.castSucc) z))
      (productMeasure incidentRate detectionProbability) := by
    simpa [X, Y, O, D, observedProcess, discardedProcess,
      pullbackForwardProcess, Function.comp_def] using hPair
  have hMarked : iIndepFun
      (fun (i : Fin n) z =>
        ((O.count (t i.succ) z - O.count (t i.castSucc) z) +
            (D.count (t i.succ) z - D.count (t i.castSucc) z),
          O.count (t i.succ) z - O.count (t i.castSucc) z))
      (productMeasure incidentRate detectionProbability) := by
    simpa [Function.comp_def] using hPairOD.comp
      (fun (_ : Fin n) => fun q : ℕ × ℕ => (q.1 + q.2, q.1))
      (fun (_ : Fin n) =>
        (measurable_fst.add measurable_snd).prodMk measurable_fst)
  have hEq : ∀ i : Fin n,
      (fun z =>
        ((O.count (t i.succ) z - O.count (t i.castSucc) z) +
            (D.count (t i.succ) z - D.count (t i.castSucc) z),
          O.count (t i.succ) z - O.count (t i.castSucc) z)) =ᵐ[
        productMeasure incidentRate detectionProbability]
      (fun z =>
        (L.count (t i.succ) z - L.count (t i.castSucc) z,
          O.count (t i.succ) z - O.count (t i.castSucc) z)) := by
    intro i
    filter_upwards [O.count_mono_ae, D.count_mono_ae] with z hO hD
    apply Prod.ext
    · simp only [L, latentProcess_count]
      change
        (O.count (t i.succ) z - O.count (t i.castSucc) z) +
            (D.count (t i.succ) z - D.count (t i.castSucc) z) =
          (O.count (t i.succ) z + D.count (t i.succ) z) -
            (O.count (t i.castSucc) z + D.count (t i.castSucc) z)
      have hOt := hO (ht (Fin.castSucc_le_succ i))
      have hDt := hD (ht (Fin.castSucc_le_succ i))
      change O.count (t i.castSucc) z ≤ O.count (t i.succ) z at hOt
      change D.count (t i.castSucc) z ≤ D.count (t i.succ) z at hDt
      omega
    · rfl
  exact (iIndepFun_congr hEq).mp hMarked

private theorem canonicalSplit_interval_joint_mass
    (incidentRate detectionProbability : ℝ)
    (hincident : 0 < incidentRate) (hdetection : 0 < detectionProbability)
    (hdetection_lt : detectionProbability < 1) :
    ∀ {s t : ℝ≥0} (_hst : s ≤ t) (latent observed : ℕ),
      (productMeasure incidentRate detectionProbability).real
          ({z : Path × Path |
              (Lemma1MarkedPoissonThinning.latentProcess incidentRate
                detectionProbability hincident hdetection hdetection_lt).intervalCount
                  s t z = latent} ∩
            {z : Path × Path |
              (observedProcess incidentRate detectionProbability hincident hdetection
                  hdetection_lt).count t z -
                (observedProcess incidentRate detectionProbability hincident hdetection
                  hdetection_lt).count s z = observed}) =
        countLikelihood incidentRate ((t : ℝ) - (s : ℝ)) latent *
          binomialThinningMass detectionProbability latent observed := by
  let hObservedRate := observedRate_pos hincident hdetection
  let hDiscardedRate := discardedRate_pos hincident hdetection_lt
  letI : IsProbabilityMeasure
      (observedMeasure incidentRate detectionProbability) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure hObservedRate
  letI : IsProbabilityMeasure
      (discardedMeasure incidentRate detectionProbability) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure hDiscardedRate
  letI : IsProbabilityMeasure
      (exponentialInterarrivalMeasure
        (observedRate incidentRate detectionProbability)) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure hObservedRate
  letI : IsProbabilityMeasure
      (exponentialInterarrivalMeasure
        (discardedRate incidentRate detectionProbability)) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure hDiscardedRate
  letI : IsProbabilityMeasure
      (productMeasure incidentRate detectionProbability) := by
    unfold productMeasure
    infer_instance
  let HO := canonicalForwardHomogeneousPoissonCountingProcessByLaw hObservedRate
  let HD := canonicalForwardHomogeneousPoissonCountingProcessByLaw hDiscardedRate
  let O := observedProcess incidentRate detectionProbability hincident hdetection
    hdetection_lt
  let D := discardedProcess incidentRate detectionProbability hincident hdetection
    hdetection_lt
  let L := Lemma1MarkedPoissonThinning.latentProcess incidentRate
    detectionProbability hincident hdetection hdetection_lt
  intro s t hst latent observed
  let exposure : ℝ := (t : ℝ) - (s : ℝ)
  let X : Path × Path → ℕ := O.intervalCount s t
  let Y : Path × Path → ℕ := D.intervalCount s t
  let Z : Path × Path → ℕ := L.intervalCount s t
  have hIndep : IndepFun X Y
      (productMeasure incidentRate detectionProbability) := by
    change
      (fun z : Path × Path => HO.intervalCount s t z.1) ⟂ᵢ[
          productMeasure incidentRate detectionProbability]
        (fun z : Path × Path => HD.intervalCount s t z.2)
    simpa [productMeasure] using indepFun_prod
      (HO.measurable_intervalCount s t)
      (HD.measurable_intervalCount s t)
  have hJointXY (a b : ℕ) :
      (productMeasure incidentRate detectionProbability).real
          {z | X z = a ∧ Y z = b} =
        countLikelihood (incidentRate * detectionProbability) exposure a *
          countLikelihood (incidentRate * (1 - detectionProbability)) exposure b := by
    simp only [measureReal_def]
    change
      ((productMeasure incidentRate detectionProbability)
        (X ⁻¹' {a} ∩ Y ⁻¹' {b})).toReal = _
    rw [hIndep.measure_inter_preimage_eq_mul {a} {b}
      (measurableSet_singleton a) (measurableSet_singleton b),
      ENNReal.toReal_mul]
    change
      (productMeasure incidentRate detectionProbability).real
            {z | X z = a} *
          (productMeasure incidentRate detectionProbability).real
            {z | Y z = b} = _
    rw [O.intervalCount_prob hst a, D.intervalCount_prob hst b]
    simp [O, D, exposure]
  have hZeq : Z =ᵐ[productMeasure incidentRate detectionProbability]
      (fun z => X z + Y z) := by
    filter_upwards [O.count_mono_ae, D.count_mono_ae] with z hO hD
    change L.count t z - L.count s z =
      (O.count t z - O.count s z) + (D.count t z - D.count s z)
    simp only [L, latentProcess_count]
    change
      (O.count t z + D.count t z) - (O.count s z + D.count s z) =
        (O.count t z - O.count s z) + (D.count t z - D.count s z)
    have hOt := hO hst
    have hDt := hD hst
    change O.count s z ≤ O.count t z at hOt
    change D.count s z ≤ D.count t z at hDt
    omega
  have hEvent :
      (fun z : Path × Path => Z z = latent ∧ X z = observed) =ᵐ[
        productMeasure incidentRate detectionProbability]
      (fun z : Path × Path =>
        X z + Y z = latent ∧ X z = observed) := by
    filter_upwards [hZeq] with z hz
    rw [hz]
  have hEventSet :
      ({z : Path × Path | Z z = latent ∧ X z = observed} :
        Set (Path × Path)) =ᵐ[
          productMeasure incidentRate detectionProbability]
      ({z : Path × Path |
        X z + Y z = latent ∧ X z = observed} : Set (Path × Path)) := by
    filter_upwards [hEvent] with z hz
    exact hz
  change (productMeasure incidentRate detectionProbability).real
      {z : Path × Path | Z z = latent ∧ X z = observed} = _
  rw [measureReal_congr hEventSet]
  by_cases hle : observed ≤ latent
  · have hset :
        {z : Path × Path |
            X z + Y z = latent ∧ X z = observed} =
          {z : Path × Path |
            X z = observed ∧ Y z = latent - observed} := by
      ext z
      change (X z + Y z = latent ∧ X z = observed) ↔
        (X z = observed ∧ Y z = latent - observed)
      omega
    rw [hset, hJointXY observed (latent - observed)]
    simpa [Nat.add_sub_of_le hle] using
      countLikelihood_split_rate_eq incidentRate exposure detectionProbability
        observed (latent - observed)
  · have hlt : latent < observed := Nat.lt_of_not_ge hle
    have hset :
        {z : Path × Path |
            X z + Y z = latent ∧ X z = observed} = ∅ := by
      ext z
      change (X z + Y z = latent ∧ X z = observed) ↔ False
      constructor
      · rintro ⟨hsum, hx⟩
        have hle' : observed ≤ latent := by
          rw [← hsum, ← hx]
          exact Nat.le_add_right _ _
        exact (Nat.not_le_of_lt hlt) hle'
      · exact False.elim
    rw [hset]
    simp [binomialThinningMass_eq_zero_of_lt hlt]

/-- Canonical observed/discarded split construction for `0 < p < 1`. -/
def ofCanonicalSplit
    (incidentRate detectionProbability : ℝ)
    (hincident : 0 < incidentRate) (hdetection : 0 < detectionProbability)
    (hdetection_lt : detectionProbability < 1) :
    MarkedPoissonReportingProcess (Path × Path)
      (productMeasure incidentRate detectionProbability) where
  latentProcess := Lemma1MarkedPoissonThinning.latentProcess incidentRate
    detectionProbability hincident hdetection hdetection_lt
  detectionProbability := detectionProbability
  detectionProbability_nonnegative := hdetection.le
  detectionProbability_le_one := hdetection_lt.le
  observedCount := (observedProcess incidentRate detectionProbability hincident
    hdetection hdetection_lt).count
  observedCount_measurable :=
    (observedProcess incidentRate detectionProbability hincident hdetection
      hdetection_lt).count_measurable
  observedCount_zero_ae :=
    (observedProcess incidentRate detectionProbability hincident hdetection
      hdetection_lt).count_zero_ae
  observedCount_mono_ae :=
    (observedProcess incidentRate detectionProbability hincident hdetection
      hdetection_lt).count_mono_ae
  intervalPairs_independent :=
    canonicalSplit_intervalPairs_independent incidentRate detectionProbability
      hincident hdetection hdetection_lt
  interval_joint_mass := by
    intro s t hst latent observed
    simpa using canonicalSplit_interval_joint_mass incidentRate
      detectionProbability hincident hdetection hdetection_lt hst latent observed

private theorem binomialThinningMass_one
    (trials kept : ℕ) :
    binomialThinningMass 1 trials kept = if kept = trials then 1 else 0 := by
  by_cases hle : kept ≤ trials
  · rw [binomialThinningMass_eq_of_le hle]
    by_cases heq : kept = trials
    · subst kept
      simp
    · have hlt : kept < trials := lt_of_le_of_ne hle heq
      have hpos : 0 < trials - kept := Nat.sub_pos_of_lt hlt
      simp [heq, hpos.ne']
  · have hlt : trials < kept := Nat.lt_of_not_ge hle
    rw [binomialThinningMass_eq_zero_of_lt hlt]
    simp [Nat.ne_of_gt hlt]

/-- Endpoint construction for perfect detection: observed and latent paths are
the same canonical Poisson process. -/
def ofDetectionOne
    (incidentRate : ℝ) (hincident : 0 < incidentRate) :
    MarkedPoissonReportingProcess Path
      (exponentialInterarrivalMeasure incidentRate) := by
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure incidentRate) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure hincident
  let H := canonicalForwardHomogeneousPoissonCountingProcessByLaw hincident
  refine
    { latentProcess := H
      detectionProbability := 1
      detectionProbability_nonnegative := zero_le_one
      detectionProbability_le_one := le_rfl
      observedCount := H.count
      observedCount_measurable := H.count_measurable
      observedCount_zero_ae := H.count_zero_ae
      observedCount_mono_ae := H.count_mono_ae
      intervalPairs_independent := ?_
      interval_joint_mass := ?_ }
  · intro n t ht
    have hInc := H.hasIndepIncrements n t ht
    simpa [Function.comp_def] using hInc.comp
      (fun (_ : Fin n) (x : ℕ) => (x, x))
      (fun (_ : Fin n) => measurable_id.prodMk measurable_id)
  · intro s t hst latent observed
    let X : Path → ℕ := H.intervalCount s t
    change (exponentialInterarrivalMeasure incidentRate).real
        ({ω | X ω = latent} ∩ {ω | X ω = observed}) =
      countLikelihood incidentRate ((t : ℝ) - (s : ℝ)) latent *
        binomialThinningMass 1 latent observed
    by_cases heq : observed = latent
    · subst observed
      have hrate : H.rate = incidentRate := rfl
      have hset : ({ω | X ω = latent} ∩ {ω | X ω = latent}) =
          {ω | X ω = latent} := by
        ext ω
        simp
      rw [hset, H.intervalCount_prob hst latent, hrate,
        binomialThinningMass_one]
      simp
    · have hset :
          ({ω | X ω = latent} ∩ {ω | X ω = observed}) = ∅ := by
        ext ω
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq,
          Set.mem_empty_iff_false]
        constructor
        · rintro ⟨hlatent, hobserved⟩
          exact heq (hobserved.symm.trans hlatent)
        · exact False.elim
      rw [hset]
      simp [binomialThinningMass_one, heq]

/-- A source model exists for every positive incident rate and every detection
probability in `(0,1]`; the endpoint uses the identity marking construction. -/
theorem exists_markedPoissonReportingProcess
    (incidentRate detectionProbability : ℝ)
    (hincident : 0 < incidentRate) (hdetection : 0 < detectionProbability)
    (hdetection_le : detectionProbability ≤ 1) :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : Measure Ω)
        (H : @MarkedPoissonReportingProcess Ω mΩ P),
      H.latentProcess.rate = incidentRate ∧
        H.detectionProbability = detectionProbability := by
  by_cases hdetection_lt : detectionProbability < 1
  · let H := ofCanonicalSplit incidentRate detectionProbability hincident
      hdetection hdetection_lt
    exact ⟨Path × Path, inferInstance,
      productMeasure incidentRate detectionProbability, H, rfl, rfl⟩
  · have hone : detectionProbability = 1 := by
      linarith
    subst detectionProbability
    let H := ofDetectionOne incidentRate hincident
    exact ⟨Path, inferInstance, exponentialInterarrivalMeasure incidentRate,
      H, rfl, rfl⟩

/-- The reported rate is nonnegative, including the source-valid zero-
detection endpoint. -/
theorem observedRate_nonnegative (H : MarkedPoissonReportingProcess Ω P) :
    0 ≤ H.latentProcess.rate * H.detectionProbability :=
  mul_nonneg H.latentProcess.rate_pos.le H.detectionProbability_nonnegative

/-- In the positive-detection branch, the reported rate is strictly positive. -/
theorem observedRate_pos (H : MarkedPoissonReportingProcess Ω P)
    (hdetection : 0 < H.detectionProbability) :
    0 < H.latentProcess.rate * H.detectionProbability :=
  mul_pos H.latentProcess.rate_pos hdetection

/-- Observed increments are derived to be independent by projecting the
independent marked increment pairs; this is not assumed in the model. -/
theorem observedCount_hasIndepIncrements
    (H : MarkedPoissonReportingProcess Ω P) :
    HasIndepIncrements H.observedCount P := by
  intro n t ht
  have hPair := H.intervalPairs_independent n t ht
  have hObserved := hPair.comp
    (fun (_ : Fin n) (q : ℕ × ℕ) => q.2)
    (fun (_ : Fin n) => measurable_snd)
  simpa [Function.comp_def] using hObserved

/-- Marginalizing the exact joint law over the latent count gives the Poisson
count/binomial-thinning mixture for the observed interval count. -/
theorem observedIntervalCount_mass_eq_binomial_mixture
    (H : MarkedPoissonReportingProcess Ω P)
    {s t : ℝ≥0} (hst : s ≤ t) (observed : ℕ) :
    P.real
        {ω : Ω |
          H.observedCount t ω - H.observedCount s ω = observed} =
      ∑' latent : ℕ,
        countLikelihood H.latentProcess.rate
            ((t : ℝ) - (s : ℝ)) latent *
          binomialThinningMass H.detectionProbability latent observed := by
  letI : IsProbabilityMeasure P := H.latentProcess.isProbability
  let L : Ω → ℕ := H.latentProcess.intervalCount s t
  let O : Ω → ℕ := fun ω =>
    H.observedCount t ω - H.observedCount s ω
  let A : ℕ → Set Ω := fun latent =>
    {ω | L ω = latent} ∩ {ω | O ω = observed}
  have mL : Measurable L := H.latentProcess.measurable_intervalCount s t
  have mO : Measurable O :=
    (H.observedCount_measurable t).sub (H.observedCount_measurable s)
  have hAmeas : ∀ latent, MeasurableSet (A latent) := by
    intro latent
    exact (mL (measurableSet_singleton latent)).inter
      (mO (measurableSet_singleton observed))
  have hAdis : Pairwise (fun a b => Disjoint (A a) (A b)) := by
    intro a b hab
    rw [Set.disjoint_left]
    intro ω ha hb
    exact hab (ha.1.symm.trans hb.1)
  have hUnion : {ω | O ω = observed} = ⋃ latent : ℕ, A latent := by
    ext ω
    constructor
    · intro hO
      exact Set.mem_iUnion.mpr ⟨L ω, rfl, hO⟩
    · intro h
      rcases Set.mem_iUnion.mp h with ⟨latent, _hL, hO⟩
      exact hO
  change P.real {ω | O ω = observed} = _
  rw [hUnion]
  calc
    P.real (⋃ latent : ℕ, A latent) =
        ∑' latent : ℕ, P.real (A latent) := by
      simp only [Measure.real, measure_iUnion hAdis hAmeas]
      exact ENNReal.tsum_toReal_eq (fun latent => measure_ne_top P (A latent))
    _ = ∑' latent : ℕ,
        countLikelihood H.latentProcess.rate
            ((t : ℝ) - (s : ℝ)) latent *
          binomialThinningMass H.detectionProbability latent observed := by
      apply tsum_congr
      intro latent
      exact H.interval_joint_mass hst latent observed

/-- The observed interval marginal is Poisson with the thinned rate. -/
theorem observedIntervalCount_mass_eq_countLikelihood
    (H : MarkedPoissonReportingProcess Ω P)
    {s t : ℝ≥0} (hst : s ≤ t) (observed : ℕ) :
    P.real
        {ω : Ω |
          H.observedCount t ω - H.observedCount s ω = observed} =
      countLikelihood
        (H.latentProcess.rate * H.detectionProbability)
        ((t : ℝ) - (s : ℝ)) observed := by
  rw [H.observedIntervalCount_mass_eq_binomial_mixture hst observed]
  calc
    (∑' latent : ℕ,
        countLikelihood H.latentProcess.rate
            ((t : ℝ) - (s : ℝ)) latent *
          binomialThinningMass H.detectionProbability latent observed) =
        ∑' latent : ℕ,
          countLikelihood 1
              (H.latentProcess.rate * ((t : ℝ) - (s : ℝ))) latent *
            binomialThinningMass H.detectionProbability latent observed := by
      congr 1
      funext latent
      congr 1
      simp [countLikelihood]
    _ = countLikelihood 1
          ((H.latentProcess.rate * ((t : ℝ) - (s : ℝ))) *
            H.detectionProbability) observed :=
      tsum_countLikelihood_mul_binomialThinningMass
        (H.latentProcess.rate * ((t : ℝ) - (s : ℝ)))
        H.detectionProbability observed
    _ = countLikelihood
          (H.latentProcess.rate * H.detectionProbability)
          ((t : ℝ) - (s : ℝ)) observed := by
      have hmean :
          (H.latentProcess.rate * ((t : ℝ) - (s : ℝ))) *
              H.detectionProbability =
            (H.latentProcess.rate * H.detectionProbability) *
              ((t : ℝ) - (s : ℝ)) := by
        ring
      simp only [countLikelihood, one_mul, hmean]

/-- Each observed interval count has the Poisson law at the thinned rate. -/
theorem observedIncrement_hasLaw
    (H : MarkedPoissonReportingProcess Ω P)
    {s t : ℝ≥0} (hst : s ≤ t) :
    HasLaw
      (fun ω : Ω => H.observedCount t ω - H.observedCount s ω)
      (poissonMeasure
        (rateExposureParam
          (H.latentProcess.rate * H.detectionProbability)
          ((t : ℝ) - (s : ℝ))
          (mul_nonneg H.observedRate_nonnegative
            (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hst))))) P := by
  let increment : Ω → ℕ := fun ω =>
    H.observedCount t ω - H.observedCount s ω
  have mincrement : Measurable increment :=
    (H.observedCount_measurable t).sub (H.observedCount_measurable s)
  refine ⟨mincrement.aemeasurable, ?_⟩
  letI : IsProbabilityMeasure P := H.latentProcess.isProbability
  apply (MeasureTheory.ext_iff_measureReal_singleton).mpr
  intro observed
  calc
    (Measure.map increment P).real {observed} =
        P.real {ω : Ω | increment ω = observed} := by
      simp only [measureReal_def]
      rw [Measure.map_apply mincrement (measurableSet_singleton observed)]
      rfl
    _ = countLikelihood
          (H.latentProcess.rate * H.detectionProbability)
          ((t : ℝ) - (s : ℝ)) observed :=
      H.observedIntervalCount_mass_eq_countLikelihood hst observed
    _ = (poissonMeasure
          (rateExposureParam
            (H.latentProcess.rate * H.detectionProbability)
            ((t : ℝ) - (s : ℝ))
            (mul_nonneg H.observedRate_nonnegative
              (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hst))))).real
          {observed} :=
      countLikelihood_eq_poissonMeasure_real_singleton
        (mul_nonneg H.observedRate_nonnegative
          (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hst))) observed

/-- The derived observed process at rate `latentRate * p`. -/
def toObservedForwardPoissonProcess
    (H : MarkedPoissonReportingProcess Ω P)
    (hdetection : 0 < H.detectionProbability) :
    ForwardHomogeneousPoissonCountingProcessByLaw Ω P where
  isProbability := H.latentProcess.isProbability
  rate := H.latentProcess.rate * H.detectionProbability
  rate_pos := H.observedRate_pos hdetection
  count := H.observedCount
  count_measurable := H.observedCount_measurable
  count_zero_ae := H.observedCount_zero_ae
  count_mono_ae := H.observedCount_mono_ae
  hasIndepIncrements := H.observedCount_hasIndepIncrements
  increment_hasLaw := by
    intro s t hst
    exact H.observedIncrement_hasLaw hst

/-- Paper-facing Lemma 1 conclusion derived from latent Poisson arrivals and
independent per-incident reporting. -/
theorem observed_process_is_homogeneous_poisson
    (H : MarkedPoissonReportingProcess Ω P)
    (hdetection : 0 < H.detectionProbability) :
    ∃ observedProcess : ForwardHomogeneousPoissonCountingProcessByLaw Ω P,
      observedProcess.count = H.observedCount ∧
      observedProcess.rate =
        H.latentProcess.rate * H.detectionProbability := by
  refine ⟨H.toObservedForwardPoissonProcess hdetection, ?_, ?_⟩
  · rfl
  · rfl

/-- The source-valid zero-detection endpoint is kept separate from the branch
that can be packaged in the library's strictly-positive-rate Poisson-process
structure. -/
theorem zero_detection_or_observed_process
    (H : MarkedPoissonReportingProcess Ω P) :
    (H.detectionProbability = 0 ∧
        H.latentProcess.rate * H.detectionProbability = 0) ∨
      (0 < H.detectionProbability ∧
        ∃ observedProcess : ForwardHomogeneousPoissonCountingProcessByLaw Ω P,
          observedProcess.count = H.observedCount ∧
          observedProcess.rate =
            H.latentProcess.rate * H.detectionProbability) := by
  by_cases hzero : H.detectionProbability = 0
  · left
    exact ⟨hzero, by simp [hzero]⟩
  · right
    have hpos : 0 < H.detectionProbability :=
      lt_of_le_of_ne H.detectionProbability_nonnegative (Ne.symm hzero)
    exact ⟨hpos, H.observed_process_is_homogeneous_poisson hpos⟩

/-- The constructed observed process has the standard almost-sure rate law.

This is deliberately a conclusion about `MarkedPoissonReportingProcess`, whose
joint thinning law is part of the Lean model.  It is not a bridge from the
paper's duration and first-report timing model. -/
theorem observed_unitIntervalCount_real_strongLaw
    (H : MarkedPoissonReportingProcess Ω P)
    (hdetection : 0 < H.detectionProbability) :
    ∀ᵐ omega ∂P,
      Tendsto (fun n : ℕ =>
        (∑ i ∈ Finset.range n,
          (H.toObservedForwardPoissonProcess hdetection |>.unitIntervalCount i omega : ℝ)) / n)
        atTop (nhds (H.latentProcess.rate * H.detectionProbability)) :=
  (H.toObservedForwardPoissonProcess hdetection).unitIntervalCount_real_strongLaw

end MarkedPoissonReportingProcess

end Lemma1MarkedPoissonThinning

end

end LBG24SpatialUnderreporting
