import AppliedModelingLib.Foundations.Probability.EquilibriumPoissonBase
import AppliedModelingLib.Foundations.Probability.PoissonSuspensionBaseArrivals
import AppliedModelingLib.Foundations.Probability.PoissonSuspensionExponentialSplit
import AppliedModelingLib.Foundations.Probability.PoissonSuspensionMarkedTransport
import AppliedModelingLib.Foundations.Probability.PoissonSuspensionProductFactors

/-!
# Marked-Campbell transport bridge for the Poisson suspension

This module identifies the deterministic coordinate map from the stationary
Palm suspension to the existing origin-split equilibrium base.  It proves a
fully formal reduction of the marked unit-window Campbell formula to two
explicit probability-transport statements: the exponential central-gap split
and a deterministic branch partition of the suspension phase strip.
-/

namespace AppliedModelingLib.Probability.PoissonProcess

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

noncomputable section

/-- Split the Palm gap containing the deterministic origin at phase `u`.
The first component is the future residual path and the second is the
backward-age path used by `equilibriumTwoSidedBaseMeasure`. -/
def suspensionToEquilibrium : ((ℤ → ℝ) × ℝ) → (ℕ → ℝ) × (ℕ → ℝ) :=
  fun p =>
    (fun n => match n with
      | 0 => twoSidedGap 0 p.1 - p.2
      | m + 1 => twoSidedGap (Int.ofNat (m + 1)) p.1,
     fun n => match n with
      | 0 => p.2
      | m + 1 => twoSidedGap (Int.negSucc m) p.1)

theorem measurable_suspensionToEquilibrium :
    Measurable suspensionToEquilibrium := by
  apply Measurable.prodMk <;> refine measurable_pi_iff.2 fun n => ?_
  · cases n with
    | zero =>
        exact ((measurable_twoSidedGap 0).comp measurable_fst).sub measurable_snd
    | succ n =>
        simpa [suspensionToEquilibrium] using
          ((measurable_twoSidedGap (Int.ofNat (n + 1))).comp measurable_fst)
  · cases n with
    | zero => simpa [suspensionToEquilibrium] using measurable_snd
    | succ n =>
        simpa [suspensionToEquilibrium] using
          ((measurable_twoSidedGap (Int.negSucc n)).comp measurable_fst)

/-- The equilibrium interarrival path reconstructed from a suspension point
is exactly its original two-sided Palm gap path. -/
theorem equilibriumBaseGap_suspensionToEquilibrium
    (p : (ℤ → ℝ) × ℝ) :
    equilibriumBaseGap (suspensionToEquilibrium p) = p.1 := by
  funext i
  cases i with
  | ofNat n =>
      cases n with
      | zero =>
          simp [equilibriumBaseGap, suspensionToEquilibrium,
            equilibriumFuturePath, equilibriumPastPath, interarrival, twoSidedGap]
      | succ n =>
          simp [equilibriumBaseGap, suspensionToEquilibrium,
            equilibriumFuturePath, interarrival, twoSidedGap]
  | negSucc n =>
      simp [equilibriumBaseGap, suspensionToEquilibrium,
        equilibriumPastPath, interarrival, twoSidedGap]

/-- The untagged equilibrium epochs are the Palm epochs translated by the
phase coordinate. -/
theorem equilibriumBaseArrival_suspensionToEquilibrium
    (p : (ℤ → ℝ) × ℝ) (i : ℤ) :
    equilibriumBaseArrival (suspensionToEquilibrium p) i =
      candidatePalmArrival p.1 i - p.2 := by
  rw [equilibriumBaseArrival]
  rw [equilibriumBaseGap_suspensionToEquilibrium]
  cases p with
  | mk ω u =>
      simp [suspensionToEquilibrium, equilibriumPastPath, interarrival]

/-- Recentring the reconstructed equilibrium configuration at label `i` is
the deterministic Palm-gap reindexing at `i`. -/
theorem equilibriumRecenterGap_suspensionToEquilibrium
    (p : (ℤ → ℝ) × ℝ) (i : ℤ) :
    equilibriumRecenterGap i (suspensionToEquilibrium p) =
      suspensionGapShift i p.1 := by
  funext j
  simp only [equilibriumRecenterGap, suspensionGapShift]
  rw [equilibriumBaseGap_suspensionToEquilibrium]
  rfl

/-- The direct analytic bridge from the size-biased Palm suspension to the
origin-split equilibrium law. Proving it is exactly the exponential
central-gap split/disintegration theorem. -/
def HasSuspensionEquilibriumBridge (rate : ℝ) : Prop :=
  Measure.map suspensionToEquilibrium (suspensionMeasure rate) =
    equilibriumTwoSidedBaseMeasure rate

/-- Move the phase coordinate next to the central gap in a four-factor
product. -/
def fourFactorRotate {α β γ δ : Type*} : ((α × β) × γ) × δ →
    (α × δ) × (β × γ) :=
  fun x => ((x.1.1.1, x.2), (x.1.1.2, x.1.2))

theorem measurable_fourFactorRotate {α β γ δ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ] :
    Measurable (@fourFactorRotate α β γ δ) := by
  exact
    (((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk measurable_snd).prodMk
      ((measurable_snd.comp (measurable_fst.comp measurable_fst)).prodMk
        (measurable_snd.comp measurable_fst)))

/-- The four-factor rotation preserves the corresponding product law. -/
theorem map_fourFactorRotate_prod
    {α β γ δ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
    (μa : Measure α) (μb : Measure β) (μc : Measure γ) (μd : Measure δ)
    [SFinite μa] [SFinite μb] [SFinite μc] [SFinite μd] :
    Measure.map fourFactorRotate (((μa.prod μb).prod μc).prod μd) =
      (μa.prod μd).prod (μb.prod μc) := by
  let h1 := measurePreserving_prodAssoc (μa.prod μb) μc μd
  let h2 := (MeasurePreserving.id (μa.prod μb)).prod
    (Measure.measurePreserving_swap (μ := μc) (ν := μd))
  let h3 := measurePreserving_prodAssoc μa μb (μd.prod μc)
  let hi1 := (measurePreserving_prodAssoc μb μd μc).symm
  let hi2 := (Measure.measurePreserving_swap (μ := μb) (ν := μd)).prod
    (MeasurePreserving.id μc)
  let hi3 := measurePreserving_prodAssoc μd μb μc
  let h4 := (MeasurePreserving.id μa).prod (hi3.comp (hi2.comp hi1))
  let h5 := (measurePreserving_prodAssoc μa μd (μb.prod μc)).symm
  have h := h5.comp (h4.comp (h3.comp (h2.comp h1)))
  convert h.map_eq using 1

/-- Transpose the middle two coordinates of a four-factor product. -/
def fourFactorTranspose {α β γ δ : Type*} : (α × β) × (γ × δ) →
    (α × γ) × (β × δ) :=
  fun x => ((x.1.1, x.2.1), (x.1.2, x.2.2))

theorem measurable_fourFactorTranspose {α β γ δ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ] :
    Measurable (@fourFactorTranspose α β γ δ) := by
  exact
    (((measurable_fst.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd)).prodMk
      ((measurable_snd.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd)))

/-- The middle-factor transpose preserves the corresponding product law. -/
theorem map_fourFactorTranspose_prod
    {α β γ δ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
    (μa : Measure α) (μb : Measure β) (μc : Measure γ) (μd : Measure δ)
    [SFinite μa] [SFinite μb] [SFinite μc] [SFinite μd] :
    Measure.map fourFactorTranspose ((μa.prod μb).prod (μc.prod μd)) =
      (μa.prod μc).prod (μb.prod μd) := by
  let s2 : (α × β) × (δ × γ) → ((α × β) × δ) × γ :=
    (MeasurableEquiv.prodAssoc : ((α × β) × δ) × γ ≃ᵐ
      (α × β) × (δ × γ)).symm
  have hs1 : Measure.map (Prod.map id Prod.swap)
      ((μa.prod μb).prod (μc.prod μd)) =
      (μa.prod μb).prod (μd.prod μc) := by
    rw [← Measure.map_prod_map _ _ measurable_id measurable_swap,
      Measure.map_id, Measure.prod_swap]
  have hs2 : Measure.map s2 ((μa.prod μb).prod (μd.prod μc)) =
      ((μa.prod μb).prod μd).prod μc := by
    exact (measurePreserving_prodAssoc (μa.prod μb) μd μc).symm.map_eq
  calc
    Measure.map fourFactorTranspose ((μa.prod μb).prod (μc.prod μd)) =
        Measure.map (fourFactorRotate ∘ s2 ∘ Prod.map id Prod.swap)
          ((μa.prod μb).prod (μc.prod μd)) := by
          congr 1
    _ = Measure.map fourFactorRotate
        (Measure.map s2 (Measure.map (Prod.map id Prod.swap)
          ((μa.prod μb).prod (μc.prod μd)))) := by
          symm
          rw [Measure.map_map measurable_fourFactorRotate
            (MeasurableEquiv.prodAssoc : ((α × β) × δ) × γ ≃ᵐ
              (α × β) × (δ × γ)).symm.measurable,
            Measure.map_map
              (measurable_fourFactorRotate.comp
                (MeasurableEquiv.prodAssoc : ((α × β) × δ) × γ ≃ᵐ
                  (α × β) × (δ × γ)).symm.measurable)
              (measurable_id.prodMap measurable_swap)]
          rfl
    _ = Measure.map fourFactorRotate (Measure.map s2
        ((μa.prod μb).prod (μd.prod μc))) := by rw [hs1]
    _ = Measure.map fourFactorRotate (((μa.prod μb).prod μd).prod μc) := by rw [hs2]
    _ = (μa.prod μc).prod (μb.prod μd) :=
          map_fourFactorRotate_prod μa μb μd μc

/-- Put the Palm central gap beside its phase, retaining the two untouched
iid tails. -/
def suspensionCentralPhaseTails : ((ℤ → ℝ) × ℝ) →
    (ℝ × ℝ) × ((ℕ → ℝ) × (ℕ → ℝ)) :=
  fun p => fourFactorRotate (twoSidedHeadPositiveNegative p.1, p.2)

theorem measurable_suspensionCentralPhaseTails :
    Measurable suspensionCentralPhaseTails := by
  exact (measurable_fourFactorRotate.comp
    ((measurable_twoSidedHeadPositiveNegative.comp measurable_fst).prodMk measurable_snd))

theorem suspensionCarrier_eq_preimage_centralPhaseTails :
    suspensionCarrier =
      suspensionCentralPhaseTails ⁻¹'
        (exponentialSplitCarrier ×ˢ Set.univ) := by
  ext p
  rcases p with ⟨ω, u⟩
  simp [suspensionCarrier, suspensionCentralPhaseTails,
    twoSidedHeadPositiveNegative_apply, fourFactorRotate, exponentialSplitCarrier,
    twoSidedGap]

/-- Tensor the normalized central gap/phase law with the independent positive
and negative Palm tails. -/
theorem map_suspensionCentralPhaseTails_suspensionMeasure
    {rate : ℝ} (hrate : 0 < rate) :
    Measure.map suspensionCentralPhaseTails (suspensionMeasure rate) =
      (ENNReal.ofReal rate • ((expMeasure rate).prod volume).restrict
        exponentialSplitCarrier).prod
        ((exponentialInterarrivalMeasure rate).prod
          (exponentialInterarrivalMeasure rate)) := by
  let tails : Measure ((ℕ → ℝ) × (ℕ → ℝ)) :=
    (exponentialInterarrivalMeasure rate).prod
      (exponentialInterarrivalMeasure rate)
  let raw : Measure ((ℤ → ℝ) × ℝ) :=
    (twoSidedInterarrivalMeasure rate).prod volume
  letI : IsProbabilityMeasure (expMeasure rate) :=
    isProbabilityMeasure_expMeasure hrate
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure rate) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure hrate
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure rate) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure tails := by
    dsimp [tails]
    infer_instance
  have hraw : Measure.map suspensionCentralPhaseTails raw =
      ((expMeasure rate).prod volume).prod tails := by
    calc
      Measure.map suspensionCentralPhaseTails raw =
          Measure.map fourFactorRotate
            (Measure.map (Prod.map twoSidedHeadPositiveNegative id) raw) := by
            symm
            rw [Measure.map_map measurable_fourFactorRotate
              (measurable_twoSidedHeadPositiveNegative.prodMap measurable_id)]
            rfl
      _ = Measure.map fourFactorRotate
          ((((expMeasure rate).prod (exponentialInterarrivalMeasure rate)).prod
            (exponentialInterarrivalMeasure rate)).prod volume) := by
            rw [← Measure.map_prod_map _ _
              measurable_twoSidedHeadPositiveNegative measurable_id,
              map_twoSidedHeadPositiveNegative_twoSidedInterarrivalMeasure hrate,
              Measure.map_id]
      _ = ((expMeasure rate).prod volume).prod tails := by
            simpa [tails] using
              (map_fourFactorRotate_prod (expMeasure rate)
                (exponentialInterarrivalMeasure rate)
                (exponentialInterarrivalMeasure rate) volume)
  calc
    Measure.map suspensionCentralPhaseTails (suspensionMeasure rate) =
        ENNReal.ofReal rate •
          Measure.map suspensionCentralPhaseTails (raw.restrict suspensionCarrier) := by
          simp only [suspensionMeasure, raw, Measure.map_smul]
    _ = ENNReal.ofReal rate •
          (Measure.map suspensionCentralPhaseTails raw).restrict
            (exponentialSplitCarrier ×ˢ Set.univ) := by
          rw [suspensionCarrier_eq_preimage_centralPhaseTails,
            ← Measure.restrict_map measurable_suspensionCentralPhaseTails
              (measurableSet_exponentialSplitCarrier.prod MeasurableSet.univ)]
    _ = ENNReal.ofReal rate •
          (((expMeasure rate).prod volume).prod tails).restrict
            (exponentialSplitCarrier ×ˢ Set.univ) := by rw [hraw]
    _ = ENNReal.ofReal rate •
          (((expMeasure rate).prod volume).restrict exponentialSplitCarrier).prod tails := by
          rw [← Measure.restrict_prod_eq_prod_univ]
    _ = (ENNReal.ofReal rate • ((expMeasure rate).prod volume).restrict
          exponentialSplitCarrier).prod tails := by
          rw [Measure.prod_smul_left]
    _ = (ENNReal.ofReal rate • ((expMeasure rate).prod volume).restrict
          exponentialSplitCarrier).prod
        ((exponentialInterarrivalMeasure rate).prod
          (exponentialInterarrivalMeasure rate)) := by rfl

/-- Reconstructing a one-sided path after splitting its head and tail restores
its iid exponential law. -/
theorem map_headTailEquiv_symm_expMeasure_prod_exponentialInterarrivalMeasure
    {rate : ℝ} (hrate : 0 < rate) :
    Measure.map headTailEquiv.symm
      ((expMeasure rate).prod (exponentialInterarrivalMeasure rate)) =
      exponentialInterarrivalMeasure rate := by
  calc
    Measure.map headTailEquiv.symm
        ((expMeasure rate).prod (exponentialInterarrivalMeasure rate)) =
        Measure.map headTailEquiv.symm
          (Measure.map headTail (exponentialInterarrivalMeasure rate)) := by
          rw [map_headTail_exponentialInterarrivalMeasure hrate]
    _ = Measure.map (headTailEquiv.symm ∘ headTail)
          (exponentialInterarrivalMeasure rate) := by
          rw [Measure.map_map headTailEquiv.symm.measurable measurable_headTail]
    _ = exponentialInterarrivalMeasure rate := by
          have hfun : headTailEquiv.symm ∘ headTail = id := by
            funext f
            exact headTailEquiv.symm_apply_apply f
          rw [hfun]
          exact Measure.map_id

/-- Apply the local gap/phase unshear while leaving both iid tails fixed. -/
def suspensionLocalUnshearTails : (ℝ × ℝ) × ((ℕ → ℝ) × (ℕ → ℝ)) →
    (ℝ × ℝ) × ((ℕ → ℝ) × (ℕ → ℝ)) :=
  Prod.map exponentialSplitUnshear id

theorem measurable_suspensionLocalUnshearTails :
    Measurable suspensionLocalUnshearTails :=
  measurable_exponentialSplitUnshear.prodMap measurable_id

theorem map_suspensionLocalUnshearTails
    {rate : ℝ} (hrate : 0 < rate) :
    Measure.map suspensionLocalUnshearTails
      ((ENNReal.ofReal rate • ((expMeasure rate).prod volume).restrict
        exponentialSplitCarrier).prod
        ((exponentialInterarrivalMeasure rate).prod
          (exponentialInterarrivalMeasure rate))) =
      ((expMeasure rate).prod (expMeasure rate)).prod
        ((exponentialInterarrivalMeasure rate).prod
          (exponentialInterarrivalMeasure rate)) := by
  letI : IsProbabilityMeasure (expMeasure rate) :=
    isProbabilityMeasure_expMeasure hrate
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure rate) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : SFinite ((expMeasure rate).prod (volume : Measure ℝ)) := by infer_instance
  letI : SFinite (((expMeasure rate).prod (volume : Measure ℝ)).restrict exponentialSplitCarrier) := by
    infer_instance
  letI : SFinite (ENNReal.ofReal rate •
      ((expMeasure rate).prod (volume : Measure ℝ)).restrict exponentialSplitCarrier) := by
    infer_instance
  letI : SFinite ((exponentialInterarrivalMeasure rate).prod
      (exponentialInterarrivalMeasure rate)) := by infer_instance
  unfold suspensionLocalUnshearTails
  rw [← Measure.map_prod_map _ _
    measurable_exponentialSplitUnshear measurable_id,
    map_exponentialSplitUnshear_rate_smul_expMeasure_prod_volume_restrict hrate,
    Measure.map_id]

/-- Regroup residual and positive tail, and age and negative tail, then
reconstruct the two one-sided interarrival paths. -/
def suspensionTransposeAndAssemble : (ℝ × ℝ) × ((ℕ → ℝ) × (ℕ → ℝ)) →
    (ℕ → ℝ) × (ℕ → ℝ) :=
  (Prod.map headTailEquiv.symm headTailEquiv.symm) ∘ fourFactorTranspose

theorem measurable_suspensionTransposeAndAssemble :
    Measurable suspensionTransposeAndAssemble :=
  (headTailEquiv.symm.measurable.prodMap headTailEquiv.symm.measurable).comp
    measurable_fourFactorTranspose

theorem map_suspensionTransposeAndAssemble
    {rate : ℝ} (hrate : 0 < rate) :
    Measure.map suspensionTransposeAndAssemble
      (((expMeasure rate).prod (expMeasure rate)).prod
        ((exponentialInterarrivalMeasure rate).prod
          (exponentialInterarrivalMeasure rate))) =
      (exponentialInterarrivalMeasure rate).prod
        (exponentialInterarrivalMeasure rate) := by
  letI : IsProbabilityMeasure (expMeasure rate) :=
    isProbabilityMeasure_expMeasure hrate
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure rate) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  unfold suspensionTransposeAndAssemble
  rw [← Measure.map_map
    (headTailEquiv.symm.measurable.prodMap headTailEquiv.symm.measurable)
    measurable_fourFactorTranspose,
    map_fourFactorTranspose_prod (expMeasure rate) (expMeasure rate)
      (exponentialInterarrivalMeasure rate) (exponentialInterarrivalMeasure rate),
    ← Measure.map_prod_map _ _ headTailEquiv.symm.measurable
      headTailEquiv.symm.measurable,
    map_headTailEquiv_symm_expMeasure_prod_exponentialInterarrivalMeasure hrate]

theorem suspensionToEquilibrium_factorization :
    suspensionToEquilibrium =
      suspensionTransposeAndAssemble ∘ suspensionLocalUnshearTails ∘
        suspensionCentralPhaseTails := by
  funext p
  rcases p with ⟨ω, u⟩
  apply Prod.ext
  · funext n
    cases n with
    | zero => rfl
    | succ n => rfl
  · funext n
    cases n with
    | zero => rfl
    | succ n => rfl

/-- The stationary Palm suspension viewed from a deterministic origin has
the residual/age iid law of the equilibrium two-sided Poisson base. -/
theorem hasSuspensionEquilibriumBridge
    {rate : ℝ} (hrate : 0 < rate) : HasSuspensionEquilibriumBridge rate := by
  unfold HasSuspensionEquilibriumBridge
  rw [suspensionToEquilibrium_factorization]
  calc
    Measure.map
        (suspensionTransposeAndAssemble ∘ suspensionLocalUnshearTails ∘
          suspensionCentralPhaseTails)
        (suspensionMeasure rate) =
        Measure.map suspensionTransposeAndAssemble
          (Measure.map suspensionLocalUnshearTails
            (Measure.map suspensionCentralPhaseTails (suspensionMeasure rate))) := by
          symm
          rw [Measure.map_map measurable_suspensionTransposeAndAssemble
            measurable_suspensionLocalUnshearTails,
            Measure.map_map
              (measurable_suspensionTransposeAndAssemble.comp
                measurable_suspensionLocalUnshearTails)
              measurable_suspensionCentralPhaseTails]
          rfl
    _ = Measure.map suspensionTransposeAndAssemble
          (Measure.map suspensionLocalUnshearTails
            ((ENNReal.ofReal rate • ((expMeasure rate).prod volume).restrict
              exponentialSplitCarrier).prod
              ((exponentialInterarrivalMeasure rate).prod
                (exponentialInterarrivalMeasure rate)))) := by
          rw [map_suspensionCentralPhaseTails_suspensionMeasure hrate]
    _ = Measure.map suspensionTransposeAndAssemble
          (((expMeasure rate).prod (expMeasure rate)).prod
            ((exponentialInterarrivalMeasure rate).prod
              (exponentialInterarrivalMeasure rate))) := by
          rw [map_suspensionLocalUnshearTails hrate]
    _ = equilibriumTwoSidedBaseMeasure rate := by
          rw [map_suspensionTransposeAndAssemble hrate]
          rfl

/-- Under the suspension/equilibrium law bridge, each current equilibrium
summand is almost everywhere the ideal suspension summand. -/
theorem ae_equilibriumMarkedUnitSummand_suspensionToEquilibrium_eq
    {rate : ℝ} (hrate : 0 < rate)
    (hbridge : HasSuspensionEquilibriumBridge rate)
    (s : Set (ℤ → ℝ)) (i : ℤ) :
    ∀ᵐ p ∂suspensionMeasure rate,
      equilibriumMarkedUnitSummand s i (suspensionToEquilibrium p) =
        suspensionMarkedUnitSummand s i p := by
  classical
  have hbase : ∀ᵐ ω ∂equilibriumTwoSidedBaseMeasure rate,
      i ∈ equilibriumForwardArrivalIndices 1 ω ∪
          equilibriumBackwardArrivalIndices 0 ω ∧
          0 ≤ equilibriumBaseArrival ω i ∧ equilibriumBaseArrival ω i < 1 ↔
        0 ≤ equilibriumBaseArrival ω i ∧ equilibriumBaseArrival ω i < 1 := by
    filter_upwards [ae_mem_equilibriumHalfOpenIntervalArrivalIndices_iff hrate 0 1]
      with ω hω
    have hi := hω i
    change (i ∈ equilibriumHalfOpenIntervalArrivalIndices 0 1 ω) ↔ _ at hi
    simpa [equilibriumHalfOpenIntervalArrivalIndices] using hi
  have hmap : ∀ᵐ ω ∂Measure.map suspensionToEquilibrium (suspensionMeasure rate),
      i ∈ equilibriumForwardArrivalIndices 1 ω ∪
          equilibriumBackwardArrivalIndices 0 ω ∧
          0 ≤ equilibriumBaseArrival ω i ∧ equilibriumBaseArrival ω i < 1 ↔
        0 ≤ equilibriumBaseArrival ω i ∧ equilibriumBaseArrival ω i < 1 := by
    rw [hbridge]
    exact hbase
  filter_upwards [MeasureTheory.ae_of_ae_map
    measurable_suspensionToEquilibrium.aemeasurable hmap] with p hp
  rw [equilibriumMarkedUnitSummand, suspensionMarkedUnitSummand]
  rw [equilibriumBaseArrival_suspensionToEquilibrium,
    equilibriumRecenterGap_suspensionToEquilibrium]
  rw [equilibriumBaseArrival_suspensionToEquilibrium] at hp
  have hsel :
      (i ∈ equilibriumForwardArrivalIndices 1 (suspensionToEquilibrium p) ∪
          equilibriumBackwardArrivalIndices 0 (suspensionToEquilibrium p) ∧
        0 ≤ candidatePalmArrival p.1 i - p.2 ∧
        candidatePalmArrival p.1 i - p.2 < 1 ∧ suspensionGapShift i p.1 ∈ s) ↔
        (0 ≤ candidatePalmArrival p.1 i - p.2 ∧
          candidatePalmArrival p.1 i - p.2 < 1 ∧ suspensionGapShift i p.1 ∈ s) := by
    constructor
    · rintro ⟨_, hzero, hone, hmark⟩
      exact ⟨hzero, hone, hmark⟩
    · rintro ⟨hzero, hone, hmark⟩
      have hprefix :
          i ∈ equilibriumForwardArrivalIndices 1 (suspensionToEquilibrium p) ∪
              equilibriumBackwardArrivalIndices 0 (suspensionToEquilibrium p) ∧
            0 ≤ candidatePalmArrival p.1 i - p.2 ∧
              candidatePalmArrival p.1 i - p.2 < 1 := hp.mpr ⟨hzero, hone⟩
      exact ⟨hprefix.1, hprefix.2.1, hprefix.2.2, hmark⟩
  by_cases hselected :
      0 ≤ candidatePalmArrival p.1 i - p.2 ∧
        candidatePalmArrival p.1 i - p.2 < 1 ∧ suspensionGapShift i p.1 ∈ s
  · have hleft :
        i ∈ equilibriumForwardArrivalIndices 1 (suspensionToEquilibrium p) ∪
            equilibriumBackwardArrivalIndices 0 (suspensionToEquilibrium p) ∧
          0 ≤ candidatePalmArrival p.1 i - p.2 ∧
            candidatePalmArrival p.1 i - p.2 < 1 ∧ suspensionGapShift i p.1 ∈ s :=
      hsel.mpr hselected
    calc
      (if i ∈ equilibriumForwardArrivalIndices 1 (suspensionToEquilibrium p) ∪
            equilibriumBackwardArrivalIndices 0 (suspensionToEquilibrium p) ∧
          0 ≤ candidatePalmArrival p.1 i - p.2 ∧
            candidatePalmArrival p.1 i - p.2 < 1 ∧ suspensionGapShift i p.1 ∈ s
        then (1 : ℝ≥0∞) else 0) = 1 := if_pos hleft
      _ = (if 0 ≤ candidatePalmArrival p.1 i - p.2 ∧
            candidatePalmArrival p.1 i - p.2 < 1 ∧ suspensionGapShift i p.1 ∈ s
          then (1 : ℝ≥0∞) else 0) := (if_pos hselected).symm
  · have hleft : ¬
        (i ∈ equilibriumForwardArrivalIndices 1 (suspensionToEquilibrium p) ∪
            equilibriumBackwardArrivalIndices 0 (suspensionToEquilibrium p) ∧
          0 ≤ candidatePalmArrival p.1 i - p.2 ∧
            candidatePalmArrival p.1 i - p.2 < 1 ∧ suspensionGapShift i p.1 ∈ s) := by
      intro h
      exact hselected (hsel.mp h)
    calc
      (if i ∈ equilibriumForwardArrivalIndices 1 (suspensionToEquilibrium p) ∪
            equilibriumBackwardArrivalIndices 0 (suspensionToEquilibrium p) ∧
          0 ≤ candidatePalmArrival p.1 i - p.2 ∧
            candidatePalmArrival p.1 i - p.2 < 1 ∧ suspensionGapShift i p.1 ∈ s
        then (1 : ℝ≥0∞) else 0) = 0 := if_neg hleft
      _ = (if 0 ≤ candidatePalmArrival p.1 i - p.2 ∧
            candidatePalmArrival p.1 i - p.2 < 1 ∧ suspensionGapShift i p.1 ∈ s
          then (1 : ℝ≥0∞) else 0) := (if_neg hselected).symm

/-- A fully checked reduction from the equilibrium marked-count Tonelli
theorem to the two remaining probability transports. No unproved Palm or
independence fact is hidden here. -/
theorem lintegral_equilibriumMarkedUnitWindowCount_eq_rate_mul_palm_of_suspension
    {rate : ℝ} (hrate : 0 < rate)
    (hbridge : HasSuspensionEquilibriumBridge rate)
    (htransport : HasSuspensionMarkedUnitTransport rate)
    (s : Set (ℤ → ℝ)) (hs : MeasurableSet s) :
    ∫⁻ ω, (Palm.unitWindowCampbellCount
      equilibriumHalfOpenIntervalArrivalIndices
      (fun ω i => equilibriumRecenterGap i ω) s ω : ℝ≥0∞)
      ∂equilibriumTwoSidedBaseMeasure rate =
      ENNReal.ofReal rate * twoSidedInterarrivalMeasure rate s := by
  calc
    ∫⁻ ω, (Palm.unitWindowCampbellCount equilibriumHalfOpenIntervalArrivalIndices
        (fun ω i => equilibriumRecenterGap i ω) s ω : ℝ≥0∞)
        ∂equilibriumTwoSidedBaseMeasure rate =
        ∑' i : ℤ, ∫⁻ ω, equilibriumMarkedUnitSummand s i ω
          ∂equilibriumTwoSidedBaseMeasure rate :=
      lintegral_equilibriumMarkedUnitWindowCount_eq_tsum s hs
    _ = ∑' i : ℤ, ∫⁻ p,
        equilibriumMarkedUnitSummand s i (suspensionToEquilibrium p)
          ∂suspensionMeasure rate := by
      apply tsum_congr
      intro i
      calc
        ∫⁻ ω, equilibriumMarkedUnitSummand s i ω
            ∂equilibriumTwoSidedBaseMeasure rate =
            ∫⁻ ω, equilibriumMarkedUnitSummand s i ω
              ∂Measure.map suspensionToEquilibrium (suspensionMeasure rate) := by
                rw [hbridge]
        _ = ∫⁻ p, equilibriumMarkedUnitSummand s i (suspensionToEquilibrium p)
            ∂suspensionMeasure rate := by
              exact MeasureTheory.lintegral_map
                (measurable_equilibriumMarkedUnitSummand s hs i)
                measurable_suspensionToEquilibrium
    _ = ∑' i : ℤ, ∫⁻ p, suspensionMarkedUnitSummand s i p
        ∂suspensionMeasure rate := by
      apply tsum_congr
      intro i
      exact MeasureTheory.lintegral_congr_ae
        (ae_equilibriumMarkedUnitSummand_suspensionToEquilibrium_eq
          hrate hbridge s i)
    _ = ENNReal.ofReal rate * twoSidedInterarrivalMeasure rate s :=
      htransport s hs

/-- The origin-split equilibrium Poisson configuration satisfies the marked
unit-window Campbell identity.  This is the equilibrium-coordinate derivation
of the same stationary Palm transport certified directly by
`poissonSuspensionCampbellCertificate`; it makes no queue-state or PASTA
claim. -/
theorem lintegral_equilibriumMarkedUnitWindowCount_eq_rate_mul_palm
    {rate : ℝ} (hrate : 0 < rate)
    (s : Set (ℤ → ℝ)) (hs : MeasurableSet s) :
    ∫⁻ ω, (Palm.unitWindowCampbellCount
      equilibriumHalfOpenIntervalArrivalIndices
      (fun ω i => equilibriumRecenterGap i ω) s ω : ℝ≥0∞)
      ∂equilibriumTwoSidedBaseMeasure rate =
      ENNReal.ofReal rate * twoSidedInterarrivalMeasure rate s := by
  exact lintegral_equilibriumMarkedUnitWindowCount_eq_rate_mul_palm_of_suspension
    hrate (hasSuspensionEquilibriumBridge hrate)
    (hasSuspensionMarkedUnitTransport hrate) s hs

end

end AppliedModelingLib.Probability.PoissonProcess
