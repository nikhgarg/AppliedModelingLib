import AppliedModelingLib.Foundations.Probability.PoissonSuspensionExponentialSplit
import AppliedModelingLib.Foundations.Probability.ExponentialInterarrival

/-!
# Finite exponential-gap and cumulative-arrival densities

This module gives measure-level finite-dimensional density facts for iid
exponential gaps.  In particular, it transports their product density through
the cumulative-sum coordinate map to finite ordered arrival epochs.  It does
not impose a terminal no-arrival event; that survival integration belongs to a
separate finite-horizon theorem.
-/

namespace AppliedModelingLib.Probability.PoissonProcess

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

/-- The lower-triangular coordinate change from finite gaps to cumulative sums. -/
def cumulativeArrivalMatrix (q : ℕ) : Matrix (Fin q) (Fin q) ℝ :=
  fun i j => if j ≤ i then 1 else 0

/-- The linear map represented by `cumulativeArrivalMatrix`. -/
def cumulativeArrivalLinearMap (q : ℕ) :
    (Fin q → ℝ) →ₗ[ℝ] Fin q → ℝ :=
  Matrix.toLin' (cumulativeArrivalMatrix q)

/-- Cumulative arrival epochs associated with a finite block of gaps. -/
def cumulativeArrivalVector (q : ℕ) : (Fin q → ℝ) → Fin q → ℝ :=
  fun gaps i => ∑ j : {j : Fin q // j ≤ i}, gaps j

/-- The linear coordinate map is the finite cumulative-arrival vector. -/
theorem cumulativeArrivalLinearMap_apply (q : ℕ) (gaps : Fin q → ℝ) :
    cumulativeArrivalLinearMap q gaps = cumulativeArrivalVector q gaps := by
  funext i
  simp only [cumulativeArrivalLinearMap, Matrix.toLin'_apply, Matrix.mulVec,
    cumulativeArrivalMatrix, cumulativeArrivalVector]
  change (∑ j : Fin q, (if j ≤ i then 1 else 0) * gaps j) = _
  rw [show (∑ j : Fin q, (if j ≤ i then 1 else 0) * gaps j) =
      ∑ j ∈ Finset.univ.filter (fun j : Fin q => j ≤ i), gaps j by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _hj
    by_cases hj : j ≤ i <;> simp [hj]]
  rw [Finset.sum_subtype]
  intro j
  simp

theorem cumulativeArrivalMatrix_lowerTriangular (q : ℕ) :
    (cumulativeArrivalMatrix q).BlockTriangular (OrderDual.toDual ∘ id) := by
  intro i j hij
  simp only [Function.comp_apply, id_eq] at hij
  have hij' : i < j := OrderDual.toDual_lt_toDual.mp hij
  simp [cumulativeArrivalMatrix, not_le_of_gt hij']

theorem cumulativeArrivalMatrix_det (q : ℕ) :
    (cumulativeArrivalMatrix q).det = 1 := by
  rw [Matrix.det_of_lowerTriangular (cumulativeArrivalMatrix q)
    (cumulativeArrivalMatrix_lowerTriangular q)]
  simp [cumulativeArrivalMatrix]

theorem cumulativeArrivalLinearMap_det (q : ℕ) :
    LinearMap.det (cumulativeArrivalLinearMap q) = 1 := by
  rw [← LinearMap.det_toMatrix']
  change (LinearMap.toMatrix' (Matrix.toLin' (cumulativeArrivalMatrix q))).det = 1
  rw [show LinearMap.toMatrix' (Matrix.toLin' (cumulativeArrivalMatrix q)) =
      cumulativeArrivalMatrix q by
    ext i j
    simp [Matrix.toLin'_apply, cumulativeArrivalMatrix]]
  exact cumulativeArrivalMatrix_det q

/-- Cumulative summation preserves finite-dimensional Lebesgue measure. -/
theorem cumulativeArrivalLinearMap_volume_preserving (q : ℕ) :
    MeasurePreserving (cumulativeArrivalLinearMap q) (volume : Measure (Fin q → ℝ)) volume := by
  refine ⟨(LinearMap.continuous_on_pi (cumulativeArrivalLinearMap q)).measurable, ?_⟩
  rw [Real.map_linearMap_volume_pi_eq_smul_volume_pi]
  · simp [cumulativeArrivalLinearMap_det]
  · rw [cumulativeArrivalLinearMap_det]
    norm_num

theorem cumulativeArrivalLinearMap_injective (q : ℕ) :
    Function.Injective (cumulativeArrivalLinearMap q) := by
  apply LinearMap.ker_eq_bot.mp
  by_contra hker
  have hdet : LinearMap.det (cumulativeArrivalLinearMap q) = 0 :=
    (LinearMap.det_eq_zero_iff_ker_ne_bot).2 hker
  rw [cumulativeArrivalLinearMap_det] at hdet
  norm_num at hdet

/-- The cumulative-arrival coordinate change is a linear equivalence. -/
noncomputable def cumulativeArrivalLinearEquiv (q : ℕ) :
    (Fin q → ℝ) ≃ₗ[ℝ] Fin q → ℝ :=
  LinearEquiv.ofInjectiveEndo (cumulativeArrivalLinearMap q)
    (cumulativeArrivalLinearMap_injective q)

@[simp] theorem cumulativeArrivalLinearEquiv_apply (q : ℕ) (x : Fin q → ℝ) :
    cumulativeArrivalLinearEquiv q x = cumulativeArrivalLinearMap q x :=
  rfl

theorem measurable_cumulativeArrivalLinearEquiv_symm (q : ℕ) :
    Measurable (cumulativeArrivalLinearEquiv q).symm := by
  exact (LinearMap.continuous_on_pi
    (cumulativeArrivalLinearEquiv q).symm.toLinearMap).measurable

/-- The product density of a finite block of iid rate-`rate` exponential gaps. -/
def exponentialBlockDensity (rate : ℝ) (q : ℕ) :
    (Fin q → ℝ) → ℝ≥0∞ :=
  fun gaps => ∏ i : Fin q, exponentialPDF rate (gaps i)

theorem measurable_exponentialBlockDensity (rate : ℝ) (q : ℕ) :
    Measurable (exponentialBlockDensity rate q) := by
  unfold exponentialBlockDensity
  exact Finset.measurable_prod Finset.univ fun i _hi =>
    (measurable_exponentialPDF rate).comp (measurable_pi_apply i)

/-- A finite-gap carrier with a terminal next-gap survival condition. -/
def terminalSurvivalEvent
    {α : Type*} (time : α → ℝ) (carrier : Set α) (horizon : ℝ) :
    Set (α × ℝ) :=
  {p | p.1 ∈ carrier ∧ horizon < time p.1 + p.2}

/-- The exponential terminal-survival density on a pre-terminal carrier. -/
def terminalSurvivalDensity
    {α : Type*} (rate horizon : ℝ) (time : α → ℝ) (carrier : Set α) :
    α → ℝ≥0∞ :=
  carrier.indicator fun a => ENNReal.ofReal (Real.exp (-(rate * (horizon - time a))))

theorem measurableSet_terminalSurvivalEvent
    {α : Type*} [MeasurableSpace α] {time : α → ℝ} {carrier : Set α}
    {horizon : ℝ} (htime : Measurable time) (hcarrier : MeasurableSet carrier) :
    MeasurableSet (terminalSurvivalEvent time carrier horizon) := by
  exact (measurable_fst hcarrier).inter
    (measurableSet_lt measurable_const ((htime.comp measurable_fst).add measurable_snd))

theorem measurable_terminalSurvivalDensity
    {α : Type*} [MeasurableSpace α] (rate horizon : ℝ) {time : α → ℝ}
    {carrier : Set α} (htime : Measurable time) (hcarrier : MeasurableSet carrier) :
    Measurable (terminalSurvivalDensity rate horizon time carrier) := by
  apply Measurable.indicator
  · fun_prop
  · exact hcarrier

private theorem expMeasure_Ioi_eq_ofReal_exp
    {rate threshold : ℝ} (hrate : 0 < rate) (hthreshold : 0 ≤ threshold) :
    expMeasure rate (Set.Ioi threshold) =
      ENNReal.ofReal (Real.exp (-(rate * threshold))) := by
  let model : AppliedModelingLib.Probability.Exponential.Model := ⟨rate, hrate⟩
  letI : IsProbabilityMeasure (expMeasure rate) :=
    isProbabilityMeasure_expMeasure hrate
  apply (ENNReal.toReal_eq_toReal_iff'
    (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
  change (model.measure (Set.Ioi threshold)).toReal =
    (ENNReal.ofReal (Real.exp (-(rate * threshold)))).toReal
  rw [model.measure_Ioi_toReal hthreshold]
  exact (ENNReal.toReal_ofReal (le_of_lt (Real.exp_pos _))).symm

private theorem preimage_fst_inter_terminalSurvivalEvent
    {α : Type*} (B carrier : Set α) (time : α → ℝ) (horizon : ℝ) (a : α)
    [Decidable (a ∈ B ∩ carrier)] :
    Prod.mk a ⁻¹' (Prod.fst ⁻¹' B ∩ terminalSurvivalEvent time carrier horizon) =
      if a ∈ B ∩ carrier then Set.Ioi (horizon - time a) else ∅ := by
  classical
  by_cases ha : a ∈ B ∩ carrier
  · ext z
    rw [if_pos ha]
    change (a ∈ B ∧ a ∈ carrier ∧ horizon < time a + z) ↔ horizon - time a < z
    constructor
    · rintro ⟨haB, hac, haz⟩
      exact by linarith
    · intro hz
      exact ⟨ha.1, ha.2, by linarith⟩
  · ext z
    rw [if_neg ha]
    change (a ∈ B ∧ a ∈ carrier ∧ horizon < time a + z) ↔ False
    constructor
    · rintro ⟨haB, hac, _⟩
      exact False.elim (ha ⟨haB, hac⟩)
    · exact False.elim

private theorem terminalSurvivalProjection_apply
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]
    {rate horizon : ℝ} (hrate : 0 < rate) (time : α → ℝ) (carrier B : Set α)
    (htime : Measurable time) (hcarrier : MeasurableSet carrier) (hB : MeasurableSet B) :
    Measure.map Prod.fst ((μ.prod (expMeasure rate)).restrict
      (terminalSurvivalEvent time carrier horizon)) B =
      ∫⁻ a, expMeasure rate
        (Prod.mk a ⁻¹' (Prod.fst ⁻¹' B ∩ terminalSurvivalEvent time carrier horizon)) ∂μ := by
  letI : IsProbabilityMeasure (expMeasure rate) :=
    isProbabilityMeasure_expMeasure hrate
  rw [Measure.map_apply measurable_fst hB]
  rw [Measure.restrict_apply (measurable_fst hB)]
  rw [Measure.prod_apply ((measurable_fst hB).inter
    (measurableSet_terminalSurvivalEvent htime hcarrier))]

private theorem terminalSurvivalProjection_apply_slice
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]
    {rate horizon : ℝ} (hrate : 0 < rate) (time : α → ℝ) (carrier B : Set α)
    (htime : Measurable time) (hcarrier : MeasurableSet carrier) (hB : MeasurableSet B) :
    Measure.map Prod.fst ((μ.prod (expMeasure rate)).restrict
      (terminalSurvivalEvent time carrier horizon)) B =
      ∫⁻ a in B ∩ carrier, expMeasure rate (Set.Ioi (horizon - time a)) ∂μ := by
  classical
  rw [terminalSurvivalProjection_apply hrate time carrier B htime hcarrier hB]
  calc
    ∫⁻ a, expMeasure rate
        (Prod.mk a ⁻¹' (Prod.fst ⁻¹' B ∩ terminalSurvivalEvent time carrier horizon)) ∂μ =
        ∫⁻ a, (B ∩ carrier).indicator
          (fun a => expMeasure rate (Set.Ioi (horizon - time a))) a ∂μ := by
      apply lintegral_congr
      intro a
      rw [preimage_fst_inter_terminalSurvivalEvent B carrier time horizon a]
      by_cases ha : a ∈ B ∩ carrier <;> simp [ha]
    _ = ∫⁻ a in B ∩ carrier, expMeasure rate (Set.Ioi (horizon - time a)) ∂μ := by
      rw [MeasureTheory.lintegral_indicator (hB.inter hcarrier)]

/--
Projecting an iid terminal exponential gap after a measurable pre-terminal
carrier gives the exact exponential-survival density over that carrier.
-/
theorem map_fst_restrict_terminalSurvivalEvent_eq_withDensity
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]
    {rate horizon : ℝ} (hrate : 0 < rate) (time : α → ℝ) (carrier : Set α)
    (htime : Measurable time) (hcarrier : MeasurableSet carrier)
    (hcarrier_time : ∀ a ∈ carrier, time a ≤ horizon) :
    Measure.map Prod.fst ((μ.prod (expMeasure rate)).restrict
      (terminalSurvivalEvent time carrier horizon)) =
      μ.withDensity (terminalSurvivalDensity rate horizon time carrier) := by
  apply Measure.ext
  intro B hB
  calc
    Measure.map Prod.fst ((μ.prod (expMeasure rate)).restrict
        (terminalSurvivalEvent time carrier horizon)) B =
        ∫⁻ a in B ∩ carrier, expMeasure rate (Set.Ioi (horizon - time a)) ∂μ := by
      exact terminalSurvivalProjection_apply_slice hrate time carrier B htime hcarrier hB
    _ = ∫⁻ a in B ∩ carrier,
        ENNReal.ofReal (Real.exp (-(rate * (horizon - time a)))) ∂μ := by
      apply MeasureTheory.setLIntegral_congr_fun (hB.inter hcarrier)
      intro a ha
      exact expMeasure_Ioi_eq_ofReal_exp hrate
        (sub_nonneg.mpr (hcarrier_time a ha.2))
    _ = ∫⁻ a in B ∩ carrier,
        terminalSurvivalDensity rate horizon time carrier a ∂μ := by
      apply MeasureTheory.setLIntegral_congr_fun (hB.inter hcarrier)
      intro a ha
      simp [terminalSurvivalDensity, ha.2]
    _ = ∫⁻ a in B,
        terminalSurvivalDensity rate horizon time carrier a ∂μ := by
      rw [← MeasureTheory.lintegral_indicator (hB.inter hcarrier),
        ← MeasureTheory.lintegral_indicator hB]
      apply lintegral_congr
      intro a
      by_cases haB : a ∈ B <;> by_cases haC : a ∈ carrier <;>
        simp [haB, haC, terminalSurvivalDensity]
    _ = (μ.withDensity (terminalSurvivalDensity rate horizon time carrier)) B := by
      exact (MeasureTheory.withDensity_apply _ hB).symm

/-- A finite iid exponential-gap product law has its explicit product density. -/
theorem pi_expMeasure_eq_withDensity_exponentialBlock
    {rate : ℝ} (hrate : 0 < rate) : ∀ q : ℕ,
      Measure.pi (fun _ : Fin q => expMeasure rate) =
        (volume : Measure (Fin q → ℝ)).withDensity
          (exponentialBlockDensity rate q) := by
  intro q
  letI : ∀ i : Fin q, IsProbabilityMeasure (expMeasure rate) :=
    fun _ => isProbabilityMeasure_expMeasure hrate
  induction q with
  | zero =>
      let e := MeasurableEquiv.ofUniqueOfUnique (Fin 0 → ℝ) Unit
      have hdens : exponentialBlockDensity rate 0 = 1 := by
        funext x
        simp [exponentialBlockDensity]
      apply e.map_measurableEquiv_injective
      rw [hdens, withDensity_one, volume_pi]
      exact
        ((MeasureTheory.measurePreserving_pi_empty
          (fun _ : Fin 0 => expMeasure rate)).map_eq).trans
          ((MeasureTheory.measurePreserving_pi_empty
            (fun _ : Fin 0 => (volume : Measure ℝ))).map_eq).symm
  | succ q ih =>
      let e := MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (q + 1) => ℝ) (Fin.last q)
      let g : ℝ × (Fin q → ℝ) → ℝ≥0∞ := fun p =>
        exponentialPDF rate p.1 * exponentialBlockDensity rate q p.2
      have hg : Measurable g := by
        exact ((measurable_exponentialPDF rate).comp measurable_fst).mul
          ((measurable_exponentialBlockDensity rate q).comp measurable_snd)
      have hdens : exponentialBlockDensity rate (q + 1) = g ∘ e := by
        funext x
        dsimp [exponentialBlockDensity, g, Function.comp_apply, e]
        rw [Fin.prod_univ_succAbove
          (fun i : Fin (q + 1) => exponentialPDF rate (x i)) (Fin.last q)]
        apply congrArg (fun z => exponentialPDF rate (x (Fin.last q)) * z)
        apply Finset.prod_congr rfl
        intro i _hi
        congr 1
      apply e.map_measurableEquiv_injective
      calc
        Measure.map e (Measure.pi (fun _ : Fin (q + 1) => expMeasure rate)) =
            (expMeasure rate).prod (Measure.pi (fun _ : Fin q => expMeasure rate)) := by
          simpa [e, Fin.succAbove_last] using
            (MeasureTheory.measurePreserving_piFinSuccAbove
              (fun _ : Fin (q + 1) => expMeasure rate) (Fin.last q)).map_eq
        _ = (volume.prod volume).withDensity g := by
          rw [ih]
          change (volume.withDensity (exponentialPDF rate)).prod
              (volume.withDensity (exponentialBlockDensity rate q)) = _
          rw [MeasureTheory.prod_withDensity (measurable_exponentialPDF rate)
            (measurable_exponentialBlockDensity rate q)]
        _ = Measure.map e ((volume : Measure (Fin (q + 1) → ℝ)).withDensity
            (exponentialBlockDensity rate (q + 1))) := by
          rw [hdens]
          symm
          exact map_withDensity_comp_of_measurePreserving
            (MeasureTheory.volume_preserving_piFinSuccAbove
              (fun _ : Fin (q + 1) => ℝ) (Fin.last q)) g hg

/--
The finite cumulative-arrival vector of iid exponential gaps has an explicit
Lebesgue density: pull the gap-product density back through the inverse
cumulative-sum linear equivalence.
-/
theorem map_cumulativeArrivalVector_pi_expMeasure_eq_withDensity
    {rate : ℝ} (hrate : 0 < rate) (q : ℕ) :
    Measure.map (cumulativeArrivalVector q)
      (Measure.pi (fun _ : Fin q => expMeasure rate)) =
      (volume : Measure (Fin q → ℝ)).withDensity
        (exponentialBlockDensity rate q ∘ (cumulativeArrivalLinearEquiv q).symm) := by
  let g : (Fin q → ℝ) → ℝ≥0∞ :=
    exponentialBlockDensity rate q ∘ (cumulativeArrivalLinearEquiv q).symm
  have hg : Measurable g := by
    exact (measurable_exponentialBlockDensity rate q).comp
      (measurable_cumulativeArrivalLinearEquiv_symm q)
  have hdens : exponentialBlockDensity rate q =
      g ∘ cumulativeArrivalLinearMap q := by
    funext x
    change exponentialBlockDensity rate q x =
      exponentialBlockDensity rate q
        ((cumulativeArrivalLinearEquiv q).symm (cumulativeArrivalLinearMap q x))
    congr 1
    change x = (cumulativeArrivalLinearEquiv q).symm
      (cumulativeArrivalLinearEquiv q x)
    exact ((cumulativeArrivalLinearEquiv q).symm_apply_apply x).symm
  have hcoord : cumulativeArrivalVector q = cumulativeArrivalLinearMap q := by
    funext x
    exact (cumulativeArrivalLinearMap_apply q x).symm
  change Measure.map (cumulativeArrivalVector q)
      (Measure.pi (fun _ : Fin q => expMeasure rate)) =
      (volume : Measure (Fin q → ℝ)).withDensity g
  rw [hcoord]
  calc
    Measure.map (cumulativeArrivalLinearMap q)
        (Measure.pi (fun _ : Fin q => expMeasure rate)) =
        Measure.map (cumulativeArrivalLinearMap q)
          ((volume : Measure (Fin q → ℝ)).withDensity
            (exponentialBlockDensity rate q)) := by
      rw [pi_expMeasure_eq_withDensity_exponentialBlock hrate q]
    _ = Measure.map (cumulativeArrivalLinearMap q)
        ((volume : Measure (Fin q → ℝ)).withDensity
          (g ∘ cumulativeArrivalLinearMap q)) := by
      rw [hdens]
    _ = (volume : Measure (Fin q → ℝ)).withDensity g :=
      map_withDensity_comp_of_measurePreserving
        (cumulativeArrivalLinearMap_volume_preserving q) g hg

/-- The total duration of a finite block of gaps. -/
def finiteGapPrefixTime (m : ℕ) : (Fin m → ℝ) → ℝ :=
  fun gaps => ∑ i, gaps i

/-- Nonnegative finite gaps whose total duration lies before a fixed horizon. -/
def finiteGapPrefixCarrier (m : ℕ) (horizon : ℝ) : Set (Fin m → ℝ) :=
  {gaps | (∀ i, 0 ≤ gaps i) ∧ finiteGapPrefixTime m gaps ≤ horizon}

theorem measurable_finiteGapPrefixTime (m : ℕ) :
    Measurable (finiteGapPrefixTime m) := by
  unfold finiteGapPrefixTime
  exact Finset.univ.measurable_sum fun i _hi => measurable_pi_apply i

theorem measurableSet_finiteGapPrefixCarrier (m : ℕ) (horizon : ℝ) :
    MeasurableSet (finiteGapPrefixCarrier m horizon) := by
  have hnonneg : MeasurableSet {gaps : Fin m → ℝ | ∀ i, 0 ≤ gaps i} := by
    rw [show {gaps : Fin m → ℝ | ∀ i, 0 ≤ gaps i} =
        ⋂ i : Fin m, {gaps : Fin m → ℝ | 0 ≤ gaps i} by
      ext gaps
      simp]
    refine MeasurableSet.iInter fun i => ?_
    exact measurableSet_le measurable_const (measurable_pi_apply i)
  exact hnonneg.inter
    (measurableSet_le (measurable_finiteGapPrefixTime m) measurable_const)

theorem finiteGapPrefixTime_le_of_mem
    {m : ℕ} {horizon : ℝ} {gaps : Fin m → ℝ}
    (hmem : gaps ∈ finiteGapPrefixCarrier m horizon) :
    finiteGapPrefixTime m gaps ≤ horizon :=
  hmem.2

private theorem cumulativeArrivalVector_last_eq_finiteGapPrefixTime
    (n : ℕ) (gaps : Fin (n + 1) → ℝ) :
    cumulativeArrivalVector (n + 1) gaps (Fin.last n) =
      finiteGapPrefixTime (n + 1) gaps := by
  simp only [cumulativeArrivalVector, finiteGapPrefixTime]
  rw [← Finset.sum_subtype (Finset.univ : Finset (Fin (n + 1)))
    (by intro i; simp [Fin.le_last i]) gaps]

private theorem cumulativeArrivalVector_castSucc_apply
    (n : ℕ) (gaps : Fin (n + 1) → ℝ) (i : Fin n) :
    cumulativeArrivalVector (n + 1) gaps i.castSucc =
      cumulativeArrivalVector n (fun j => gaps j.castSucc) i := by
  simp only [cumulativeArrivalVector]
  let e : {j : Fin n // j ≤ i} ≃ {j : Fin (n + 1) // j ≤ i.castSucc} :=
    { toFun := fun j => ⟨j.1.castSucc, Fin.castSucc_le_castSucc_iff.mpr j.2⟩
      invFun := fun j =>
        ⟨j.1.castLT (lt_of_le_of_lt j.2 i.isLt), by
          simpa using j.2⟩
      left_inv := by
        intro j
        apply Subtype.ext
        simp
      right_inv := by
        intro j
        apply Subtype.ext
        simp }
  symm
  refine Fintype.sum_equiv e (fun j => gaps j.1.castSucc) (fun j => gaps j.1) ?_
  intro j
  simp [e]

/--
Cumulative summation maps a finite nonnegative-gap carrier with total duration
at most a nonnegative horizon exactly onto the closed ordered arrival region.
-/
theorem cumulativeArrivalVector_mem_orderedJumpRegion_iff_mem_finiteGapPrefixCarrier
    {m : ℕ} {horizon : ℝ} {gaps : Fin m → ℝ}
    (horizon_nonneg : 0 ≤ horizon) :
    cumulativeArrivalVector m gaps ∈ orderedJumpRegion m horizon ↔
      gaps ∈ finiteGapPrefixCarrier m horizon := by
  induction m generalizing horizon with
  | zero =>
      simp [orderedJumpRegion, finiteGapPrefixCarrier, finiteGapPrefixTime,
        horizon_nonneg]
  | succ n ih =>
      let preGaps : Fin n → ℝ := fun i => gaps i.castSucc
      let totalTime : ℝ := ∑ i, gaps i
      have hlast : cumulativeArrivalVector (n + 1) gaps (Fin.last n) = totalTime := by
        simpa [totalTime] using cumulativeArrivalVector_last_eq_finiteGapPrefixTime n gaps
      have hprefix :
          (fun i : Fin n => cumulativeArrivalVector (n + 1) gaps i.castSucc) =
            cumulativeArrivalVector n preGaps := by
        funext i
        exact cumulativeArrivalVector_castSucc_apply n gaps i
      rw [orderedJumpRegion_succ_mem_iff, hlast, hprefix]
      constructor
      · rintro ⟨htotal, hprefix_mem⟩
        have hprefix_carrier : preGaps ∈ finiteGapPrefixCarrier n totalTime :=
          (ih htotal.1).mp hprefix_mem
        change (∀ i : Fin (n + 1), 0 ≤ gaps i) ∧ totalTime ≤ horizon
        constructor
        · intro i
          by_cases hi : i = Fin.last n
          · subst i
            have hsplit : totalTime =
                (∑ j : Fin n, preGaps j) + gaps (Fin.last n) := by
              simp [totalTime, preGaps, Fin.sum_univ_castSucc]
            change (∀ j : Fin n, 0 ≤ preGaps j) ∧
              (∑ j : Fin n, preGaps j) ≤ totalTime at hprefix_carrier
            linarith [hprefix_carrier.2]
          · have hilt : i < Fin.last n :=
              lt_of_le_of_ne (Fin.le_last i) hi
            let j : Fin n := i.castLT hilt
            have hjcast : j.castSucc = i := by
              apply Fin.ext
              simp [j]
            change (∀ j : Fin n, 0 ≤ preGaps j) ∧
              (∑ j : Fin n, preGaps j) ≤ totalTime at hprefix_carrier
            simpa [preGaps, hjcast] using hprefix_carrier.1 j
        · exact htotal.2
      · rintro ⟨hnonneg, hupper⟩
        have htotal_nonneg : 0 ≤ totalTime := by
          dsimp [totalTime]
          exact Finset.sum_nonneg fun i _ => hnonneg i
        refine ⟨⟨htotal_nonneg, hupper⟩, ?_⟩
        apply (ih htotal_nonneg).mpr
        change (∀ i : Fin n, 0 ≤ preGaps i) ∧
          (∑ i : Fin n, preGaps i) ≤ totalTime
        constructor
        · intro i
          exact hnonneg i.castSucc
        · have hsplit : totalTime =
              (∑ j : Fin n, preGaps j) + gaps (Fin.last n) := by
            simp [totalTime, preGaps, Fin.sum_univ_castSucc]
          linarith [hnonneg (Fin.last n)]

/--
The inverse cumulative-arrival equivalence pulls the finite gap carrier back
from the ordered arrival-epoch region.
-/
theorem cumulativeArrivalLinearEquiv_symm_mem_finiteGapPrefixCarrier_iff
    {m : ℕ} {horizon : ℝ} {epochs : Fin m → ℝ}
    (horizon_nonneg : 0 ≤ horizon) :
    (cumulativeArrivalLinearEquiv m).symm epochs ∈
        finiteGapPrefixCarrier m horizon ↔
      epochs ∈ orderedJumpRegion m horizon := by
  have h := (cumulativeArrivalVector_mem_orderedJumpRegion_iff_mem_finiteGapPrefixCarrier
    (gaps := (cumulativeArrivalLinearEquiv m).symm epochs) horizon_nonneg).symm
  have hcoord :
      cumulativeArrivalVector m ((cumulativeArrivalLinearEquiv m).symm epochs) =
        epochs := by
    calc
      cumulativeArrivalVector m ((cumulativeArrivalLinearEquiv m).symm epochs) =
          cumulativeArrivalLinearMap m ((cumulativeArrivalLinearEquiv m).symm epochs) :=
        (cumulativeArrivalLinearMap_apply m _).symm
      _ = cumulativeArrivalLinearEquiv m ((cumulativeArrivalLinearEquiv m).symm epochs) :=
        rfl
      _ = epochs := (cumulativeArrivalLinearEquiv m).apply_symm_apply epochs
  rw [hcoord] at h
  exact h

/--
The exact finite-arrival density before a deterministic horizon, written in
cumulative-arrival coordinates.  The inverse cumulative map recovers the
gaps, whose product density is multiplied by terminal exponential survival.
-/
def finiteArrivalTerminalDensity (rate horizon : ℝ) (m : ℕ) :
    (Fin m → ℝ) → ℝ≥0∞ :=
  fun epochs =>
    let gaps := (cumulativeArrivalLinearEquiv m).symm epochs
    exponentialBlockDensity rate m gaps *
      terminalSurvivalDensity rate horizon (finiteGapPrefixTime m)
        (finiteGapPrefixCarrier m horizon) gaps

theorem measurable_finiteArrivalTerminalDensity (rate horizon : ℝ) (m : ℕ) :
    Measurable (finiteArrivalTerminalDensity rate horizon m) := by
  unfold finiteArrivalTerminalDensity
  exact ((measurable_exponentialBlockDensity rate m).comp
    (measurable_cumulativeArrivalLinearEquiv_symm m)).mul
    ((measurable_terminalSurvivalDensity rate horizon
      (measurable_finiteGapPrefixTime m)
      (measurableSet_finiteGapPrefixCarrier m horizon)).comp
      (measurable_cumulativeArrivalLinearEquiv_symm m))

/--
The finite vector of cumulative iid exponential gaps, restricted to a terminal
survival gap, has an actual Lebesgue density in cumulative-arrival coordinates.
This is the arbitrary finite-count measure-level bridge underlying ordered
Poisson arrival likelihoods.
-/
theorem map_cumulativeArrival_finiteTerminal_eq_withDensity
    {rate horizon : ℝ} (hrate : 0 < rate) (m : ℕ) :
    Measure.map (fun p : (Fin m → ℝ) × ℝ => cumulativeArrivalVector m p.1)
      (((Measure.pi (fun _ : Fin m => expMeasure rate)).prod (expMeasure rate)).restrict
        (terminalSurvivalEvent (finiteGapPrefixTime m)
          (finiteGapPrefixCarrier m horizon) horizon)) =
      (volume : Measure (Fin m → ℝ)).withDensity
        (finiteArrivalTerminalDensity rate horizon m) := by
  let μ : Measure (Fin m → ℝ) := Measure.pi (fun _ : Fin m => expMeasure rate)
  letI : ∀ i : Fin m, IsProbabilityMeasure (expMeasure rate) :=
    fun _ => isProbabilityMeasure_expMeasure hrate
  let tail : (Fin m → ℝ) → ℝ≥0∞ :=
    terminalSurvivalDensity rate horizon (finiteGapPrefixTime m)
      (finiteGapPrefixCarrier m horizon)
  have htail : Measurable tail := by
    exact measurable_terminalSurvivalDensity rate horizon
      (measurable_finiteGapPrefixTime m)
      (measurableSet_finiteGapPrefixCarrier m horizon)
  have hterminal :
      Measure.map Prod.fst ((μ.prod (expMeasure rate)).restrict
        (terminalSurvivalEvent (finiteGapPrefixTime m)
          (finiteGapPrefixCarrier m horizon) horizon)) =
        μ.withDensity tail := by
    exact map_fst_restrict_terminalSurvivalEvent_eq_withDensity hrate
      (finiteGapPrefixTime m) (finiteGapPrefixCarrier m horizon)
      (measurable_finiteGapPrefixTime m)
      (measurableSet_finiteGapPrefixCarrier m horizon)
      (fun gaps hmem => finiteGapPrefixTime_le_of_mem hmem)
  have hcoord : cumulativeArrivalVector m = cumulativeArrivalLinearMap m := by
    funext gaps
    exact (cumulativeArrivalLinearMap_apply m gaps).symm
  have hdens :
      (fun gaps : Fin m → ℝ => exponentialBlockDensity rate m gaps * tail gaps) =
        finiteArrivalTerminalDensity rate horizon m ∘ cumulativeArrivalLinearMap m := by
    funext gaps
    change exponentialBlockDensity rate m gaps * tail gaps =
      exponentialBlockDensity rate m
          ((cumulativeArrivalLinearEquiv m).symm (cumulativeArrivalLinearMap m gaps)) *
        tail ((cumulativeArrivalLinearEquiv m).symm (cumulativeArrivalLinearMap m gaps))
    have hinv : (cumulativeArrivalLinearEquiv m).symm
        (cumulativeArrivalLinearMap m gaps) = gaps := by
      change (cumulativeArrivalLinearEquiv m).symm
        (cumulativeArrivalLinearEquiv m gaps) = gaps
      exact (cumulativeArrivalLinearEquiv m).symm_apply_apply gaps
    rw [hinv]
  have hfinal : Measurable (finiteArrivalTerminalDensity rate horizon m) :=
    measurable_finiteArrivalTerminalDensity rate horizon m
  have hdens' : exponentialBlockDensity rate m * tail =
      finiteArrivalTerminalDensity rate horizon m ∘ cumulativeArrivalLinearMap m := by
    simpa only [Pi.mul_apply] using hdens
  change Measure.map (fun p : (Fin m → ℝ) × ℝ => cumulativeArrivalVector m p.1)
      ((μ.prod (expMeasure rate)).restrict
        (terminalSurvivalEvent (finiteGapPrefixTime m)
          (finiteGapPrefixCarrier m horizon) horizon)) =
      (volume : Measure (Fin m → ℝ)).withDensity
        (finiteArrivalTerminalDensity rate horizon m)
  calc
    Measure.map (fun p : (Fin m → ℝ) × ℝ => cumulativeArrivalVector m p.1)
        ((μ.prod (expMeasure rate)).restrict
          (terminalSurvivalEvent (finiteGapPrefixTime m)
            (finiteGapPrefixCarrier m horizon) horizon)) =
        Measure.map (cumulativeArrivalLinearMap m)
          (Measure.map Prod.fst ((μ.prod (expMeasure rate)).restrict
            (terminalSurvivalEvent (finiteGapPrefixTime m)
              (finiteGapPrefixCarrier m horizon) horizon))) := by
      rw [hcoord]
      simpa [Function.comp_def] using
        (Measure.map_map
          (LinearMap.continuous_on_pi (cumulativeArrivalLinearMap m)).measurable
          measurable_fst).symm
    _ = Measure.map (cumulativeArrivalLinearMap m) (μ.withDensity tail) := by
      rw [hterminal]
    _ = Measure.map (cumulativeArrivalLinearMap m)
        ((volume : Measure (Fin m → ℝ)).withDensity
          (exponentialBlockDensity rate m * tail)) := by
      rw [show μ = (volume : Measure (Fin m → ℝ)).withDensity
        (exponentialBlockDensity rate m) by
        exact pi_expMeasure_eq_withDensity_exponentialBlock hrate m]
      rw [← MeasureTheory.withDensity_mul volume
        (measurable_exponentialBlockDensity rate m) htail]
    _ = Measure.map (cumulativeArrivalLinearMap m)
        ((volume : Measure (Fin m → ℝ)).withDensity
          (finiteArrivalTerminalDensity rate horizon m ∘ cumulativeArrivalLinearMap m)) := by
      rw [hdens']
    _ = (volume : Measure (Fin m → ℝ)).withDensity
        (finiteArrivalTerminalDensity rate horizon m) :=
      map_withDensity_comp_of_measurePreserving
        (cumulativeArrivalLinearMap_volume_preserving m)
        (finiteArrivalTerminalDensity rate horizon m) hfinal

end

end AppliedModelingLib.Probability.PoissonProcess
