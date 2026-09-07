import PG24NoisyMatchingMarkets.Theorem1DenseCaseAnalytic
import PG24NoisyMatchingMarkets.Theorem1LiteralSelectedCutoffBridge
import PG24NoisyMatchingMarkets.Theorem2HolderNoAtoms
import Mathlib.Tactic

/-!
# PG24 Theorem 1 literal dense-branch source route

This module instantiates the dense-cutoff branch directly at the literal
selected demand rule.  The value-window estimate is derived from the source
Holder witness, and the analytic split handles either ordering of the dense
transition and the supply threshold.
-/

open Filter Topology MeasureTheory
open AppliedModelingLib.Matching

namespace PG24NoisyMatchingMarkets

noncomputable section

universe u v

/--
The source Holder witness controls the closed three-radius transition window
after enlarging it to an open five-radius interval.  The enlargement avoids
silently discarding endpoint atoms.
-/
theorem theorem1_holder_middle_window_mass_le
    (eta : Measure ℝ) [IsFiniteMeasure eta]
    {holderConstant gamma pivot center radius : ℝ}
    (hholder : ∀ (x delta : ℝ), 0 < delta →
      eta.real (Set.Ioo x (x + delta)) ≤
        holderConstant * Real.rpow delta gamma)
    (hradius_pos : 0 < radius) :
    eta.real (Set.Icc (pivot - center - radius)
      (pivot - center + 2 * radius)) ≤
      holderConstant * Real.rpow (5 * radius) gamma := by
  have hsubset : Set.Icc (pivot - center - radius)
      (pivot - center + 2 * radius) ⊆
      Set.Ioo (pivot - center - 2 * radius)
        ((pivot - center - 2 * radius) + 5 * radius) := by
    intro value hvalue
    constructor <;> linarith [hvalue.1, hvalue.2]
  calc
    eta.real (Set.Icc (pivot - center - radius)
        (pivot - center + 2 * radius)) ≤
        eta.real (Set.Ioo (pivot - center - 2 * radius)
          ((pivot - center - 2 * radius) + 5 * radius)) :=
      MeasureTheory.measureReal_mono hsubset (by finiteness)
    _ ≤ holderConstant * Real.rpow (5 * radius) gamma :=
      hholder (pivot - center - 2 * radius) (5 * radius) (by positivity)

/--
The analytic dense-branch bound does not require the transition's high
endpoint to lie below the supply threshold.  Above the threshold, the usual
capacity budget applies; when the transition is already above it, the Holder
middle interval alone covers the remaining low tail.
-/
theorem theorem1_low_affordance_integral_le_of_analytic_primitives_any_highPivot
    (valueLaw : Measure ℝ) [IsProbabilityMeasure valueLaw]
    (p : ℝ → ℝ) (hp : Integrable p valueLaw)
    {totalSupply lowError highError middleMass lowPivot highPivot vS : ℝ}
    (hp_nonneg : ∀ value, 0 ≤ p value)
    (hp_le_one : ∀ value, p value ≤ 1)
    (hlow_error_nonneg : 0 ≤ lowError)
    (hhigh_error_nonneg : 0 ≤ highError)
    (hhigh_error_le_half : highError ≤ 1 / 2)
    (hlow_high : lowPivot ≤ highPivot)
    (hlow_match : ∀ value ∈ Set.Iio lowPivot, p value ≤ lowError)
    (hhigh_match : ∀ value ∈ Set.Ioi highPivot, 1 - highError ≤ p value)
    (htotal : (∫ value, p value ∂valueLaw) ≤ totalSupply)
    (htail_normalization : valueLaw.real (Set.Ioi vS) = totalSupply)
    (hmiddle : valueLaw.real (Set.Icc lowPivot highPivot) ≤ middleMass) :
    (∫ value : ℝ, (Set.Iic vS).indicator p value ∂valueLaw) ≤
      lowError + middleMass + 2 * totalSupply * highError := by
  by_cases hhigh_vS : highPivot ≤ vS
  · exact theorem1_low_affordance_integral_le_of_analytic_primitives
      valueLaw p hp hp_nonneg hp_le_one hlow_error_nonneg hhigh_error_nonneg
      hhigh_error_le_half hlow_high hhigh_vS hlow_match hhigh_match htotal
      htail_normalization hmiddle
  · have hvS_high : vS ≤ highPivot := le_of_lt (lt_of_not_ge hhigh_vS)
    have hlow_integral :
        (∫ value in Set.Iio lowPivot, p value ∂valueLaw) ≤ lowError := by
      calc
        (∫ value in Set.Iio lowPivot, p value ∂valueLaw) ≤
            valueLaw.real (Set.Iio lowPivot) * lowError :=
          theorem1_setIntegral_le_measureReal_mul_of_pointwise_le
            valueLaw p hp measurableSet_Iio hlow_match
        _ ≤ lowError := by
          have hmass : valueLaw.real (Set.Iio lowPivot) ≤ 1 :=
            measureReal_le_one (μ := valueLaw)
          nlinarith
    have hmiddle_integral :
        (∫ value in Set.Icc lowPivot highPivot, p value ∂valueLaw) ≤ middleMass := by
      calc
        (∫ value in Set.Icc lowPivot highPivot, p value ∂valueLaw) ≤
            valueLaw.real (Set.Icc lowPivot highPivot) :=
          theorem1_setIntegral_le_measureReal_of_le_one
            valueLaw p hp measurableSet_Icc (fun value _ => hp_le_one value)
        _ ≤ middleMass := hmiddle
    have hrestrict :
        (∫ value in Set.Iic vS, p value ∂valueLaw) ≤
          ∫ value in Set.Iic highPivot, p value ∂valueLaw :=
      setIntegral_mono_set hp.integrableOn
        (ae_of_all (valueLaw.restrict (Set.Iic highPivot)) hp_nonneg)
        (Set.Iic_subset_Iic.mpr hvS_high).eventuallyLE
    have hhigh_decomposition :
        (∫ value in Set.Iic highPivot, p value ∂valueLaw) =
          (∫ value in Set.Iio lowPivot, p value ∂valueLaw) +
            ∫ value in Set.Icc lowPivot highPivot, p value ∂valueLaw := by
      have hsplit := theorem1_setIntegral_Iic_eq_low_middle_high
        valueLaw p hp hlow_high le_rfl
      simpa using hsplit
    have htotal_nonneg : 0 ≤ totalSupply := by
      have hintegral_nonneg : 0 ≤ ∫ value, p value ∂valueLaw :=
        integral_nonneg hp_nonneg
      exact hintegral_nonneg.trans htotal
    rw [integral_indicator measurableSet_Iic]
    calc
      (∫ value in Set.Iic vS, p value ∂valueLaw) ≤
          ∫ value in Set.Iic highPivot, p value ∂valueLaw := hrestrict
      _ = (∫ value in Set.Iio lowPivot, p value ∂valueLaw) +
            ∫ value in Set.Icc lowPivot highPivot, p value ∂valueLaw :=
          hhigh_decomposition
      _ ≤ lowError + middleMass := add_le_add hlow_integral hmiddle_integral
      _ ≤ lowError + middleMass + 2 * totalSupply * highError := by
          have htail_nonneg : 0 ≤ 2 * totalSupply * highError := by
            exact mul_nonneg (mul_nonneg (by norm_num) htotal_nonneg)
              hhigh_error_nonneg
          linarith

/--
At the literal selected cutoff, a canonical ranked dense window supplies all
of the dense-branch analytic primitives.  In particular, the dense block,
its cardinality, and the full-capacity identity are derived from the literal
source model rather than supplied as a selector certificate.
-/
theorem theorem1_literal_dense_upper_low_integral_le_of_ranked_window
    {StudentType : Type u} [MeasurableSpace StudentType]
    {Cutoff : Type v} {C : ℕ}
    (noiseLaw eta : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {totalSupply alpha beta gamma holderConstant vS : ℝ}
    (inst : PG24LiteralBasicTwoScaleInstance C noiseLaw eta totalSupply alpha
      StudentType Cutoff)
    (hholder : ∀ (x delta : ℝ), 0 < delta →
      eta.real (Set.Ioo x (x + delta)) ≤
        holderConstant * Real.rpow delta gamma)
    (hC_pos : 0 < C)
    (start : ℕ)
    (hterminal : start + theorem3DenseWindowCount C
        (theorem1TailPhi2 beta gamma) ≤ C)
    (hdense : theorem1TailDenseRankWindow
      (theorem3RankedCutoffNat C inst.selectedCutoffVector) start
      (theorem3DenseWindowCount C (theorem1TailPhi2 beta gamma))
      (theorem1DenseDeviationRadius C beta gamma))
    (hradius_le_half :
      AppliedModelingLib.Matching.topOrderDeviationProbability
          (Measure.pi (fun _ : Fin
            (theorem1DenseGroupIndex C beta gamma + 1) => noiseLaw))
          (theorem1DenseGroupCenter noiseLaw C beta gamma)
          (theorem1DenseDeviationRadius C beta gamma) ≤ 1 / 2)
    (htail_normalization : eta.real (Set.Ioi vS) = totalSupply) :
    (∫ value : ℝ,
      (Set.Iic vS).indicator
        (fun value => cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (theorem1CutoffAtOrAboveBlock
            (Finset.univ : Finset (Fin (C + 1))) inst.selectedCutoffVector
            (theorem3RankedCutoffNat C inst.selectedCutoffVector start))
          value inst.selectedCutoffVector) value
      ∂eta) ≤
        (theorem1IntegerGroupCount
        (theorem1CutoffAtOrAboveBlock
          (Finset.univ : Finset (Fin (C + 1))) inst.selectedCutoffVector
          (theorem3RankedCutoffNat C inst.selectedCutoffVector start))
        (theorem1DenseGroupIndex C beta gamma + 1) : ℝ) *
        AppliedModelingLib.Matching.topOrderDeviationProbability
          (Measure.pi (fun _ : Fin
            (theorem1DenseGroupIndex C beta gamma + 1) => noiseLaw))
          (theorem1DenseGroupCenter noiseLaw C beta gamma)
          (theorem1DenseDeviationRadius C beta gamma) +
        holderConstant *
          Real.rpow (5 * theorem1DenseDeviationRadius C beta gamma) gamma +
        2 * totalSupply *
          AppliedModelingLib.Matching.topOrderDeviationProbability
            (Measure.pi (fun _ : Fin
              (theorem1DenseGroupIndex C beta gamma + 1) => noiseLaw))
            (theorem1DenseGroupCenter noiseLaw C beta gamma)
            (theorem1DenseDeviationRadius C beta gamma) := by
  classical
  letI : IsProbabilityMeasure inst.studentLaw := inst.studentLaw_isProbability
  letI : IsProbabilityMeasure eta := by
    rw [← inst.value_marginal]
    exact Measure.isProbabilityMeasure_map inst.value_measurable.aemeasurable
  let m : ℕ := theorem1DenseGroupIndex C beta gamma + 1
  let pivot : ℝ := theorem3RankedCutoffNat C inst.selectedCutoffVector start
  let radius : ℝ := theorem1DenseDeviationRadius C beta gamma
  let center : ℝ := theorem1DenseGroupCenter noiseLaw C beta gamma
  let upper : Finset (Fin (C + 1)) := theorem1CutoffAtOrAboveBlock
    Finset.univ inst.selectedCutoffVector pivot
  let dense : Finset (Fin (C + 1)) := theorem1CutoffWindowBlock
    Finset.univ inst.selectedCutoffVector pivot radius
  let error : ℝ := AppliedModelingLib.Matching.topOrderDeviationProbability
    (Measure.pi (fun _ : Fin m => noiseLaw)) center radius
  have hm_pos : 0 < m := by
    dsimp [m]
    exact Nat.zero_lt_succ _
  have hsize_eq : theorem1DenseGroupSize C beta gamma =
      theorem3DenseWindowCount C (theorem1TailPhi2 beta gamma) := by
    unfold theorem1DenseGroupSize theorem3DenseWindowCount
    exact Nat.max_eq_right (Nat.one_le_iff_ne_zero.mpr
      (Nat.ne_of_gt (by
        rw [Nat.ceil_pos]
        exact Real.rpow_pos_of_pos (by exact_mod_cast hC_pos) _)))
  have hm_eq : m = theorem3DenseWindowCount C (theorem1TailPhi2 beta gamma) := by
    dsimp [m]
    rw [theorem1DenseGroupIndex_add_one C beta gamma]
    exact hsize_eq
  have hradius_pos : 0 < radius := by
    dsimp [radius, theorem1DenseDeviationRadius]
    exact Real.rpow_pos_of_pos (by exact_mod_cast hC_pos) _
  have hdense_card : m ≤ dense.card := by
    have hwindow := theorem1CutoffWindowBlock_card_ge_of_rankedDenseWindow
      C start (theorem3DenseWindowCount C (theorem1TailPhi2 beta gamma))
      inst.selectedCutoffVector radius hterminal hdense
    rw [hm_eq]
    exact le_trans (Nat.le_succ _) (by simpa [dense] using hwindow)
  have hdense_subset : dense ⊆ upper := by
    simpa [dense, upper] using
      (theorem1CutoffWindowBlock_subset_atOrAboveBlock
        (Finset.univ : Finset (Fin (C + 1))) inst.selectedCutoffVector pivot radius)
  have hdense_upper : ∀ college ∈ dense,
      inst.selectedCutoffVector college ≤ pivot + radius := by
    intro college hcollege
    exact (Finset.mem_filter.mp hcollege).2.2
  have hfull_capacity :
      (∫ value : ℝ,
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (Finset.univ : Finset (Fin (C + 1))) value
          inst.selectedCutoffVector ∂eta) = totalSupply :=
    inst.theorem1_selected_full_affordance_integral_eq_totalSupply
  have hlow_separation : ∀ value ∈ Set.Iio (pivot - center - radius),
      center + radius ≤ pivot - value := by
    intro value hvalue
    change value < pivot - center - radius at hvalue
    linarith
  have hhigh_separation : ∀ value ∈ Set.Ioi (pivot - center + 2 * radius),
      pivot + radius - value < center - radius := by
    intro value hvalue
    change pivot - center + 2 * radius < value at hvalue
    linarith
  have hlow_high : pivot - center - radius ≤ pivot - center + 2 * radius := by
    linarith
  have hmiddle : eta.real (Set.Icc (pivot - center - radius)
      (pivot - center + 2 * radius)) ≤
      holderConstant * Real.rpow (5 * radius) gamma :=
    theorem1_holder_middle_window_mass_le eta hholder hradius_pos
  let p : ℝ → ℝ := fun value => cutoffAffordanceProbability
    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)) upper value
      inst.selectedCutoffVector
  let fullP : ℝ → ℝ := fun value => cutoffAffordanceProbability
    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)) Finset.univ value
      inst.selectedCutoffVector
  have hp : Integrable p eta := by
    simpa [p, cutoffAffordanceProbability] using
      (AppliedModelingLib.Matching.cutoffCrossingProbability_integrable_value
        (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)) eta upper
        inst.selectedCutoffVector)
  have hfullP : Integrable fullP eta := by
    simpa [fullP, cutoffAffordanceProbability] using
      (AppliedModelingLib.Matching.cutoffCrossingProbability_integrable_value
        (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)) eta Finset.univ
        inst.selectedCutoffVector)
  have hp_nonneg : ∀ value, 0 ≤ p value := by
    intro value
    exact cutoffAffordanceProbability_nonneg
      (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)) upper value
      inst.selectedCutoffVector
  have hp_le_one : ∀ value, p value ≤ 1 := by
    intro value
    exact cutoffAffordanceProbability_le_one
      (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)) upper value
      inst.selectedCutoffVector
  have herror_nonneg : 0 ≤ error :=
    theorem1_iid_topOrderDeviationProbability_nonneg
      (m := m) noiseLaw center radius
  have hupper_le_full : ∀ value, p value ≤ fullP value := by
    intro value
    exact cutoffAffordanceProbability_mono_active
      (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)) (Finset.subset_univ upper)
  have htotal : (∫ value, p value ∂eta) ≤ totalSupply := by
    calc
      (∫ value, p value ∂eta) ≤ ∫ value, fullP value ∂eta :=
        integral_mono hp hfullP hupper_le_full
      _ = totalSupply := by simpa [fullP] using hfull_capacity
  have hlow_match : ∀ value ∈ Set.Iio (pivot - center - radius),
      p value ≤ (theorem1IntegerGroupCount upper m : ℝ) * error := by
    intro value hvalue
    simpa [p, upper, error] using
      (theorem1_iid_atOrAbove_affordance_le_integer_group_count_mul_deviation
        (m := m) noiseLaw (Finset.univ : Finset (Fin (C + 1)))
        inst.selectedCutoffVector pivot (hlow_separation value hvalue))
  have hhigh_match : ∀ value ∈ Set.Ioi (pivot - center + 2 * radius),
      1 - error ≤ p value := by
    intro value hvalue
    have hfailure := theorem1_one_sub_iid_cutoff_affordance_le_deviation_of_dense_card_ge
      (m := m) noiseLaw (cutoff := inst.selectedCutoffVector)
      hdense_subset hdense_card hdense_upper hradius_pos
      (hhigh_separation value hvalue)
    dsimp [p, upper, error]
    linarith
  have hclosed := theorem1_low_affordance_integral_le_of_analytic_primitives_any_highPivot
    eta p hp hp_nonneg hp_le_one
    (mul_nonneg (by exact_mod_cast (theorem1IntegerGroupCount upper m).zero_le)
      herror_nonneg)
    herror_nonneg (by simpa [error, center, radius, m] using hradius_le_half)
    hlow_high hlow_match hhigh_match htotal htail_normalization hmiddle
  simpa [p, upper, error, center, radius, pivot, m] using hclosed

/--
The literal selected matching mass in the dense branch is bounded by the
derived sparse-prefix capacity and the derived dense upper-block integral.
No choice-mass equality, pre-sorted college indexing, or separate block
selection witness is an input to this statement.
-/
theorem theorem1_literal_selected_dense_low_matched_mass_le_of_ranked_window
    {StudentType : Type u} [MeasurableSpace StudentType]
    {Cutoff : Type v} {C : ℕ}
    (noiseLaw eta : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {totalSupply alpha beta gamma holderConstant vS : ℝ}
    (inst : PG24LiteralBasicTwoScaleInstance C noiseLaw eta totalSupply alpha
      StudentType Cutoff)
    (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (halpha_nonneg : 0 ≤ alpha)
    (hholder : ∀ (x delta : ℝ), 0 < delta →
      eta.real (Set.Ioo x (x + delta)) ≤
        holderConstant * Real.rpow delta gamma)
    (hC_pos : 0 < C)
    (start : ℕ)
    (hstart_window : start + theorem3DenseWindowCount C
        (theorem1TailPhi2 beta gamma) ≤
        theorem3DenseGapBlockCount C
          (theorem1TailPhi2 beta gamma) (theorem1TailPhi3 beta gamma) *
          theorem3DenseWindowCount C (theorem1TailPhi2 beta gamma))
    (hdense : theorem1TailDenseRankWindow
      (theorem3RankedCutoffNat C inst.selectedCutoffVector) start
      (theorem3DenseWindowCount C (theorem1TailPhi2 beta gamma))
      (theorem1DenseDeviationRadius C beta gamma))
    (hradius_le_half :
      AppliedModelingLib.Matching.topOrderDeviationProbability
          (Measure.pi (fun _ : Fin
            (theorem1DenseGroupIndex C beta gamma + 1) => noiseLaw))
          (theorem1DenseGroupCenter noiseLaw C beta gamma)
          (theorem1DenseDeviationRadius C beta gamma) ≤ 1 / 2)
    (htail_normalization : eta.real (Set.Ioi vS) = totalSupply) :
    eventMass
        (inst.studentLaw.prod
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)))
        (fun outcome : StudentType × (Fin (C + 1) → ℝ) =>
          inst.value outcome.1 ∈ Set.Iic vS ∧
            chosenInActive
              (inst.literal.demand.demandAt inst.literal.selectedCutoff)
              (Finset.univ : Finset (Fin (C + 1))) outcome) ≤
      alpha * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)) +
        (theorem1IntegerGroupCount
          (theorem1CutoffAtOrAboveBlock
            (Finset.univ : Finset (Fin (C + 1))) inst.selectedCutoffVector
            (theorem3RankedCutoffNat C inst.selectedCutoffVector start))
          (theorem1DenseGroupIndex C beta gamma + 1) : ℝ) *
          AppliedModelingLib.Matching.topOrderDeviationProbability
            (Measure.pi (fun _ : Fin
              (theorem1DenseGroupIndex C beta gamma + 1) => noiseLaw))
            (theorem1DenseGroupCenter noiseLaw C beta gamma)
            (theorem1DenseDeviationRadius C beta gamma) +
          holderConstant *
            Real.rpow (5 * theorem1DenseDeviationRadius C beta gamma) gamma +
          2 * totalSupply *
            AppliedModelingLib.Matching.topOrderDeviationProbability
              (Measure.pi (fun _ : Fin
                (theorem1DenseGroupIndex C beta gamma + 1) => noiseLaw))
              (theorem1DenseGroupCenter noiseLaw C beta gamma)
              (theorem1DenseDeviationRadius C beta gamma) := by
  classical
  letI : IsProbabilityMeasure inst.studentLaw := inst.studentLaw_isProbability
  letI : IsProbabilityMeasure eta := by
    rw [← inst.value_marginal]
    exact Measure.isProbabilityMeasure_map inst.value_measurable.aemeasurable
  let stride : ℕ := theorem3DenseWindowCount C (theorem1TailPhi2 beta gamma)
  let earlyRank : ℕ := theorem3EarlyPrefixRank C (theorem1TailPhi3 beta gamma)
  have hblocks_prefix :
      theorem3DenseGapBlockCount C
          (theorem1TailPhi2 beta gamma) (theorem1TailPhi3 beta gamma) *
          stride ≤ earlyRank := by
    dsimp [stride, earlyRank]
    exact theorem3DenseGapBlockCount_mul_denseWindowCount_le_earlyPrefixRank
      C (theorem1TailPhi2 beta gamma) (theorem1TailPhi3 beta gamma)
  have hstart_earlyRank : start ≤ earlyRank := by
    calc
      start ≤ start + stride := Nat.le_add_right _ _
      _ ≤ theorem3DenseGapBlockCount C
            (theorem1TailPhi2 beta gamma) (theorem1TailPhi3 beta gamma) *
            stride := by simpa [stride] using hstart_window
      _ ≤ earlyRank := hblocks_prefix
  have hearlyRank_market : earlyRank ≤ C := by
    dsimp [earlyRank]
    exact theorem1EarlyPrefixRank_le_marketIndex hbeta hgamma hC_pos
  have hstart_market : start ≤ C := hstart_earlyRank.trans hearlyRank_market
  have hterminal : start + stride ≤ C := by
    calc
      start + stride ≤ theorem3DenseGapBlockCount C
            (theorem1TailPhi2 beta gamma) (theorem1TailPhi3 beta gamma) *
            stride := by simpa [stride] using hstart_window
      _ ≤ earlyRank := hblocks_prefix
      _ ≤ C := hearlyRank_market
  have hsparse_nat :
      (theorem1CutoffBelowBlock (Finset.univ : Finset (Fin (C + 1)))
        inst.selectedCutoffVector
        (theorem3RankedCutoffNat C inst.selectedCutoffVector start)).card ≤
        start := by
    simpa [theorem3RankedCutoffNat_eq_rankedCutoff C
      inst.selectedCutoffVector hstart_market] using
      (theorem1CutoffBelowBlock_card_le_rank_start C start
        inst.selectedCutoffVector hstart_market)
  have hearlyRank_real : (earlyRank : ℝ) ≤
      Real.rpow (C : ℝ) (theorem1TailPhi3 beta gamma) := by
    dsimp [earlyRank]
    unfold theorem3EarlyPrefixRank
    exact Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg C) _)
  have hsparse_real :
      ((theorem1CutoffBelowBlock (Finset.univ : Finset (Fin (C + 1)))
        inst.selectedCutoffVector
        (theorem3RankedCutoffNat C inst.selectedCutoffVector start)).card : ℝ) ≤
        Real.rpow (C : ℝ) (theorem1TailPhi3 beta gamma) := by
    have hsparse_start :
        ((theorem1CutoffBelowBlock (Finset.univ : Finset (Fin (C + 1)))
          inst.selectedCutoffVector
          (theorem3RankedCutoffNat C inst.selectedCutoffVector start)).card : ℝ) ≤
          (start : ℝ) := by exact_mod_cast hsparse_nat
    have hstart_earlyRank_real : (start : ℝ) ≤ (earlyRank : ℝ) := by
      exact_mod_cast hstart_earlyRank
    exact hsparse_start.trans (hstart_earlyRank_real.trans hearlyRank_real)
  have hC_real_pos : 0 < (C : ℝ) := by exact_mod_cast hC_pos
  have hC_le_succ : (C : ℝ) ≤ ((C + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_succ C
  have hregular_to_C : alpha / ((C + 1 : ℕ) : ℝ) ≤ alpha / (C : ℝ) :=
    div_le_div_of_nonneg_left halpha_nonneg hC_real_pos hC_le_succ
  have hcapacity : ∀ college ∈ (Finset.univ : Finset (Fin (C + 1))),
      inst.literal.capacity college ≤ alpha / (C : ℝ) := by
    intro college _
    exact (capacityRegular.le inst.capacity_regular college).trans hregular_to_C
  have hcapacity_sparse :
      activeCapacity
        (theorem1CutoffBelowBlock (Finset.univ : Finset (Fin (C + 1)))
          inst.selectedCutoffVector
          (theorem3RankedCutoffNat C inst.selectedCutoffVector start))
        inst.literal.capacity ≤
        alpha * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)) := by
    apply theorem1Tail_sparseBlock_capacity_le_alpha_rpow_neg_K
      (theorem1CutoffBelowBlock (Finset.univ : Finset (Fin (C + 1)))
        inst.selectedCutoffVector
        (theorem3RankedCutoffNat C inst.selectedCutoffVector start))
      inst.literal.capacity hC_real_pos halpha_nonneg hsparse_real
    intro college hcollege
    exact hcapacity college (Finset.mem_filter.mp hcollege).1
  have hcomponents :=
    inst.theorem1_selected_low_matched_mass_le_lower_capacity_add_upper_affordance
      (theorem3RankedCutoffNat C inst.selectedCutoffVector start)
      (region := Set.Iic vS) measurableSet_Iic
  have hupper := theorem1_literal_dense_upper_low_integral_le_of_ranked_window
    noiseLaw eta inst hholder hC_pos start (by simpa [stride] using hterminal)
    hdense hradius_le_half htail_normalization
  calc
    eventMass
        (inst.studentLaw.prod
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)))
        (fun outcome : StudentType × (Fin (C + 1) → ℝ) =>
          inst.value outcome.1 ∈ Set.Iic vS ∧
            chosenInActive
              (inst.literal.demand.demandAt inst.literal.selectedCutoff)
              (Finset.univ : Finset (Fin (C + 1))) outcome) ≤
        activeCapacity
          (theorem1CutoffBelowBlock (Finset.univ : Finset (Fin (C + 1)))
            inst.selectedCutoffVector
            (theorem3RankedCutoffNat C inst.selectedCutoffVector start))
          inst.literal.capacity +
          ∫ value : ℝ,
            (Set.Iic vS).indicator
              (fun value => cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (theorem1CutoffAtOrAboveBlock
                  (Finset.univ : Finset (Fin (C + 1)))
                  inst.selectedCutoffVector
                  (theorem3RankedCutoffNat C inst.selectedCutoffVector start))
                value inst.selectedCutoffVector) value
            ∂eta := hcomponents
    _ ≤ alpha * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)) +
          (theorem1IntegerGroupCount
            (theorem1CutoffAtOrAboveBlock
              (Finset.univ : Finset (Fin (C + 1))) inst.selectedCutoffVector
              (theorem3RankedCutoffNat C inst.selectedCutoffVector start))
            (theorem1DenseGroupIndex C beta gamma + 1) : ℝ) *
            AppliedModelingLib.Matching.topOrderDeviationProbability
              (Measure.pi (fun _ : Fin
                (theorem1DenseGroupIndex C beta gamma + 1) => noiseLaw))
              (theorem1DenseGroupCenter noiseLaw C beta gamma)
              (theorem1DenseDeviationRadius C beta gamma) +
            holderConstant *
              Real.rpow (5 * theorem1DenseDeviationRadius C beta gamma) gamma +
            2 * totalSupply *
              AppliedModelingLib.Matching.topOrderDeviationProbability
                (Measure.pi (fun _ : Fin
                  (theorem1DenseGroupIndex C beta gamma + 1) => noiseLaw))
              (theorem1DenseGroupCenter noiseLaw C beta gamma)
              (theorem1DenseDeviationRadius C beta gamma) := by
      linarith

/-- The rounded dense-block deviation itself vanishes under the source beta-max condition. -/
theorem theorem1_dense_group_deviation_tendsto_zero_of_beta
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {beta gamma : ℝ} {maxVarianceSeq : ℕ → ℝ}
    (hbeta : betaMaxConcentratingVariance maxVarianceSeq beta)
    (hgamma : 0 < gamma)
    (hvariance : source_assumption_iid_beta_max_variance_bound
      noiseLaw maxVarianceSeq) :
    Tendsto (fun C : ℕ =>
      AppliedModelingLib.Matching.topOrderDeviationProbability
        (Measure.pi (fun _ : Fin (theorem1DenseGroupIndex C beta gamma + 1) => noiseLaw))
        (theorem1DenseGroupCenter noiseLaw C beta gamma)
        (theorem1DenseDeviationRadius C beta gamma)) atTop (nhds 0) := by
  rcases theorem1DenseGroup_deviation_eventually_le_of_beta
    noiseLaw hbeta hgamma hvariance with ⟨A, hA_nonneg, hbound⟩
  let exponent : ℝ :=
    -beta * theorem1TailPhi2 beta gamma - 2 * theorem1TailPhi1 beta gamma
  have hscale_neg : exponent < 0 := by
    have hK_pos : 0 < theorem1TailK beta gamma :=
      theorem1TailK_pos hbeta.1 hgamma
    have hphi_gap : 0 < 1 - theorem1TailPhi2 beta gamma :=
      theorem1Tail_one_sub_phi2_pos hbeta.1 hgamma
    have hid := theorem1Tail_case1_chebyshev_exp_eq_neg_K hbeta.1 hgamma
    dsimp [exponent]
    linarith
  have hpow_zero : Tendsto
      (fun C : ℕ => Real.rpow (C : ℝ) exponent) atTop (nhds 0) := by
    simpa [exponent] using
      ((tendsto_rpow_neg_atTop (neg_pos.mpr hscale_neg)).comp
        tendsto_natCast_atTop_atTop)
  have hupper_zero : Tendsto
      (fun C : ℕ => A * Real.rpow (C : ℝ) exponent) atTop (nhds 0) := by
    simpa using hpow_zero.const_mul A
  have hbound' : ∀ᶠ C : ℕ in atTop,
      AppliedModelingLib.Matching.topOrderDeviationProbability
          (Measure.pi (fun _ : Fin (theorem1DenseGroupIndex C beta gamma + 1) => noiseLaw))
          (theorem1DenseGroupCenter noiseLaw C beta gamma)
          (theorem1DenseDeviationRadius C beta gamma) ≤
        A * Real.rpow (C : ℝ) exponent := by
    filter_upwards [hbound] with C hC
    simpa [exponent] using hC
  have hnonneg : ∀ C : ℕ, 0 ≤
      AppliedModelingLib.Matching.topOrderDeviationProbability
          (Measure.pi (fun _ : Fin
            (theorem1DenseGroupIndex C beta gamma + 1) => noiseLaw))
          (theorem1DenseGroupCenter noiseLaw C beta gamma)
          (theorem1DenseDeviationRadius C beta gamma) := by
    intro C
    exact theorem1_iid_topOrderDeviationProbability_nonneg
      (m := theorem1DenseGroupIndex C beta gamma + 1) noiseLaw _ _
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
    hupper_zero (Filter.Eventually.of_forall hnonneg) hbound'

/--
The source Case-1 finite union factor remains negligible after the exact
quotient/remainder grouping of a `Fin (C+1)` market.  This is derived from
the rounded dense-block beta-max estimate, not accepted as a branch rate.
-/
theorem theorem1_dense_group_union_error_tendsto_zero_of_beta
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {beta gamma : ℝ} {maxVariance : ℕ → ℝ}
    (hbeta : betaMaxConcentratingVariance maxVariance beta)
    (hgamma : 0 < gamma)
    (hvariance : source_assumption_iid_beta_max_variance_bound
      noiseLaw maxVariance)
    (block : ∀ C : ℕ, Finset (Fin (C + 1))) :
    Tendsto (fun C : ℕ =>
      (theorem1IntegerGroupCount (block C)
        (theorem1DenseGroupIndex C beta gamma + 1) : ℝ) *
        AppliedModelingLib.Matching.topOrderDeviationProbability
          (Measure.pi (fun _ : Fin
            (theorem1DenseGroupIndex C beta gamma + 1) => noiseLaw))
          (theorem1DenseGroupCenter noiseLaw C beta gamma)
          (theorem1DenseDeviationRadius C beta gamma)) atTop (nhds 0) := by
  rcases theorem1DenseGroup_deviation_eventually_le_of_beta
    noiseLaw hbeta hgamma hvariance with ⟨A, hA_nonneg, hdeviation⟩
  let errorExponent : ℝ :=
    -beta * theorem1TailPhi2 beta gamma - 2 * theorem1TailPhi1 beta gamma
  have hcount_bound : ∀ᶠ C : ℕ in atTop,
      (theorem1IntegerGroupCount (block C)
        (theorem1DenseGroupIndex C beta gamma + 1) : ℝ) ≤
        3 * Real.rpow (C : ℝ) (1 - theorem1TailPhi2 beta gamma) := by
    filter_upwards [eventually_ge_atTop 1] with C hC_one
    let m : ℕ := theorem1DenseGroupIndex C beta gamma + 1
    have hC_pos : 0 < C := lt_of_lt_of_le Nat.zero_lt_one hC_one
    have hC_real_pos : 0 < (C : ℝ) := by exact_mod_cast hC_pos
    have hC_real_one : (1 : ℝ) ≤ (C : ℝ) := by exact_mod_cast hC_one
    have hm_eq_size : m = theorem1DenseGroupSize C beta gamma := by
      dsimp [m]
      exact theorem1DenseGroupIndex_add_one C beta gamma
    have hm_real_pos : 0 < (m : ℝ) := by
      rw [hm_eq_size]
      exact_mod_cast theorem1DenseGroupSize_pos C beta gamma
    have hm_lower : Real.rpow (C : ℝ) (theorem1TailPhi2 beta gamma) ≤
        (m : ℝ) := by
      rw [hm_eq_size]
      exact theorem1DenseGroupSize_real_le C beta gamma
    have hpower_pos : 0 < Real.rpow (C : ℝ) (theorem1TailPhi2 beta gamma) :=
      Real.rpow_pos_of_pos hC_real_pos _
    have hblock_card : (block C).card ≤ C + 1 := by
      simpa using Finset.card_le_card (Finset.subset_univ (block C))
    have hblock_card_real : ((block C).card : ℝ) ≤ ((C + 1 : ℕ) : ℝ) := by
      exact_mod_cast hblock_card
    have hnum : ((C + 1 : ℕ) : ℝ) ≤ 2 * (C : ℝ) := by
      norm_num [Nat.cast_add]
      linarith
    have hquotient : ((C + 1 : ℕ) : ℝ) / (m : ℝ) ≤
        2 * Real.rpow (C : ℝ) (1 - theorem1TailPhi2 beta gamma) := by
      calc
        ((C + 1 : ℕ) : ℝ) / (m : ℝ) ≤ (2 * (C : ℝ)) / (m : ℝ) :=
          div_le_div_of_nonneg_right hnum hm_real_pos.le
        _ ≤ (2 * (C : ℝ)) /
            Real.rpow (C : ℝ) (theorem1TailPhi2 beta gamma) :=
          div_le_div_of_nonneg_left (by positivity) hpower_pos hm_lower
        _ = 2 * Real.rpow (C : ℝ) (1 - theorem1TailPhi2 beta gamma) := by
          calc
            (2 * (C : ℝ)) /
                Real.rpow (C : ℝ) (theorem1TailPhi2 beta gamma) =
                (2 * Real.rpow (C : ℝ) 1) /
                  Real.rpow (C : ℝ) (theorem1TailPhi2 beta gamma) := by
              exact congrArg
                (fun value : ℝ => (2 * value) /
                  Real.rpow (C : ℝ) (theorem1TailPhi2 beta gamma))
                (Real.rpow_one (C : ℝ)).symm
            _ = 2 * (Real.rpow (C : ℝ) 1 /
                  Real.rpow (C : ℝ) (theorem1TailPhi2 beta gamma)) := by
              ring
            _ = 2 * Real.rpow (C : ℝ)
                (1 - theorem1TailPhi2 beta gamma) := by
              exact congrArg (fun value : ℝ => 2 * value)
                (Real.rpow_sub hC_real_pos 1
                  (theorem1TailPhi2 beta gamma)).symm
    have hscale_one : 1 ≤ Real.rpow (C : ℝ)
        (1 - theorem1TailPhi2 beta gamma) :=
      Real.one_le_rpow hC_real_one
        (theorem1Tail_one_sub_phi2_pos hbeta.1 hgamma).le
    have hdiv_cast : (((block C).card / m : ℕ) : ℝ) ≤
        ((block C).card : ℝ) / (m : ℝ) := Nat.cast_div_le
    change (((block C).card / m + 1 : ℕ) : ℝ) ≤ _
    calc
      (((block C).card / m + 1 : ℕ) : ℝ) =
          (((block C).card / m : ℕ) : ℝ) + 1 := by norm_num
      _ ≤ ((block C).card : ℝ) / (m : ℝ) + 1 :=
        by simpa [add_comm] using (add_le_add_right hdiv_cast 1)
      _ ≤ ((C + 1 : ℕ) : ℝ) / (m : ℝ) + 1 :=
        by simpa [add_comm] using (add_le_add_right
          (div_le_div_of_nonneg_right hblock_card_real hm_real_pos.le) 1)
      _ ≤ 2 * Real.rpow (C : ℝ) (1 - theorem1TailPhi2 beta gamma) + 1 :=
        by simpa [add_comm] using (add_le_add_right hquotient 1)
      _ ≤ 3 * Real.rpow (C : ℝ) (1 - theorem1TailPhi2 beta gamma) := by
        linarith
  have hproduct_bound : ∀ᶠ C : ℕ in atTop,
      (theorem1IntegerGroupCount (block C)
        (theorem1DenseGroupIndex C beta gamma + 1) : ℝ) *
        AppliedModelingLib.Matching.topOrderDeviationProbability
          (Measure.pi (fun _ : Fin
            (theorem1DenseGroupIndex C beta gamma + 1) => noiseLaw))
          (theorem1DenseGroupCenter noiseLaw C beta gamma)
          (theorem1DenseDeviationRadius C beta gamma) ≤
        (3 * A) * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)) := by
    filter_upwards [eventually_ge_atTop 1, hcount_bound, hdeviation]
      with C hC_one hcount herror
    have hC_pos : 0 < (C : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hC_one)
    have herror_nonneg : 0 ≤
        AppliedModelingLib.Matching.topOrderDeviationProbability
          (Measure.pi (fun _ : Fin
            (theorem1DenseGroupIndex C beta gamma + 1) => noiseLaw))
          (theorem1DenseGroupCenter noiseLaw C beta gamma)
          (theorem1DenseDeviationRadius C beta gamma) :=
      theorem1_iid_topOrderDeviationProbability_nonneg
        (m := theorem1DenseGroupIndex C beta gamma + 1) noiseLaw _ _
    have hfactor_nonneg : 0 ≤ 3 * Real.rpow (C : ℝ)
        (1 - theorem1TailPhi2 beta gamma) := by
      exact mul_nonneg (by norm_num)
        (Real.rpow_nonneg (Nat.cast_nonneg C) _)
    have herror' :
        AppliedModelingLib.Matching.topOrderDeviationProbability
          (Measure.pi (fun _ : Fin
            (theorem1DenseGroupIndex C beta gamma + 1) => noiseLaw))
          (theorem1DenseGroupCenter noiseLaw C beta gamma)
          (theorem1DenseDeviationRadius C beta gamma) ≤
          A * Real.rpow (C : ℝ) errorExponent := by
      simpa [errorExponent] using herror
    have hexponent :
        (1 - theorem1TailPhi2 beta gamma) + errorExponent =
          -(theorem1TailK beta gamma) := by
      dsimp [errorExponent]
      calc
        (1 - theorem1TailPhi2 beta gamma) +
            (-beta * theorem1TailPhi2 beta gamma -
              2 * theorem1TailPhi1 beta gamma) =
            1 - 2 * theorem1TailPhi1 beta gamma -
              (1 + beta) * theorem1TailPhi2 beta gamma := by ring
        _ = -(theorem1TailK beta gamma) :=
          theorem1Tail_case1_chebyshev_exp_eq_neg_K hbeta.1 hgamma
    calc
      (theorem1IntegerGroupCount (block C)
        (theorem1DenseGroupIndex C beta gamma + 1) : ℝ) *
          AppliedModelingLib.Matching.topOrderDeviationProbability
            (Measure.pi (fun _ : Fin
              (theorem1DenseGroupIndex C beta gamma + 1) => noiseLaw))
            (theorem1DenseGroupCenter noiseLaw C beta gamma)
            (theorem1DenseDeviationRadius C beta gamma) ≤
          (3 * Real.rpow (C : ℝ) (1 - theorem1TailPhi2 beta gamma)) *
            AppliedModelingLib.Matching.topOrderDeviationProbability
              (Measure.pi (fun _ : Fin
                (theorem1DenseGroupIndex C beta gamma + 1) => noiseLaw))
              (theorem1DenseGroupCenter noiseLaw C beta gamma)
              (theorem1DenseDeviationRadius C beta gamma) :=
        mul_le_mul_of_nonneg_right hcount herror_nonneg
      _ ≤ (3 * Real.rpow (C : ℝ) (1 - theorem1TailPhi2 beta gamma)) *
            (A * Real.rpow (C : ℝ) errorExponent) :=
        mul_le_mul_of_nonneg_left herror' hfactor_nonneg
      _ = (3 * A) * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)) := by
        calc
          (3 * Real.rpow (C : ℝ) (1 - theorem1TailPhi2 beta gamma)) *
              (A * Real.rpow (C : ℝ) errorExponent) =
              (3 * A) *
                (Real.rpow (C : ℝ) (1 - theorem1TailPhi2 beta gamma) *
                  Real.rpow (C : ℝ) errorExponent) := by ring
          _ = (3 * A) * Real.rpow (C : ℝ)
                ((1 - theorem1TailPhi2 beta gamma) + errorExponent) := by
            exact congrArg (fun value : ℝ => (3 * A) * value)
              (Real.rpow_add hC_pos (1 - theorem1TailPhi2 beta gamma)
                errorExponent).symm
          _ = (3 * A) * Real.rpow (C : ℝ)
                (-(theorem1TailK beta gamma)) := by rw [hexponent]
  have hpower_zero : Tendsto
      (fun C : ℕ => Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)))
        atTop (nhds 0) := by
    simpa using
      ((tendsto_rpow_neg_atTop (theorem1TailK_pos hbeta.1 hgamma)).comp
        tendsto_natCast_atTop_atTop)
  have hupper_zero : Tendsto
      (fun C : ℕ => (3 * A) *
        Real.rpow (C : ℝ) (-(theorem1TailK beta gamma))) atTop (nhds 0) := by
    simpa using hpower_zero.const_mul (3 * A)
  have hnonneg : ∀ C : ℕ, 0 ≤
      (theorem1IntegerGroupCount (block C)
        (theorem1DenseGroupIndex C beta gamma + 1) : ℝ) *
        AppliedModelingLib.Matching.topOrderDeviationProbability
          (Measure.pi (fun _ : Fin
            (theorem1DenseGroupIndex C beta gamma + 1) => noiseLaw))
          (theorem1DenseGroupCenter noiseLaw C beta gamma)
          (theorem1DenseDeviationRadius C beta gamma) := by
    intro C
    exact mul_nonneg (by positivity)
      (theorem1_iid_topOrderDeviationProbability_nonneg
        (m := theorem1DenseGroupIndex C beta gamma + 1) noiseLaw _ _)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
    hupper_zero (Filter.Eventually.of_forall hnonneg) hproduct_bound

/--
The quotient/remainder group count is uniformly bounded by the dense-scale
envelope for every active block of a `Fin (C+1)` market.
-/
theorem theorem1_dense_group_count_eventually_le_three_rpow
    {beta gamma : ℝ}
    (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (block : ∀ C : ℕ, Finset (Fin (C + 1))) :
    ∀ᶠ C : ℕ in atTop,
      (theorem1IntegerGroupCount (block C)
        (theorem1DenseGroupIndex C beta gamma + 1) : ℝ) ≤
        3 * Real.rpow (C : ℝ) (1 - theorem1TailPhi2 beta gamma) := by
  filter_upwards [eventually_ge_atTop 1] with C hC_one
  let m : ℕ := theorem1DenseGroupIndex C beta gamma + 1
  have hC_pos : 0 < C := lt_of_lt_of_le Nat.zero_lt_one hC_one
  have hC_real_pos : 0 < (C : ℝ) := by exact_mod_cast hC_pos
  have hC_real_one : (1 : ℝ) ≤ (C : ℝ) := by exact_mod_cast hC_one
  have hm_eq_size : m = theorem1DenseGroupSize C beta gamma := by
    dsimp [m]
    exact theorem1DenseGroupIndex_add_one C beta gamma
  have hm_real_pos : 0 < (m : ℝ) := by
    rw [hm_eq_size]
    exact_mod_cast theorem1DenseGroupSize_pos C beta gamma
  have hm_lower : Real.rpow (C : ℝ) (theorem1TailPhi2 beta gamma) ≤
      (m : ℝ) := by
    rw [hm_eq_size]
    exact theorem1DenseGroupSize_real_le C beta gamma
  have hpower_pos : 0 < Real.rpow (C : ℝ) (theorem1TailPhi2 beta gamma) :=
    Real.rpow_pos_of_pos hC_real_pos _
  have hblock_card : (block C).card ≤ C + 1 := by
    simpa using Finset.card_le_card (Finset.subset_univ (block C))
  have hblock_card_real : ((block C).card : ℝ) ≤ ((C + 1 : ℕ) : ℝ) := by
    exact_mod_cast hblock_card
  have hnum : ((C + 1 : ℕ) : ℝ) ≤ 2 * (C : ℝ) := by
    norm_num [Nat.cast_add]
    linarith
  have hquotient : ((C + 1 : ℕ) : ℝ) / (m : ℝ) ≤
      2 * Real.rpow (C : ℝ) (1 - theorem1TailPhi2 beta gamma) := by
    calc
      ((C + 1 : ℕ) : ℝ) / (m : ℝ) ≤ (2 * (C : ℝ)) / (m : ℝ) :=
        div_le_div_of_nonneg_right hnum hm_real_pos.le
      _ ≤ (2 * (C : ℝ)) /
          Real.rpow (C : ℝ) (theorem1TailPhi2 beta gamma) :=
        div_le_div_of_nonneg_left (by positivity) hpower_pos hm_lower
      _ = 2 * Real.rpow (C : ℝ) (1 - theorem1TailPhi2 beta gamma) := by
        calc
          (2 * (C : ℝ)) /
              Real.rpow (C : ℝ) (theorem1TailPhi2 beta gamma) =
              (2 * Real.rpow (C : ℝ) 1) /
                Real.rpow (C : ℝ) (theorem1TailPhi2 beta gamma) := by
            exact congrArg
              (fun value : ℝ => (2 * value) /
                Real.rpow (C : ℝ) (theorem1TailPhi2 beta gamma))
              (Real.rpow_one (C : ℝ)).symm
          _ = 2 * (Real.rpow (C : ℝ) 1 /
                Real.rpow (C : ℝ) (theorem1TailPhi2 beta gamma)) := by
            ring
          _ = 2 * Real.rpow (C : ℝ)
              (1 - theorem1TailPhi2 beta gamma) := by
            exact congrArg (fun value : ℝ => 2 * value)
              (Real.rpow_sub hC_real_pos 1
                (theorem1TailPhi2 beta gamma)).symm
  have hscale_one : 1 ≤ Real.rpow (C : ℝ)
      (1 - theorem1TailPhi2 beta gamma) :=
    Real.one_le_rpow hC_real_one
      (theorem1Tail_one_sub_phi2_pos hbeta hgamma).le
  have hdiv_cast : (((block C).card / m : ℕ) : ℝ) ≤
      ((block C).card : ℝ) / (m : ℝ) := Nat.cast_div_le
  change (((block C).card / m + 1 : ℕ) : ℝ) ≤ _
  calc
    (((block C).card / m + 1 : ℕ) : ℝ) =
        (((block C).card / m : ℕ) : ℝ) + 1 := by norm_num
    _ ≤ ((block C).card : ℝ) / (m : ℝ) + 1 :=
      by simpa [add_comm] using (add_le_add_right hdiv_cast 1)
    _ ≤ ((C + 1 : ℕ) : ℝ) / (m : ℝ) + 1 :=
      by simpa [add_comm] using (add_le_add_right
        (div_le_div_of_nonneg_right hblock_card_real hm_real_pos.le) 1)
    _ ≤ 2 * Real.rpow (C : ℝ) (1 - theorem1TailPhi2 beta gamma) + 1 :=
      by simpa [add_comm] using (add_le_add_right hquotient 1)
    _ ≤ 3 * Real.rpow (C : ℝ) (1 - theorem1TailPhi2 beta gamma) := by
      linarith

/-- The preceding group-count envelope holds simultaneously for every block. -/
theorem theorem1_dense_group_count_le_three_rpow_of_one_le
    {C : ℕ} {beta gamma : ℝ}
    (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hC_one : 1 ≤ C) (block : Finset (Fin (C + 1))) :
    (theorem1IntegerGroupCount block
      (theorem1DenseGroupIndex C beta gamma + 1) : ℝ) ≤
      3 * Real.rpow (C : ℝ) (1 - theorem1TailPhi2 beta gamma) := by
  let m : ℕ := theorem1DenseGroupIndex C beta gamma + 1
  have hC_pos : 0 < C := lt_of_lt_of_le Nat.zero_lt_one hC_one
  have hC_real_pos : 0 < (C : ℝ) := by exact_mod_cast hC_pos
  have hC_real_one : (1 : ℝ) ≤ (C : ℝ) := by exact_mod_cast hC_one
  have hm_eq_size : m = theorem1DenseGroupSize C beta gamma := by
    dsimp [m]
    exact theorem1DenseGroupIndex_add_one C beta gamma
  have hm_real_pos : 0 < (m : ℝ) := by
    rw [hm_eq_size]
    exact_mod_cast theorem1DenseGroupSize_pos C beta gamma
  have hm_lower : Real.rpow (C : ℝ) (theorem1TailPhi2 beta gamma) ≤
      (m : ℝ) := by
    rw [hm_eq_size]
    exact theorem1DenseGroupSize_real_le C beta gamma
  have hpower_pos : 0 < Real.rpow (C : ℝ) (theorem1TailPhi2 beta gamma) :=
    Real.rpow_pos_of_pos hC_real_pos _
  have hblock_card : block.card ≤ C + 1 := by
    simpa using Finset.card_le_card (Finset.subset_univ block)
  have hblock_card_real : (block.card : ℝ) ≤ ((C + 1 : ℕ) : ℝ) := by
    exact_mod_cast hblock_card
  have hnum : ((C + 1 : ℕ) : ℝ) ≤ 2 * (C : ℝ) := by
    norm_num [Nat.cast_add]
    linarith
  have hquotient : ((C + 1 : ℕ) : ℝ) / (m : ℝ) ≤
      2 * Real.rpow (C : ℝ) (1 - theorem1TailPhi2 beta gamma) := by
    calc
      ((C + 1 : ℕ) : ℝ) / (m : ℝ) ≤ (2 * (C : ℝ)) / (m : ℝ) :=
        div_le_div_of_nonneg_right hnum hm_real_pos.le
      _ ≤ (2 * (C : ℝ)) /
          Real.rpow (C : ℝ) (theorem1TailPhi2 beta gamma) :=
        div_le_div_of_nonneg_left (by positivity) hpower_pos hm_lower
      _ = 2 * Real.rpow (C : ℝ) (1 - theorem1TailPhi2 beta gamma) := by
        calc
          (2 * (C : ℝ)) /
              Real.rpow (C : ℝ) (theorem1TailPhi2 beta gamma) =
              (2 * Real.rpow (C : ℝ) 1) /
                Real.rpow (C : ℝ) (theorem1TailPhi2 beta gamma) := by
            exact congrArg
              (fun value : ℝ => (2 * value) /
                Real.rpow (C : ℝ) (theorem1TailPhi2 beta gamma))
              (Real.rpow_one (C : ℝ)).symm
          _ = 2 * (Real.rpow (C : ℝ) 1 /
                Real.rpow (C : ℝ) (theorem1TailPhi2 beta gamma)) := by
            ring
          _ = 2 * Real.rpow (C : ℝ)
              (1 - theorem1TailPhi2 beta gamma) := by
            exact congrArg (fun value : ℝ => 2 * value)
              (Real.rpow_sub hC_real_pos 1
                (theorem1TailPhi2 beta gamma)).symm
  have hscale_one : 1 ≤ Real.rpow (C : ℝ)
      (1 - theorem1TailPhi2 beta gamma) :=
    Real.one_le_rpow hC_real_one
      (theorem1Tail_one_sub_phi2_pos hbeta hgamma).le
  have hdiv_cast : ((block.card / m : ℕ) : ℝ) ≤
      (block.card : ℝ) / (m : ℝ) := Nat.cast_div_le
  change ((block.card / m + 1 : ℕ) : ℝ) ≤ _
  calc
    ((block.card / m + 1 : ℕ) : ℝ) =
        ((block.card / m : ℕ) : ℝ) + 1 := by norm_num
    _ ≤ (block.card : ℝ) / (m : ℝ) + 1 :=
      by simpa [add_comm] using (add_le_add_right hdiv_cast 1)
    _ ≤ ((C + 1 : ℕ) : ℝ) / (m : ℝ) + 1 :=
      by simpa [add_comm] using (add_le_add_right
        (div_le_div_of_nonneg_right hblock_card_real hm_real_pos.le) 1)
    _ ≤ 2 * Real.rpow (C : ℝ) (1 - theorem1TailPhi2 beta gamma) + 1 :=
      by simpa [add_comm] using (add_le_add_right hquotient 1)
    _ ≤ 3 * Real.rpow (C : ℝ) (1 - theorem1TailPhi2 beta gamma) := by
      linarith

/-- The source Holder-window envelope decays at the same dense-branch rate. -/
theorem theorem1_dense_holder_envelope_tendsto_zero
    {beta gamma holderConstant : ℝ}
    (hbeta : 0 < beta) (hgamma : 0 < gamma) :
    Tendsto (fun C : ℕ =>
      holderConstant * Real.rpow
        (5 * theorem1DenseDeviationRadius C beta gamma) gamma)
      atTop (nhds 0) := by
  have hpower_zero : Tendsto
      (fun C : ℕ => Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)))
        atTop (nhds 0) := by
    simpa using
      ((tendsto_rpow_neg_atTop (theorem1TailK_pos hbeta hgamma)).comp
        tendsto_natCast_atTop_atTop)
  have hmain : Tendsto
      (fun C : ℕ => (holderConstant * Real.rpow 5 gamma) *
        Real.rpow (C : ℝ) (-(theorem1TailK beta gamma))) atTop (nhds 0) := by
    simpa using hpower_zero.const_mul (holderConstant * Real.rpow 5 gamma)
  refine Tendsto.congr' ?_ hmain
  filter_upwards [eventually_gt_atTop 0] with C hC_pos
  have hC_real_pos : 0 < (C : ℝ) := by exact_mod_cast hC_pos
  unfold theorem1DenseDeviationRadius
  symm
  calc
    holderConstant * Real.rpow
        (5 * Real.rpow (C : ℝ) (theorem1TailPhi1 beta gamma)) gamma =
        (holderConstant * Real.rpow 5 gamma) *
          Real.rpow (C : ℝ)
            (gamma * theorem1TailPhi1 beta gamma) := by
      have hmul : Real.rpow
          (5 * Real.rpow (C : ℝ) (theorem1TailPhi1 beta gamma)) gamma =
          Real.rpow 5 gamma *
            Real.rpow (Real.rpow (C : ℝ)
              (theorem1TailPhi1 beta gamma)) gamma := by
        exact Real.mul_rpow (by norm_num) (le_of_lt
          (Real.rpow_pos_of_pos hC_real_pos _))
      have hcompose : Real.rpow
          (Real.rpow (C : ℝ) (theorem1TailPhi1 beta gamma)) gamma =
          Real.rpow (C : ℝ) (theorem1TailPhi1 beta gamma * gamma) := by
        exact (Real.rpow_mul (le_of_lt hC_real_pos)
          (theorem1TailPhi1 beta gamma) gamma).symm
      rw [hmul, hcompose]
      ring
    _ = (holderConstant * Real.rpow 5 gamma) *
          Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)) := by
      rw [theorem1Tail_gamma_mul_phi1_eq_neg_K beta gamma]

/-- The start-independent dense union-error envelope tends to zero. -/
theorem theorem1_dense_group_error_envelope_tendsto_zero_of_beta
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {beta gamma : ℝ} {maxVariance : ℕ → ℝ}
    (hbeta : betaMaxConcentratingVariance maxVariance beta)
    (hgamma : 0 < gamma)
    (hvariance : source_assumption_iid_beta_max_variance_bound
      noiseLaw maxVariance) :
    Tendsto (fun C : ℕ =>
      (3 * Real.rpow (C : ℝ) (1 - theorem1TailPhi2 beta gamma)) *
        AppliedModelingLib.Matching.topOrderDeviationProbability
          (Measure.pi (fun _ : Fin
            (theorem1DenseGroupIndex C beta gamma + 1) => noiseLaw))
          (theorem1DenseGroupCenter noiseLaw C beta gamma)
          (theorem1DenseDeviationRadius C beta gamma)) atTop (nhds 0) := by
  rcases theorem1DenseGroup_deviation_eventually_le_of_beta
    noiseLaw hbeta hgamma hvariance with ⟨A, hA_nonneg, hdeviation⟩
  let errorExponent : ℝ :=
    -beta * theorem1TailPhi2 beta gamma - 2 * theorem1TailPhi1 beta gamma
  have hupper_bound : ∀ᶠ C : ℕ in atTop,
      (3 * Real.rpow (C : ℝ) (1 - theorem1TailPhi2 beta gamma)) *
        AppliedModelingLib.Matching.topOrderDeviationProbability
          (Measure.pi (fun _ : Fin
            (theorem1DenseGroupIndex C beta gamma + 1) => noiseLaw))
          (theorem1DenseGroupCenter noiseLaw C beta gamma)
          (theorem1DenseDeviationRadius C beta gamma) ≤
        (3 * A) * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)) := by
    filter_upwards [eventually_ge_atTop 1, hdeviation]
      with C hC_one herror
    have hC_pos : 0 < (C : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hC_one)
    have hfactor_nonneg : 0 ≤ 3 * Real.rpow (C : ℝ)
        (1 - theorem1TailPhi2 beta gamma) := by
      exact mul_nonneg (by norm_num)
        (Real.rpow_nonneg (Nat.cast_nonneg C) _)
    have herror' :
        AppliedModelingLib.Matching.topOrderDeviationProbability
          (Measure.pi (fun _ : Fin
            (theorem1DenseGroupIndex C beta gamma + 1) => noiseLaw))
          (theorem1DenseGroupCenter noiseLaw C beta gamma)
          (theorem1DenseDeviationRadius C beta gamma) ≤
          A * Real.rpow (C : ℝ) errorExponent := by
      simpa [errorExponent] using herror
    have hexponent :
        (1 - theorem1TailPhi2 beta gamma) + errorExponent =
          -(theorem1TailK beta gamma) := by
      dsimp [errorExponent]
      calc
        (1 - theorem1TailPhi2 beta gamma) +
            (-beta * theorem1TailPhi2 beta gamma -
              2 * theorem1TailPhi1 beta gamma) =
            1 - 2 * theorem1TailPhi1 beta gamma -
              (1 + beta) * theorem1TailPhi2 beta gamma := by ring
        _ = -(theorem1TailK beta gamma) :=
          theorem1Tail_case1_chebyshev_exp_eq_neg_K hbeta.1 hgamma
    calc
      (3 * Real.rpow (C : ℝ) (1 - theorem1TailPhi2 beta gamma)) *
          AppliedModelingLib.Matching.topOrderDeviationProbability
            (Measure.pi (fun _ : Fin
              (theorem1DenseGroupIndex C beta gamma + 1) => noiseLaw))
            (theorem1DenseGroupCenter noiseLaw C beta gamma)
            (theorem1DenseDeviationRadius C beta gamma) ≤
          (3 * Real.rpow (C : ℝ) (1 - theorem1TailPhi2 beta gamma)) *
            (A * Real.rpow (C : ℝ) errorExponent) :=
        mul_le_mul_of_nonneg_left herror' hfactor_nonneg
      _ = (3 * A) * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)) := by
        calc
          (3 * Real.rpow (C : ℝ) (1 - theorem1TailPhi2 beta gamma)) *
              (A * Real.rpow (C : ℝ) errorExponent) =
              (3 * A) *
                (Real.rpow (C : ℝ) (1 - theorem1TailPhi2 beta gamma) *
                  Real.rpow (C : ℝ) errorExponent) := by ring
          _ = (3 * A) * Real.rpow (C : ℝ)
                ((1 - theorem1TailPhi2 beta gamma) + errorExponent) := by
            exact congrArg (fun value : ℝ => (3 * A) * value)
              (Real.rpow_add hC_pos (1 - theorem1TailPhi2 beta gamma)
                errorExponent).symm
          _ = (3 * A) * Real.rpow (C : ℝ)
                (-(theorem1TailK beta gamma)) := by rw [hexponent]
  have hpower_zero : Tendsto
      (fun C : ℕ => Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)))
        atTop (nhds 0) := by
    simpa using
      ((tendsto_rpow_neg_atTop (theorem1TailK_pos hbeta.1 hgamma)).comp
        tendsto_natCast_atTop_atTop)
  have hupper_zero : Tendsto
      (fun C : ℕ => (3 * A) *
        Real.rpow (C : ℝ) (-(theorem1TailK beta gamma))) atTop (nhds 0) := by
    simpa using hpower_zero.const_mul (3 * A)
  have hnonneg : ∀ C : ℕ, 0 ≤
      (3 * Real.rpow (C : ℝ) (1 - theorem1TailPhi2 beta gamma)) *
        AppliedModelingLib.Matching.topOrderDeviationProbability
          (Measure.pi (fun _ : Fin
            (theorem1DenseGroupIndex C beta gamma + 1) => noiseLaw))
          (theorem1DenseGroupCenter noiseLaw C beta gamma)
          (theorem1DenseDeviationRadius C beta gamma) := by
    intro C
    exact mul_nonneg
      (mul_nonneg (by norm_num)
        (Real.rpow_nonneg (Nat.cast_nonneg C) _))
      (theorem1_iid_topOrderDeviationProbability_nonneg
        (m := theorem1DenseGroupIndex C beta gamma + 1) noiseLaw _ _)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
    hupper_zero (Filter.Eventually.of_forall hnonneg) hupper_bound

/--
Every actual canonical dense window has vanishing literal selected low matched
mass.  The eventual bound is uniform in the window start, so this result can
be joined with the complementary large-gap alternative without choosing a
single dense witness in advance.
-/
theorem theorem1_literal_selected_dense_branch_eventually_small_of_holder
    {StudentType : Type u} [MeasurableSpace StudentType]
    {Cutoff : Type v}
    (noiseLaw eta : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {maxVariance : ℕ → ℝ} {alpha beta vS totalSupply : ℝ}
    (inst : ∀ C : ℕ,
      PG24LiteralBasicTwoScaleInstance C noiseLaw eta totalSupply alpha
        StudentType Cutoff)
    (hbeta : betaMaxConcentratingVariance maxVariance beta)
    (hvariance : source_assumption_iid_beta_max_variance_bound
      noiseLaw maxVariance)
    (halpha_nonneg : 0 ≤ alpha)
    (hregular : PG24HolderIntervalRegular eta)
    (htail_normalization : eta.real (Set.Ioi vS) = totalSupply) :
    ∃ holderConstant gamma : ℝ,
      0 < gamma ∧
      0 ≤ holderConstant ∧
      (∀ (x delta : ℝ), 0 < delta →
        eta.real (Set.Ioo x (x + delta)) ≤
          holderConstant * Real.rpow delta gamma) ∧
      ∀ epsilon : ℝ, 0 < epsilon →
        ∀ᶠ C : ℕ in atTop, ∀ start : ℕ,
          start + theorem3DenseWindowCount C
              (theorem1TailPhi2 beta gamma) ≤
            theorem3DenseGapBlockCount C
                (theorem1TailPhi2 beta gamma) (theorem1TailPhi3 beta gamma) *
              theorem3DenseWindowCount C (theorem1TailPhi2 beta gamma) →
          theorem1TailDenseRankWindow
              (theorem3RankedCutoffNat C (inst C).selectedCutoffVector) start
              (theorem3DenseWindowCount C (theorem1TailPhi2 beta gamma))
              (theorem1DenseDeviationRadius C beta gamma) →
          eventMass
            ((inst C).studentLaw.prod
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)))
            (fun outcome : StudentType × (Fin (C + 1) → ℝ) =>
              (inst C).value outcome.1 ∈ Set.Iic vS ∧
                chosenInActive
                  ((inst C).literal.demand.demandAt
                    (inst C).literal.selectedCutoff)
                  (Finset.univ : Finset (Fin (C + 1))) outcome) < epsilon := by
  rcases hregular with ⟨holderConstant, gamma, hgamma, hholder_nonneg, hholder⟩
  refine ⟨holderConstant, gamma, hgamma, hholder_nonneg, hholder, ?_⟩
  have hcapacity_zero : Tendsto
      (fun C : ℕ => alpha * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)))
      atTop (nhds 0) := by
    have hpower : Tendsto
        (fun C : ℕ => Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)))
        atTop (nhds 0) := by
      simpa using
        ((tendsto_rpow_neg_atTop (theorem1TailK_pos hbeta.1 hgamma)).comp
          tendsto_natCast_atTop_atTop)
    simpa using hpower.const_mul alpha
  have hgroup_zero := theorem1_dense_group_error_envelope_tendsto_zero_of_beta
    noiseLaw hbeta hgamma hvariance
  have hholder_zero := theorem1_dense_holder_envelope_tendsto_zero
    (holderConstant := holderConstant) hbeta.1 hgamma
  have herror_zero := theorem1_dense_group_deviation_tendsto_zero_of_beta
    noiseLaw hbeta hgamma hvariance
  have hhigh_zero : Tendsto (fun C : ℕ =>
      2 * totalSupply *
        AppliedModelingLib.Matching.topOrderDeviationProbability
          (Measure.pi (fun _ : Fin
            (theorem1DenseGroupIndex C beta gamma + 1) => noiseLaw))
          (theorem1DenseGroupCenter noiseLaw C beta gamma)
          (theorem1DenseDeviationRadius C beta gamma)) atTop (nhds 0) := by
    simpa using herror_zero.const_mul (2 * totalSupply)
  let denseBound : ℕ → ℝ := fun C =>
    alpha * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)) +
      (3 * Real.rpow (C : ℝ) (1 - theorem1TailPhi2 beta gamma)) *
        AppliedModelingLib.Matching.topOrderDeviationProbability
          (Measure.pi (fun _ : Fin
            (theorem1DenseGroupIndex C beta gamma + 1) => noiseLaw))
          (theorem1DenseGroupCenter noiseLaw C beta gamma)
          (theorem1DenseDeviationRadius C beta gamma) +
      holderConstant * Real.rpow
        (5 * theorem1DenseDeviationRadius C beta gamma) gamma +
      2 * totalSupply *
        AppliedModelingLib.Matching.topOrderDeviationProbability
          (Measure.pi (fun _ : Fin
            (theorem1DenseGroupIndex C beta gamma + 1) => noiseLaw))
          (theorem1DenseGroupCenter noiseLaw C beta gamma)
          (theorem1DenseDeviationRadius C beta gamma)
  have hdenseBound_zero : Tendsto denseBound atTop (nhds 0) := by
    simpa [denseBound] using
      ((hcapacity_zero.add hgroup_zero).add hholder_zero).add hhigh_zero
  intro epsilon hepsilon
  have hdenseBound_small : ∀ᶠ C : ℕ in atTop, denseBound C < epsilon := by
    simpa using hdenseBound_zero (Iio_mem_nhds hepsilon)
  have hradius_le_half : ∀ᶠ C : ℕ in atTop,
      AppliedModelingLib.Matching.topOrderDeviationProbability
          (Measure.pi (fun _ : Fin
            (theorem1DenseGroupIndex C beta gamma + 1) => noiseLaw))
          (theorem1DenseGroupCenter noiseLaw C beta gamma)
          (theorem1DenseDeviationRadius C beta gamma) ≤ 1 / 2 := by
    have hstrict : ∀ᶠ C : ℕ in atTop,
        AppliedModelingLib.Matching.topOrderDeviationProbability
            (Measure.pi (fun _ : Fin
              (theorem1DenseGroupIndex C beta gamma + 1) => noiseLaw))
            (theorem1DenseGroupCenter noiseLaw C beta gamma)
            (theorem1DenseDeviationRadius C beta gamma) < 1 / 2 := by
      simpa using herror_zero (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
    filter_upwards [hstrict] with C hC
    linarith
  filter_upwards [eventually_ge_atTop 1, hdenseBound_small, hradius_le_half]
    with C hC_one hbound_small hradius start hstart_window hdense
  have hC_pos : 0 < C := lt_of_lt_of_le Nat.zero_lt_one hC_one
  let upper : Finset (Fin (C + 1)) := theorem1CutoffAtOrAboveBlock
    Finset.univ (inst C).selectedCutoffVector
    (theorem3RankedCutoffNat C (inst C).selectedCutoffVector start)
  have hcount : (theorem1IntegerGroupCount upper
      (theorem1DenseGroupIndex C beta gamma + 1) : ℝ) ≤
      3 * Real.rpow (C : ℝ) (1 - theorem1TailPhi2 beta gamma) :=
    theorem1_dense_group_count_le_three_rpow_of_one_le
      hbeta.1 hgamma hC_one upper
  have herror_nonneg : 0 ≤
      AppliedModelingLib.Matching.topOrderDeviationProbability
        (Measure.pi (fun _ : Fin
          (theorem1DenseGroupIndex C beta gamma + 1) => noiseLaw))
        (theorem1DenseGroupCenter noiseLaw C beta gamma)
        (theorem1DenseDeviationRadius C beta gamma) :=
    theorem1_iid_topOrderDeviationProbability_nonneg
      (m := theorem1DenseGroupIndex C beta gamma + 1) noiseLaw _ _
  have hgroup_le :
      (theorem1IntegerGroupCount upper
        (theorem1DenseGroupIndex C beta gamma + 1) : ℝ) *
        AppliedModelingLib.Matching.topOrderDeviationProbability
          (Measure.pi (fun _ : Fin
            (theorem1DenseGroupIndex C beta gamma + 1) => noiseLaw))
          (theorem1DenseGroupCenter noiseLaw C beta gamma)
          (theorem1DenseDeviationRadius C beta gamma) ≤
      (3 * Real.rpow (C : ℝ) (1 - theorem1TailPhi2 beta gamma)) *
        AppliedModelingLib.Matching.topOrderDeviationProbability
          (Measure.pi (fun _ : Fin
            (theorem1DenseGroupIndex C beta gamma + 1) => noiseLaw))
          (theorem1DenseGroupCenter noiseLaw C beta gamma)
          (theorem1DenseDeviationRadius C beta gamma) :=
    mul_le_mul_of_nonneg_right hcount herror_nonneg
  have hstatic := theorem1_literal_selected_dense_low_matched_mass_le_of_ranked_window
    noiseLaw eta (inst C) hbeta.1 hgamma halpha_nonneg hholder hC_pos start
    hstart_window hdense hradius htail_normalization
  calc
    eventMass
        ((inst C).studentLaw.prod
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)))
        (fun outcome : StudentType × (Fin (C + 1) → ℝ) =>
          (inst C).value outcome.1 ∈ Set.Iic vS ∧
            chosenInActive
              ((inst C).literal.demand.demandAt
                (inst C).literal.selectedCutoff)
              (Finset.univ : Finset (Fin (C + 1))) outcome) ≤
        alpha * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)) +
          (theorem1IntegerGroupCount upper
            (theorem1DenseGroupIndex C beta gamma + 1) : ℝ) *
            AppliedModelingLib.Matching.topOrderDeviationProbability
              (Measure.pi (fun _ : Fin
                (theorem1DenseGroupIndex C beta gamma + 1) => noiseLaw))
              (theorem1DenseGroupCenter noiseLaw C beta gamma)
              (theorem1DenseDeviationRadius C beta gamma) +
          holderConstant * Real.rpow
            (5 * theorem1DenseDeviationRadius C beta gamma) gamma +
          2 * totalSupply *
            AppliedModelingLib.Matching.topOrderDeviationProbability
              (Measure.pi (fun _ : Fin
                (theorem1DenseGroupIndex C beta gamma + 1) => noiseLaw))
              (theorem1DenseGroupCenter noiseLaw C beta gamma)
              (theorem1DenseDeviationRadius C beta gamma) := by
        simpa [upper] using hstatic
    _ ≤ denseBound C := by
      change _ ≤
        alpha * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)) +
          (3 * Real.rpow (C : ℝ) (1 - theorem1TailPhi2 beta gamma)) *
            AppliedModelingLib.Matching.topOrderDeviationProbability
              (Measure.pi (fun _ : Fin
                (theorem1DenseGroupIndex C beta gamma + 1) => noiseLaw))
              (theorem1DenseGroupCenter noiseLaw C beta gamma)
              (theorem1DenseDeviationRadius C beta gamma) +
          holderConstant * Real.rpow
            (5 * theorem1DenseDeviationRadius C beta gamma) gamma +
          2 * totalSupply *
            AppliedModelingLib.Matching.topOrderDeviationProbability
              (Measure.pi (fun _ : Fin
                (theorem1DenseGroupIndex C beta gamma + 1) => noiseLaw))
              (theorem1DenseGroupCenter noiseLaw C beta gamma)
              (theorem1DenseDeviationRadius C beta gamma)
      exact add_le_add_left
        (add_le_add_left (add_le_add_right hgroup_le _) _) _
    _ < epsilon := hbound_small

end

end PG24NoisyMatchingMarkets
