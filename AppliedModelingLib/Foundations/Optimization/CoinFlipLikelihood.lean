import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Binary Log-Likelihood Geometry

Paper-neutral strict-concavity facts for the log likelihood of positive
success and failure weights.  The maximum calculation belongs here because it
recurs in binary random-utility and pairwise-comparison likelihood arguments.
-/

namespace AppliedModelingLib

/-- The real log likelihood for positive weighted binary outcomes. -/
noncomputable def coinFlipLogLikelihood (heads tails probability : ℝ) : ℝ :=
  heads * Real.log probability + tails * Real.log (1 - probability)

/-- Positive multiplication preserves strict concavity of a real-valued function. -/
theorem StrictConcaveOn.const_mul_pos
    {s : Set ℝ} {objective : ℝ → ℝ} {weight : ℝ}
    (hobjective : StrictConcaveOn ℝ s objective) (hweight : 0 < weight) :
    StrictConcaveOn ℝ s (fun point => weight * objective point) := by
  refine ⟨hobjective.1, ?_⟩
  intro first hfirst second hsecond hne left right hleft hright hsum
  have hstrict := hobjective.2 hfirst hsecond hne hleft hright hsum
  have hscaled := mul_lt_mul_of_pos_left hstrict hweight
  convert hscaled using 1
  all_goals simp only [smul_eq_mul]
  all_goals ring_nf

/-- `p ↦ log (1-p)` is strictly concave on the open unit interval. -/
theorem strictConcaveOn_log_one_sub_Ioo :
    StrictConcaveOn ℝ (Set.Ioo (0 : ℝ) 1) (fun probability => Real.log (1 - probability)) := by
  refine ⟨convex_Ioo (0 : ℝ) 1, ?_⟩
  intro first hfirst second hsecond hne left right hleft hright hsum
  have hfirstPos : 1 - first ∈ Set.Ioi (0 : ℝ) := by
    exact sub_pos.mpr hfirst.2
  have hsecondPos : 1 - second ∈ Set.Ioi (0 : ℝ) := by
    exact sub_pos.mpr hsecond.2
  have himageNe : 1 - first ≠ 1 - second := by
    intro heq
    apply hne
    linarith
  have hstrict := strictConcaveOn_log_Ioi.2
    hfirstPos hsecondPos himageNe hleft hright hsum
  have hcombine :
      left * (1 - first) + right * (1 - second) =
        1 - (left * first + right * second) := by
    nlinarith
  calc
    left * Real.log (1 - first) + right * Real.log (1 - second) <
        Real.log (left * (1 - first) + right * (1 - second)) := by
          simpa only [smul_eq_mul] using hstrict
    _ = Real.log (1 - (left * first + right * second)) := by rw [hcombine]

/-- The positive-weight binary log likelihood is strictly concave on `(0,1)`. -/
theorem coinFlipLogLikelihood_strictConcave
    {heads tails : ℝ} (hheads : 0 < heads) (htails : 0 < tails) :
    StrictConcaveOn ℝ (Set.Ioo (0 : ℝ) 1)
      (coinFlipLogLikelihood heads tails) := by
  unfold coinFlipLogLikelihood
  have hheadsLog : StrictConcaveOn ℝ (Set.Ioo (0 : ℝ) 1)
      (fun probability => heads * Real.log probability) := by
    refine StrictConcaveOn.const_mul_pos ?_ hheads
    exact strictConcaveOn_log_Ioi.subset (fun _ hpoint => hpoint.1) (convex_Ioo 0 1)
  have htailsLog : StrictConcaveOn ℝ (Set.Ioo (0 : ℝ) 1)
      (fun probability => tails * Real.log (1 - probability)) :=
    StrictConcaveOn.const_mul_pos strictConcaveOn_log_one_sub_Ioo htails
  exact hheadsLog.add htailsLog

/-- The tangent upper bound for `log` at a positive anchor. -/
theorem log_le_log_add_sub_div
    {value anchor : ℝ} (hvalue : 0 < value) (hanchor : 0 < anchor) :
    Real.log value ≤ Real.log anchor + (value - anchor) / anchor := by
  have hratio := Real.log_le_sub_one_of_pos (div_pos hvalue hanchor)
  rw [Real.log_div hvalue.ne' hanchor.ne'] at hratio
  calc
    Real.log value = (Real.log value - Real.log anchor) + Real.log anchor := by ring
    _ ≤ (value / anchor - 1) + Real.log anchor := by
      simpa only [add_comm] using add_le_add_right hratio (Real.log anchor)
    _ = Real.log anchor + (value - anchor) / anchor := by field

/--
Positive weighted binary log likelihood is maximized on the open unit interval
at the empirical success frequency `heads / (heads + tails)`.
-/
theorem coinFlipLogLikelihood_isMaxOn
    {heads tails : ℝ} (hheads : 0 < heads) (htails : 0 < tails) :
    IsMaxOn (coinFlipLogLikelihood heads tails) (Set.Ioo (0 : ℝ) 1)
      (heads / (heads + tails)) := by
  let maximizer : ℝ := heads / (heads + tails)
  have htotal : 0 < heads + tails := add_pos hheads htails
  have hmaxPos : 0 < maximizer := by
    dsimp [maximizer]
    exact div_pos hheads htotal
  have hmaxLt : maximizer < 1 := by
    dsimp [maximizer]
    exact (div_lt_one htotal).mpr (lt_add_of_pos_right heads htails)
  have hmaxMem : maximizer ∈ Set.Ioo (0 : ℝ) 1 := ⟨hmaxPos, hmaxLt⟩
  change ∀ ⦃probability⦄, probability ∈ Set.Ioo (0 : ℝ) 1 →
    coinFlipLogLikelihood heads tails probability ≤
      coinFlipLogLikelihood heads tails maximizer
  intro probability hprobability
  have hprobabilityPos : 0 < probability := hprobability.1
  have hfailurePos : 0 < 1 - probability := sub_pos.mpr hprobability.2
  have hmaxFailurePos : 0 < 1 - maximizer := sub_pos.mpr hmaxLt
  have hsuccessTangent := log_le_log_add_sub_div hprobabilityPos hmaxPos
  have hfailureTangent := log_le_log_add_sub_div hfailurePos hmaxFailurePos
  have hsuccessScaled :
      heads * Real.log probability ≤
        heads * (Real.log maximizer + (probability - maximizer) / maximizer) :=
    mul_le_mul_of_nonneg_left hsuccessTangent hheads.le
  have hfailureScaled :
      tails * Real.log (1 - probability) ≤
        tails *
          (Real.log (1 - maximizer) + ((1 - probability) - (1 - maximizer)) /
            (1 - maximizer)) :=
    mul_le_mul_of_nonneg_left hfailureTangent htails.le
  have hcancel :
      heads * (probability - maximizer) / maximizer +
          tails * ((1 - probability) - (1 - maximizer)) / (1 - maximizer) = 0 := by
    dsimp [maximizer]
    field_simp [hheads.ne', htails.ne', htotal.ne']
    ring
  unfold coinFlipLogLikelihood
  calc
    heads * Real.log probability + tails * Real.log (1 - probability) ≤
        heads * (Real.log maximizer + (probability - maximizer) / maximizer) +
          tails *
            (Real.log (1 - maximizer) + ((1 - probability) - (1 - maximizer)) /
              (1 - maximizer)) :=
      add_le_add hsuccessScaled hfailureScaled
    _ = heads * Real.log maximizer + tails * Real.log (1 - maximizer) := by
      calc
        _ = heads * Real.log maximizer + tails * Real.log (1 - maximizer) +
              (heads * (probability - maximizer) / maximizer +
                tails * ((1 - probability) - (1 - maximizer)) / (1 - maximizer)) := by ring
        _ = heads * Real.log maximizer + tails * Real.log (1 - maximizer) := by rw [hcancel, add_zero]

/-- The positive weighted binary log likelihood has a unique maximum on `(0,1)`. -/
theorem coinFlipLogLikelihood_existsUnique_isMaxOn
    {heads tails : ℝ} (hheads : 0 < heads) (htails : 0 < tails) :
    ∃! maximizer,
      maximizer ∈ Set.Ioo (0 : ℝ) 1 ∧
        IsMaxOn (coinFlipLogLikelihood heads tails) (Set.Ioo (0 : ℝ) 1) maximizer := by
  let maximizer : ℝ := heads / (heads + tails)
  have htotal : 0 < heads + tails := add_pos hheads htails
  have hmaxPos : 0 < maximizer := by
    dsimp [maximizer]
    exact div_pos hheads htotal
  have hmaxLt : maximizer < 1 := by
    dsimp [maximizer]
    exact (div_lt_one htotal).mpr (lt_add_of_pos_right heads htails)
  have hmaxMem : maximizer ∈ Set.Ioo (0 : ℝ) 1 := ⟨hmaxPos, hmaxLt⟩
  have hmax : IsMaxOn (coinFlipLogLikelihood heads tails) (Set.Ioo (0 : ℝ) 1) maximizer := by
    simpa only [maximizer] using coinFlipLogLikelihood_isMaxOn hheads htails
  refine ⟨maximizer, ⟨hmaxMem, hmax⟩, ?_⟩
  intro other hother
  exact (coinFlipLogLikelihood_strictConcave hheads htails).eq_of_isMaxOn
    hother.2 hmax hother.1 hmaxMem

/--
On the open unit interval, equality with the positive-weight coin-flip
likelihood's maximum occurs only at the empirical success frequency.
-/
theorem coinFlipLogLikelihood_eq_maximizer
    {heads tails probability : ℝ} (hheads : 0 < heads) (htails : 0 < tails)
    (hprobability : probability ∈ Set.Ioo (0 : ℝ) 1)
    (heq : coinFlipLogLikelihood heads tails probability =
      coinFlipLogLikelihood heads tails (heads / (heads + tails))) :
    probability = heads / (heads + tails) := by
  have hmax : IsMaxOn (coinFlipLogLikelihood heads tails) (Set.Ioo (0 : ℝ) 1)
      (heads / (heads + tails)) :=
    coinFlipLogLikelihood_isMaxOn hheads htails
  have hmaxAtProbability :
      IsMaxOn (coinFlipLogLikelihood heads tails) (Set.Ioo (0 : ℝ) 1) probability := by
    intro other hother
    rw [heq]
    exact hmax hother
  have htotal : 0 < heads + tails := add_pos hheads htails
  have hmaxMem : heads / (heads + tails) ∈ Set.Ioo (0 : ℝ) 1 := by
    exact ⟨div_pos hheads htotal,
      (div_lt_one htotal).mpr (lt_add_of_pos_right heads htails)⟩
  exact (coinFlipLogLikelihood_strictConcave hheads htails).eq_of_isMaxOn
    hmaxAtProbability hmax hprobability hmaxMem

/--
Above its empirical-frequency maximizer, the positive-weight coin-flip log
likelihood is strictly decreasing.  This order form is useful when a
pairwise-comparison score gap is shifted a little toward its perfect-fit
distance.
-/
theorem coinFlipLogLikelihood_strictDecrease_above_maximizer
    {heads tails lower upper : ℝ} (hheads : 0 < heads) (htails : 0 < tails)
    (hlower : lower ∈ Set.Ioo (0 : ℝ) 1) (hupper : upper ∈ Set.Ioo (0 : ℝ) 1)
    (hmaxLower : heads / (heads + tails) < lower) (hlowerUpper : lower < upper) :
    coinFlipLogLikelihood heads tails upper < coinFlipLogLikelihood heads tails lower := by
  have hmax : IsMaxOn (coinFlipLogLikelihood heads tails) (Set.Ioo (0 : ℝ) 1)
      (heads / (heads + tails)) := coinFlipLogLikelihood_isMaxOn hheads htails
  have hlowerLtMax :
      coinFlipLogLikelihood heads tails lower <
        coinFlipLogLikelihood heads tails (heads / (heads + tails)) := by
    refine lt_of_le_of_ne (hmax hlower) ?_
    intro heq
    have heqMax := coinFlipLogLikelihood_eq_maximizer hheads htails hlower heq
    exact (ne_of_gt hmaxLower) heqMax
  have hmaxMem : heads / (heads + tails) ∈ Set.Ioo (0 : ℝ) 1 := by
    have htotal : 0 < heads + tails := add_pos hheads htails
    exact ⟨div_pos hheads htotal,
      (div_lt_one htotal).mpr (lt_add_of_pos_right heads htails)⟩
  have hstrictAnti : StrictAntiOn (coinFlipLogLikelihood heads tails)
      (Set.Ioo (0 : ℝ) 1 ∩ Set.Ici lower) :=
    (coinFlipLogLikelihood_strictConcave hheads htails).concaveOn.strictAntiOn
      hmaxMem hmaxLower hlowerLtMax
  exact hstrictAnti ⟨hlower, Set.mem_Ici.mpr le_rfl⟩
    ⟨hupper, Set.mem_Ici.mpr hlowerUpper.le⟩ hlowerUpper

end AppliedModelingLib
