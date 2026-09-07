import AppliedModelingLib.Learning.Prediction.Approximation
import AppliedModelingLib.Learning.Statistics.FiniteRademacher
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Finset.Sort
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Threshold bases on the unit interval

This file supplies the real-interval discretization layer for threshold-basis
constructions from Lipschitz or bounded-variation loss derivatives.  The
finite-grid coefficient algebra lives in `ThresholdBasis`; here a point of
`[0,1]` is rounded down to a uniform grid.
-/

namespace AppliedModelingLib.Learning.Prediction

/-- A real-valued point in the probability-report interval. -/
abbrev UnitIntervalPoint := Set.Icc (0 : ℝ) 1

/-- A binary loss whose report coordinate is one-Lipschitz on the probability
interval, separately for each outcome. -/
def IsUnitIntervalLipschitzBinaryLoss (loss : BinaryLoss) : Prop :=
  ∀ outcome : Bool, LipschitzWith 1 (fun point : UnitIntervalPoint => loss point.1 outcome)

/-- A binary loss whose report coordinate is convex on the probability
interval, separately for each outcome.  This is independent of properness:
the convex ReLU construction uses convexity of the two loss coordinates
themselves before taking their discrete-derivative difference. -/
def IsUnitIntervalConvexBinaryLoss (loss : BinaryLoss) : Prop :=
  ∀ outcome : Bool, ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (fun report => loss report outcome)

/-- The discrete-derivative class of a binary-loss family, restricted to valid
probability reports.  This is the target class for one-dimensional threshold
bases in omniprediction. -/
def unitIntervalDiscreteDerivativeClass (losses : Set BinaryLoss) :
    Set (UnitIntervalPoint → ℝ) :=
  { derivative | ∃ loss ∈ losses, derivative = fun point => discreteDerivative loss point.1 }

/-- View a class of subtype-valued probability reports as an ordinary
real-valued hypothesis class.  This is the coercion bridge between the
one-dimensional threshold basis and the omniprediction reduction. -/
def unitIntervalPointHypothesisClass {X : Type*}
    (hypotheses : Set (X → UnitIntervalPoint)) : Set (X → ℝ) :=
  { hypothesis | ∃ source ∈ hypotheses, hypothesis = fun point => (source point).1 }

/-- Every hypothesis obtained by forgetting the interval subtype still takes
values in the unit interval. -/
theorem unitIntervalPointHypothesisClass_mem_HypothesisInUnitInterval
    {X : Type*} {hypotheses : Set (X → UnitIntervalPoint)}
    {hypothesis : X → ℝ} (hhypothesis : hypothesis ∈ unitIntervalPointHypothesisClass hypotheses) :
    HypothesisInUnitInterval hypothesis := by
  rcases hhypothesis with ⟨source, hsource, rfl⟩
  intro point
  exact (source point).2

/-- Discrete derivatives composed with subtype-valued reports are exactly the
ordinary derivative-hypothesis class after the report coercion. -/
theorem derivativeHypothesisClass_unitIntervalPointHypothesisClass_eq
    {X : Type*} (losses : Set BinaryLoss) (hypotheses : Set (X → UnitIntervalPoint)) :
    derivativeHypothesisClass losses (unitIntervalPointHypothesisClass hypotheses) =
      functionClassPostcompose (unitIntervalDiscreteDerivativeClass losses) hypotheses := by
  ext test
  constructor
  · rintro ⟨loss, hloss, hypothesis, ⟨source, hsource, rfl⟩, rfl⟩
    exact ⟨fun point => discreteDerivative loss point.1, ⟨loss, hloss, rfl⟩,
      source, hsource, rfl⟩
  · rintro ⟨derivative, ⟨loss, hloss, rfl⟩, hypothesis, hhypothesis, rfl⟩
    exact ⟨loss, hloss, fun point => (hypothesis point).1,
      ⟨hypothesis, hhypothesis, rfl⟩, rfl⟩

/-- A real function on the probability-report interval has total variation at
most `bound`.  Mathlib's `eVariationOn` is the supremum over finite monotone
partitions, which is the source paper's variation definition. -/
def HasTotalVariationAtMost (function : UnitIntervalPoint → ℝ) (bound : ℝ) : Prop :=
  eVariationOn function Set.univ ≤ ENNReal.ofReal bound

/-- A binary loss in the paper's bounded-variation class: it is unit bounded
on valid reports and its discrete derivative has total variation at most two. -/
def IsBoundedVariationBinaryLoss (loss : BinaryLoss) : Prop :=
  IsUnitBoundedBinaryLoss loss ∧
    HasTotalVariationAtMost (fun point : UnitIntervalPoint => discreteDerivative loss point.1) 2

/-- The centered, scaled Brier score.  It is a proper binary loss in `[-1, 1]`;
its discrete derivative ranges from `2` to `-2`. -/
def centeredBrierLoss : BinaryLoss :=
  fun report outcome => 2 * (report - binaryOutcomeValue outcome) ^ 2 - 1

/-- The centered Brier loss is bounded by one on the report interval. -/
theorem centeredBrierLoss_isUnitBounded : IsUnitBoundedBinaryLoss centeredBrierLoss := by
  intro report hreport outcome
  rcases hreport with ⟨hzero, hOne⟩
  unfold centeredBrierLoss binaryOutcomeValue
  cases outcome <;> simp
  · have hupperFactor : 0 ≤ report * (2 - report) := by
      exact mul_nonneg hzero (by linarith)
    constructor
    · nlinarith [sq_nonneg (report - 1)]
    · nlinarith [hupperFactor]
  · have hupperFactor : 0 ≤ report * (1 - report) := by
      exact mul_nonneg hzero (sub_nonneg.mpr hOne)
    constructor
    · nlinarith [sq_nonneg report]
    · nlinarith [hupperFactor]

/-- The centered Brier loss is proper. -/
theorem centeredBrierLoss_isProper : IsProperBinaryLoss centeredBrierLoss := by
  intro truth report htruth hreport
  unfold bernoulliRisk centeredBrierLoss binaryOutcomeValue
  norm_num
  nlinarith [sq_nonneg (report - truth)]

/-- The centered Brier loss has affine discrete derivative `2 - 4p`. -/
theorem discreteDerivative_centeredBrierLoss (report : ℝ) :
    discreteDerivative centeredBrierLoss report = 2 - 4 * report := by
  unfold discreteDerivative centeredBrierLoss binaryOutcomeValue
  norm_num
  ring

/-- The centered Brier derivative has variation greater than two.  Thus a
bounded proper loss need not belong to the paper's variation-two loss class. -/
theorem centeredBrierLoss_not_isBoundedVariationBinaryLoss :
    ¬ IsBoundedVariationBinaryLoss centeredBrierLoss := by
  intro hboundedVariation
  let zero : UnitIntervalPoint := ⟨0, by norm_num⟩
  let one : UnitIntervalPoint := ⟨1, by norm_num⟩
  have hzero : discreteDerivative centeredBrierLoss zero.1 = 2 := by
    rw [discreteDerivative_centeredBrierLoss]
    norm_num [zero]
  have hone : discreteDerivative centeredBrierLoss one.1 = -2 := by
    rw [discreteDerivative_centeredBrierLoss]
    norm_num [one]
  have hdistance := eVariationOn.edist_le
    (fun point : UnitIntervalPoint => discreteDerivative centeredBrierLoss point.1)
    (s := Set.univ) (Set.mem_univ zero) (Set.mem_univ one)
  change edist (discreteDerivative centeredBrierLoss zero.1)
    (discreteDerivative centeredBrierLoss one.1) ≤ _ at hdistance
  rw [hzero, hone] at hdistance
  have hcontradiction : ENNReal.ofReal 4 ≤ ENNReal.ofReal 2 := by
    calc
      ENNReal.ofReal 4 = edist (2 : ℝ) (-2 : ℝ) := by
        norm_num [edist_dist, Real.dist_eq]
      _ ≤ eVariationOn (fun point : UnitIntervalPoint =>
        discreteDerivative centeredBrierLoss point.1) Set.univ := hdistance
      _ ≤ ENNReal.ofReal 2 := hboundedVariation.2
  norm_num at hcontradiction

/-- Extend a finite monotone grid of unit-interval points to a monotone
sequence by keeping its final point thereafter.  This lets Mathlib's
natural-indexed variation API bound the adjacent variation of a finite grid. -/
noncomputable def finiteGridPointExtension {gridSize : ℕ}
    (grid : Fin (gridSize + 1) → UnitIntervalPoint) (index : ℕ) : UnitIntervalPoint :=
  if hindex : index ≤ gridSize then
    grid ⟨index, Nat.lt_succ_of_le hindex⟩
  else grid (Fin.last gridSize)

/-- The constant-tail extension of a monotone finite grid remains monotone. -/
theorem finiteGridPointExtension_monotone {gridSize : ℕ}
    (grid : Fin (gridSize + 1) → UnitIntervalPoint) (hgrid : Monotone grid) :
    Monotone (finiteGridPointExtension grid) := by
  intro lower upper hlowerUpper
  unfold finiteGridPointExtension
  by_cases hupper : upper ≤ gridSize
  · have hlower : lower ≤ gridSize := hlowerUpper.trans hupper
    simp only [dif_pos hlower, dif_pos hupper]
    apply hgrid
    exact_mod_cast hlowerUpper
  · by_cases hlower : lower ≤ gridSize
    · simp only [dif_pos hlower, dif_neg hupper]
      apply hgrid
      exact Fin.le_last _
    · simp only [dif_neg hlower, dif_neg hupper]
      exact le_rfl

/-- Sampling a function of total variation at most two on any finite monotone
grid has adjacent variation at most two. -/
theorem finiteGrid_sum_abs_sub_le_two_of_totalVariation {gridSize : ℕ}
    (function : UnitIntervalPoint → ℝ) (hvariation : HasTotalVariationAtMost function 2)
    (grid : Fin (gridSize + 1) → UnitIntervalPoint) (hgrid : Monotone grid) :
    (∑ level : Fin gridSize,
      |function (grid level.succ) - function (grid level.castSucc)|) ≤ 2 := by
  let extend : ℕ → UnitIntervalPoint := finiteGridPointExtension grid
  have hextend : Monotone extend := by
    exact finiteGridPointExtension_monotone grid hgrid
  have hextendSum :
      (∑ index ∈ Finset.range gridSize,
        edist (function (extend (index + 1))) (function (extend index))) =
      ∑ level : Fin gridSize,
        edist (function (grid level.succ)) (function (grid level.castSucc)) := by
    apply Finset.sum_bij (fun index hindex =>
      (⟨index, Finset.mem_range.mp hindex⟩ : Fin gridSize))
    · intro index hindex
      simp
    · intro first hfirst second hsecond hequal
      exact Fin.ext_iff.mp hequal
    · intro level _
      refine ⟨level.1, Finset.mem_range.mpr level.2, ?_⟩
      apply Fin.ext
      rfl
    · intro index hindex
      have hindexLt : index < gridSize := Finset.mem_range.mp hindex
      have hindexLe : index ≤ gridSize := Nat.le_of_lt hindexLt
      have hnextLe : index + 1 ≤ gridSize := by omega
      have hnext : extend (index + 1) = grid (Fin.succ ⟨index, hindexLt⟩) := by
        simp only [extend, finiteGridPointExtension, dif_pos hnextLe]
        apply congrArg grid
        apply Fin.ext
        rfl
      have hcurrent : extend index = grid (Fin.castSucc ⟨index, hindexLt⟩) := by
        simp only [extend, finiteGridPointExtension, dif_pos hindexLe]
        apply congrArg grid
        apply Fin.ext
        rfl
      rw [hnext, hcurrent]
  have hsum : ENNReal.ofReal (∑ level : Fin gridSize,
      |function (grid level.succ) - function (grid level.castSucc)|) ≤ ENNReal.ofReal 2 := by
    calc
      ENNReal.ofReal (∑ level : Fin gridSize,
          |function (grid level.succ) - function (grid level.castSucc)|) =
          ∑ level : Fin gridSize,
            ENNReal.ofReal |function (grid level.succ) - function (grid level.castSucc)| := by
            rw [ENNReal.ofReal_sum_of_nonneg]
            intro level _
            exact abs_nonneg _
      _ = ∑ level : Fin gridSize,
          edist (function (grid level.succ)) (function (grid level.castSucc)) := by
            apply Finset.sum_congr rfl
            intro level _
            rw [edist_dist, Real.dist_eq]
      _ = ∑ index ∈ Finset.range gridSize,
          edist (function (extend (index + 1))) (function (extend index)) := hextendSum.symm
      _ ≤ eVariationOn function Set.univ :=
        eVariationOn.sum_le hextend (fun _ => Set.mem_univ _)
      _ ≤ ENNReal.ofReal 2 := hvariation
  exact (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mp hsum

/-- The corrected threshold basis represents the sampled values of a
bounded-variation function exactly on every finite monotone grid. -/
theorem sampledFiniteGrid_isFiniteApproximateBasis_of_totalVariation {gridSize : ℕ}
    (function : UnitIntervalPoint → ℝ) (hbounded : ∀ point, |function point| ≤ 2)
    (hvariation : HasTotalVariationAtMost function 2)
    (grid : Fin (gridSize + 1) → UnitIntervalPoint) (hgrid : Monotone grid) :
    IsFiniteApproximateBasis ({fun level => function (grid level)} :
      Set (Fin (gridSize + 1) → ℝ))
      (Set.range (duplicatedZeroFiniteThresholdBasis (gridSize := gridSize)))
      0 (gridSize + 2) 3 := by
  apply finiteGrid_isFiniteApproximateBasis_of_range_and_variation
  · intro level
    exact hbounded (grid level)
  · exact finiteGrid_sum_abs_sub_le_two_of_totalVariation function hvariation grid hgrid

/-- An antitone range-two finite grid function has an exact threshold basis
with coefficient norm two.  Every threshold coordinate is duplicated so that
the representation remains within the source's individual coefficient bound
even when the derivative has a jump of size four. -/
theorem antitoneFiniteGrid_isFiniteApproximateBasis
    {gridSize : ℕ} (values : Fin (gridSize + 1) → ℝ) (hantitone : Antitone values)
    (hbounded : ∀ level, |values level| ≤ 2) :
    IsFiniteApproximateBasis ({values} : Set (Fin (gridSize + 1) → ℝ))
      (Set.range (finiteGridThreshold (n := gridSize + 1)))
      0 (2 * (gridSize + 1)) 2 := by
  intro target htarget
  have htargetEq : target = values := by simpa using htarget
  subst target
  refine ⟨2 * (gridSize + 1), doubledFiniteThresholdBasis,
    doubledFiniteThresholdBasisCoefficients values, le_rfl, ?_, ?_, ?_, ?_⟩
  · intro coordinate
    exact ⟨(finProdFinEquiv.symm coordinate).2, rfl⟩
  · intro coordinate
    apply abs_doubledFiniteThresholdBasisCoefficients_le_one
    intro level
    exact abs_finiteThresholdBasisCoefficients_le_two values hbounded level
  · rw [sum_abs_doubledFiniteThresholdBasisCoefficients]
    exact sum_abs_finiteThresholdBasisCoefficients_le_two values hantitone hbounded
  · intro report
    change |values report - ∑ coordinate,
      doubledFiniteThresholdBasisCoefficients values coordinate *
        doubledFiniteThresholdBasis coordinate report| ≤ 0
    rw [show (∑ coordinate,
      doubledFiniteThresholdBasisCoefficients values coordinate *
        doubledFiniteThresholdBasis coordinate report) =
        finiteThresholdBasisEvaluation values report from
          congrFun (doubledFiniteThresholdBasis_evaluation_eq values) report,
      finiteThresholdBasisEvaluation_eq]
    simp

/-- Restrict a class of report functions to the values of a finite grid. -/
def finiteGridSampleClass {gridSize : ℕ} (functions : Set (UnitIntervalPoint → ℝ))
    (grid : Fin (gridSize + 1) → UnitIntervalPoint) : Set (Fin (gridSize + 1) → ℝ) :=
  { values | ∃ function ∈ functions, values = fun level => function (grid level) }

/-- The signed-threshold class on a finite ordered report grid. -/
def finiteGridThresholdClass (gridSize : ℕ) : Set (Fin (gridSize + 1) → ℝ) :=
  Set.range (fun level : Fin (gridSize + 1) => finiteGridThreshold level)

/-- A signed threshold at a report value, with the positive side including
the threshold itself.  This is the Section 5 threshold convention. -/
noncomputable def signedThresholdAt (threshold : UnitIntervalPoint) : UnitIntervalPoint → ℝ :=
  fun report => if threshold ≤ report then 1 else -1

/-- A signed threshold has unit magnitude at every valid report. -/
@[simp] theorem abs_signedThresholdAt (threshold report : UnitIntervalPoint) :
    |signedThresholdAt threshold report| = 1 := by
  unfold signedThresholdAt
  split <;> norm_num

/-- Thresholds whose breakpoints belong to a particular finite report grid. -/
def gridThresholdClass {gridSize : ℕ} (grid : Fin (gridSize + 1) → UnitIntervalPoint) :
    Set (UnitIntervalPoint → ℝ) :=
  Set.range (fun level => signedThresholdAt (grid level))

/-- The duplicated-constant threshold family used to control coefficients is
a subfamily of the ordinary finite-grid threshold class. -/
theorem duplicatedZeroFiniteThresholdBasis_range_subset_finiteGridThresholdClass
    (gridSize : ℕ) :
    Set.range (duplicatedZeroFiniteThresholdBasis (gridSize := gridSize)) ⊆
      finiteGridThresholdClass gridSize := by
  intro basis hbasis
  rcases hbasis with ⟨coordinate, rfl⟩
  unfold duplicatedZeroFiniteThresholdBasis finiteGridThresholdClass
  refine Fin.cases ?_ (fun remaining => ?_) coordinate
  · exact ⟨0, rfl⟩
  · refine Fin.cases ?_ (fun level => ?_) remaining
    · exact ⟨0, rfl⟩
    · exact ⟨level.succ, rfl⟩

/-- A class of bounded-variation functions has the corrected finite threshold
basis after restriction to an arbitrary finite monotone grid. -/
theorem finiteGridSampleClass_isFiniteApproximateBasis_of_totalVariation {gridSize : ℕ}
    (functions : Set (UnitIntervalPoint → ℝ))
    (hbounded : ∀ function ∈ functions, ∀ point, |function point| ≤ 2)
    (hvariation : ∀ function ∈ functions, HasTotalVariationAtMost function 2)
    (grid : Fin (gridSize + 1) → UnitIntervalPoint) (hgrid : Monotone grid) :
    IsFiniteApproximateBasis (finiteGridSampleClass functions grid)
      (Set.range (duplicatedZeroFiniteThresholdBasis (gridSize := gridSize)))
      0 (gridSize + 2) 3 := by
  intro values hvalues
  rcases hvalues with ⟨function, hfunction, rfl⟩
  exact (sampledFiniteGrid_isFiniteApproximateBasis_of_totalVariation function
    (hbounded function hfunction) (hvariation function hfunction) grid hgrid)
    (fun level => function (grid level)) (by simp)

/-- On a finite report grid, unit-bounded proper losses have an exact
threshold basis even though they need not satisfy the variation-two condition.
Their antitone derivative gives the sharper coefficient norm two. -/
theorem finiteGridProperDerivativeSampleClass_isFiniteApproximateBasis
    {gridSize : ℕ} (losses : Set BinaryLoss)
    (hproper : ∀ loss ∈ losses, IsProperBinaryLoss loss)
    (hbounded : ∀ loss ∈ losses, IsUnitBoundedBinaryLoss loss)
    (grid : Fin (gridSize + 1) → UnitIntervalPoint) (hgrid : Monotone grid) :
    IsFiniteApproximateBasis
      (finiteGridSampleClass (unitIntervalDiscreteDerivativeClass losses) grid)
      (finiteGridThresholdClass gridSize) 0 (2 * (gridSize + 1)) 2 := by
  intro values hvalues
  rcases hvalues with ⟨function, ⟨loss, hloss, rfl⟩, rfl⟩
  have hgridReal : Monotone (fun level => (grid level).1) := fun lower upper hlowerUpper =>
    hgrid hlowerUpper
  have hantitone : Antitone (fun level => discreteDerivative loss (grid level).1) :=
    properDerivative_values_antitone (fun level => (grid level).1) (hproper loss hloss)
      hgridReal (fun level => (grid level).2)
  have hrange : ∀ level, |discreteDerivative loss (grid level).1| ≤ 2 := fun level =>
    discreteDerivative_abs_le_two_of_unitBounded (hbounded loss hloss) (grid level).2
  simpa [finiteGridThresholdClass] using
    (antitoneFiniteGrid_isFiniteApproximateBasis
      (fun level => discreteDerivative loss (grid level).1) hantitone hrange)
      (fun level => discreteDerivative loss (grid level).1) (by simp)

/-- The preceding finite-grid basis is preserved under arbitrary
post-composition by grid-index maps.  This is the finite-report bridge used
when a hypothesis class takes values in a finite ordered report grid. -/
theorem finiteGridSampleClassPostcompose_isFiniteApproximateBasis_of_totalVariation
    {X : Type*} {gridSize : ℕ} (functions : Set (UnitIntervalPoint → ℝ))
    (hbounded : ∀ function ∈ functions, ∀ point, |function point| ≤ 2)
    (hvariation : ∀ function ∈ functions, HasTotalVariationAtMost function 2)
    (grid : Fin (gridSize + 1) → UnitIntervalPoint) (hgrid : Monotone grid)
    (indexMaps : Set (X → Fin (gridSize + 1))) :
    IsFiniteApproximateBasis
      (functionClassPostcompose (finiteGridSampleClass functions grid) indexMaps)
      (functionClassPostcompose
        (Set.range (duplicatedZeroFiniteThresholdBasis (gridSize := gridSize))) indexMaps)
      0 (gridSize + 2) 3 := by
  exact finiteApproximateBasis_postcompose
    (finiteGridSampleClass_isFiniteApproximateBasis_of_totalVariation functions hbounded hvariation
      grid hgrid)

/-- The exact finite-grid proper-loss basis is preserved under arbitrary
post-composition by report-index maps. -/
theorem finiteGridProperDerivativeSampleClassPostcompose_isFiniteApproximateBasis
    {X : Type*} {gridSize : ℕ} (losses : Set BinaryLoss)
    (hproper : ∀ loss ∈ losses, IsProperBinaryLoss loss)
    (hbounded : ∀ loss ∈ losses, IsUnitBoundedBinaryLoss loss)
    (grid : Fin (gridSize + 1) → UnitIntervalPoint) (hgrid : Monotone grid)
    (indexMaps : Set (X → Fin (gridSize + 1))) :
    IsFiniteApproximateBasis
      (functionClassPostcompose
        (finiteGridSampleClass (unitIntervalDiscreteDerivativeClass losses) grid) indexMaps)
      (functionClassPostcompose (finiteGridThresholdClass gridSize) indexMaps)
      0 (2 * (gridSize + 1)) 2 := by
  exact finiteApproximateBasis_postcompose
    (finiteGridProperDerivativeSampleClass_isFiniteApproximateBasis losses hproper hbounded grid hgrid)

/-- After post-composition, the finite-grid bounded-variation basis may use
the ordinary finite threshold class rather than its coefficient-splitting
subfamily. -/
theorem finiteGridSampleClassPostcompose_isFiniteApproximateBasis_finiteGridThreshold
    {X : Type*} {gridSize : ℕ} (functions : Set (UnitIntervalPoint → ℝ))
    (hbounded : ∀ function ∈ functions, ∀ point, |function point| ≤ 2)
    (hvariation : ∀ function ∈ functions, HasTotalVariationAtMost function 2)
    (grid : Fin (gridSize + 1) → UnitIntervalPoint) (hgrid : Monotone grid)
    (indexMaps : Set (X → Fin (gridSize + 1))) :
    IsFiniteApproximateBasis
      (functionClassPostcompose (finiteGridSampleClass functions grid) indexMaps)
      (functionClassPostcompose (finiteGridThresholdClass gridSize) indexMaps)
      0 (gridSize + 2) 3 := by
  apply IsFiniteApproximateBasis.mono
    (finiteGridSampleClassPostcompose_isFiniteApproximateBasis_of_totalVariation
      functions hbounded hvariation grid hgrid indexMaps)
  · exact Set.Subset.rfl
  · intro basis hbasis
    rcases hbasis with ⟨function, hfunction, map, hmap, rfl⟩
    exact ⟨function,
      duplicatedZeroFiniteThresholdBasis_range_subset_finiteGridThresholdClass gridSize hfunction,
      map, hmap, rfl⟩

/-- Hypotheses obtained by composing a finite report grid with a class of
index maps. -/
def gridHypothesisClass {X : Type*} {gridSize : ℕ}
    (grid : Fin (gridSize + 1) → UnitIntervalPoint)
    (indexMaps : Set (X → Fin (gridSize + 1))) : Set (X → UnitIntervalPoint) :=
  { hypothesis | ∃ indexMap ∈ indexMaps, hypothesis = fun point => grid (indexMap point) }

/-- The index of a report in a finite report set, under its canonical ordered
enumeration. -/
noncomputable def finiteReportIndexMap {X : Type*} {gridSize : ℕ}
    (reports : Finset UnitIntervalPoint) (hcard : reports.card = gridSize + 1)
    (hypothesis : X → UnitIntervalPoint) (hvalues : ∀ point, hypothesis point ∈ reports) :
    X → Fin (gridSize + 1) :=
  fun point => (reports.orderIsoOfFin hcard).symm ⟨hypothesis point, hvalues point⟩

/-- The ordered report grid applied to the index of a report recovers that
report exactly. -/
theorem finiteReportIndexMap_apply {X : Type*} {gridSize : ℕ}
    (reports : Finset UnitIntervalPoint) (hcard : reports.card = gridSize + 1)
    (hypothesis : X → UnitIntervalPoint) (hvalues : ∀ point, hypothesis point ∈ reports)
    (point : X) :
    reports.orderEmbOfFin hcard (finiteReportIndexMap reports hcard hypothesis hvalues point) =
      hypothesis point := by
  exact congrArg Subtype.val ((reports.orderIsoOfFin hcard).apply_symm_apply
    ⟨hypothesis point, hvalues point⟩)

/-- The index-map representation of a hypothesis class whose reports all lie
in one finite ordered report set. -/
noncomputable def finiteReportIndexMapClass {X : Type*} {gridSize : ℕ}
    (reports : Finset UnitIntervalPoint) (hcard : reports.card = gridSize + 1)
    (hypotheses : Set (X → UnitIntervalPoint))
    (hvalues : ∀ hypothesis ∈ hypotheses, ∀ point, hypothesis point ∈ reports) :
    Set (X → Fin (gridSize + 1)) :=
  { indexMap | ∃ hypothesis, ∃ hhypothesis : hypothesis ∈ hypotheses,
    indexMap = finiteReportIndexMap reports hcard hypothesis
      (fun point => hvalues hypothesis hhypothesis point) }

/-- A finite-report hypothesis class is exactly the grid-hypothesis class of
its canonical ordered report-index maps. -/
theorem gridHypothesisClass_finiteReportIndexMapClass_eq {X : Type*} {gridSize : ℕ}
    (reports : Finset UnitIntervalPoint) (hcard : reports.card = gridSize + 1)
    (hypotheses : Set (X → UnitIntervalPoint))
    (hvalues : ∀ hypothesis ∈ hypotheses, ∀ point, hypothesis point ∈ reports) :
    gridHypothesisClass (reports.orderEmbOfFin hcard)
      (finiteReportIndexMapClass reports hcard hypotheses hvalues) = hypotheses := by
  ext hypothesis
  constructor
  · rintro ⟨indexMap, ⟨sourceHypothesis, hsourceHypothesis, hindexMap⟩, hrepresentation⟩
    rw [hindexMap] at hrepresentation
    rw [hrepresentation]
    convert hsourceHypothesis using 1
    funext point
    exact finiteReportIndexMap_apply reports hcard sourceHypothesis
      (fun point => hvalues sourceHypothesis hsourceHypothesis point) point
  · intro hhypothesis
    refine ⟨finiteReportIndexMap reports hcard hypothesis
      (fun point => hvalues hypothesis hhypothesis point), ?_, ?_⟩
    · exact ⟨hypothesis, hhypothesis, rfl⟩
    · funext point
      exact (finiteReportIndexMap_apply reports hcard hypothesis
        (fun point => hvalues hypothesis hhypothesis point) point).symm

/-- Under an order embedding of grid indices into report values, finite-grid
thresholds followed by index maps are exactly report thresholds followed by
the corresponding grid-valued hypotheses. -/
theorem finiteGridThreshold_postcompose_eq_gridThreshold_postcompose
    {X : Type*} {gridSize : ℕ} (grid : Fin (gridSize + 1) ↪o UnitIntervalPoint)
    (indexMaps : Set (X → Fin (gridSize + 1))) :
    functionClassPostcompose (finiteGridThresholdClass gridSize) indexMaps =
      functionClassPostcompose (gridThresholdClass grid) (gridHypothesisClass grid indexMaps) := by
  ext composite
  constructor
  · rintro ⟨function, ⟨level, rfl⟩, indexMap, hindexMap, rfl⟩
    refine ⟨signedThresholdAt (grid level), ⟨level, rfl⟩,
      (fun point => grid (indexMap point)), ⟨indexMap, hindexMap, rfl⟩, ?_⟩
    funext point
    unfold finiteGridThreshold signedThresholdAt
    change (if level ≤ indexMap point then 1 else -1) =
      if grid level ≤ grid (indexMap point) then 1 else -1
    by_cases hle : level ≤ indexMap point
    · have hgrid : grid level ≤ grid (indexMap point) := (grid.le_iff_le).2 hle
      simp [hle, hgrid]
    · have hgrid : ¬ grid level ≤ grid (indexMap point) := by
        intro hgrid
        exact hle ((grid.le_iff_le).1 hgrid)
      simp [hle, hgrid]
  · rintro ⟨function, ⟨level, rfl⟩, hypothesis, hhypothesis, rfl⟩
    rcases hhypothesis with ⟨indexMap, hindexMap, rfl⟩
    refine ⟨finiteGridThreshold level, ⟨level, rfl⟩, indexMap, hindexMap, ?_⟩
    funext point
    unfold finiteGridThreshold signedThresholdAt
    change (if grid level ≤ grid (indexMap point) then 1 else -1) =
      if level ≤ indexMap point then 1 else -1
    by_cases hle : level ≤ indexMap point
    · have hgrid : grid level ≤ grid (indexMap point) := (grid.le_iff_le).2 hle
      simp [hle, hgrid]
    · have hgrid : ¬ grid level ≤ grid (indexMap point) := by
        intro hgrid
        exact hle ((grid.le_iff_le).1 hgrid)
      simp [hle, hgrid]

/-- Restricting target functions to a finite grid before post-composition is
extensionally the same as post-composing them with hypotheses represented by
that grid. -/
theorem functionClassPostcompose_gridHypothesisClass_eq {X : Type*} {gridSize : ℕ}
    (functions : Set (UnitIntervalPoint → ℝ))
    (grid : Fin (gridSize + 1) → UnitIntervalPoint)
    (indexMaps : Set (X → Fin (gridSize + 1))) :
    functionClassPostcompose functions (gridHypothesisClass grid indexMaps) =
      functionClassPostcompose (finiteGridSampleClass functions grid) indexMaps := by
  ext composite
  constructor
  · rintro ⟨function, hfunction, hypothesis, hhypothesis, rfl⟩
    rcases hhypothesis with ⟨indexMap, hindexMap, rfl⟩
    exact ⟨fun level => function (grid level), ⟨function, hfunction, rfl⟩,
      indexMap, hindexMap, rfl⟩
  · rintro ⟨values, hvalues, indexMap, hindexMap, rfl⟩
    rcases hvalues with ⟨function, hfunction, rfl⟩
    exact ⟨function, hfunction, fun point => grid (indexMap point),
      ⟨indexMap, hindexMap, rfl⟩, rfl⟩

/-- The finite-grid threshold basis gives an exact coefficient-norm-three
representation for bounded-variation targets composed with grid-valued
hypotheses. -/
theorem gridHypothesisClass_isFiniteApproximateBasis_finiteGridThreshold
    {X : Type*} {gridSize : ℕ} (functions : Set (UnitIntervalPoint → ℝ))
    (hbounded : ∀ function ∈ functions, ∀ point, |function point| ≤ 2)
    (hvariation : ∀ function ∈ functions, HasTotalVariationAtMost function 2)
    (grid : Fin (gridSize + 1) → UnitIntervalPoint) (hgrid : Monotone grid)
    (indexMaps : Set (X → Fin (gridSize + 1))) :
    IsFiniteApproximateBasis
      (functionClassPostcompose functions (gridHypothesisClass grid indexMaps))
      (functionClassPostcompose (finiteGridThresholdClass gridSize) indexMaps)
      0 (gridSize + 2) 3 := by
  rw [functionClassPostcompose_gridHypothesisClass_eq]
  exact finiteGridSampleClassPostcompose_isFiniteApproximateBasis_finiteGridThreshold
    functions hbounded hvariation grid hgrid indexMaps

/-- Proper-loss derivatives composed with a grid-valued hypothesis class have
an exact finite threshold basis, without requiring a variation-two premise. -/
theorem gridHypothesisClass_properDerivative_isFiniteApproximateBasis_finiteGridThreshold
    {X : Type*} {gridSize : ℕ} (losses : Set BinaryLoss)
    (hproper : ∀ loss ∈ losses, IsProperBinaryLoss loss)
    (hbounded : ∀ loss ∈ losses, IsUnitBoundedBinaryLoss loss)
    (grid : Fin (gridSize + 1) → UnitIntervalPoint) (hgrid : Monotone grid)
    (indexMaps : Set (X → Fin (gridSize + 1))) :
    IsFiniteApproximateBasis
      (functionClassPostcompose (unitIntervalDiscreteDerivativeClass losses)
        (gridHypothesisClass grid indexMaps))
      (functionClassPostcompose (finiteGridThresholdClass gridSize) indexMaps)
      0 (2 * (gridSize + 1)) 2 := by
  rw [functionClassPostcompose_gridHypothesisClass_eq]
  exact finiteGridProperDerivativeSampleClassPostcompose_isFiniteApproximateBasis
    losses hproper hbounded grid hgrid indexMaps

/-- The same exact basis may be expressed using thresholds at the report
values of an ordered grid, rather than thresholds on its index type. -/
theorem gridHypothesisClass_isFiniteApproximateBasis_gridThreshold
    {X : Type*} {gridSize : ℕ} (functions : Set (UnitIntervalPoint → ℝ))
    (hbounded : ∀ function ∈ functions, ∀ point, |function point| ≤ 2)
    (hvariation : ∀ function ∈ functions, HasTotalVariationAtMost function 2)
    (grid : Fin (gridSize + 1) ↪o UnitIntervalPoint)
    (indexMaps : Set (X → Fin (gridSize + 1))) :
    IsFiniteApproximateBasis
      (functionClassPostcompose functions (gridHypothesisClass grid indexMaps))
      (functionClassPostcompose (gridThresholdClass grid) (gridHypothesisClass grid indexMaps))
      0 (gridSize + 2) 3 := by
  rw [← finiteGridThreshold_postcompose_eq_gridThreshold_postcompose grid indexMaps]
  exact gridHypothesisClass_isFiniteApproximateBasis_finiteGridThreshold
    functions hbounded hvariation grid grid.monotone indexMaps

/-- The proper-loss finite-grid basis can equivalently use thresholds at the
report values of an ordered grid. -/
theorem gridHypothesisClass_properDerivative_isFiniteApproximateBasis_gridThreshold
    {X : Type*} {gridSize : ℕ} (losses : Set BinaryLoss)
    (hproper : ∀ loss ∈ losses, IsProperBinaryLoss loss)
    (hbounded : ∀ loss ∈ losses, IsUnitBoundedBinaryLoss loss)
    (grid : Fin (gridSize + 1) ↪o UnitIntervalPoint)
    (indexMaps : Set (X → Fin (gridSize + 1))) :
    IsFiniteApproximateBasis
      (functionClassPostcompose (unitIntervalDiscreteDerivativeClass losses)
        (gridHypothesisClass grid indexMaps))
      (functionClassPostcompose (gridThresholdClass grid) (gridHypothesisClass grid indexMaps))
      0 (2 * (gridSize + 1)) 2 := by
  rw [← finiteGridThreshold_postcompose_eq_gridThreshold_postcompose grid indexMaps]
  exact gridHypothesisClass_properDerivative_isFiniteApproximateBasis_finiteGridThreshold
    losses hproper hbounded grid grid.monotone indexMaps

/-- For any finite set of valid report values, bounded-variation target
functions composed with a hypothesis class taking values in that set have an
exact finite threshold basis with coefficient norm three. -/
theorem finiteReportHypothesisClass_isFiniteApproximateBasis_gridThreshold
    {X : Type*} {gridSize : ℕ} (functions : Set (UnitIntervalPoint → ℝ))
    (hbounded : ∀ function ∈ functions, ∀ point, |function point| ≤ 2)
    (hvariation : ∀ function ∈ functions, HasTotalVariationAtMost function 2)
    (reports : Finset UnitIntervalPoint) (hcard : reports.card = gridSize + 1)
    (hypotheses : Set (X → UnitIntervalPoint))
    (hvalues : ∀ hypothesis ∈ hypotheses, ∀ point, hypothesis point ∈ reports) :
    IsFiniteApproximateBasis (functionClassPostcompose functions hypotheses)
      (functionClassPostcompose (gridThresholdClass (reports.orderEmbOfFin hcard)) hypotheses)
      0 (gridSize + 2) 3 := by
  rw [← gridHypothesisClass_finiteReportIndexMapClass_eq reports hcard hypotheses hvalues]
  exact gridHypothesisClass_isFiniteApproximateBasis_gridThreshold
    functions hbounded hvariation (reports.orderEmbOfFin hcard)
      (finiteReportIndexMapClass reports hcard hypotheses hvalues)

/-- The discrete derivatives of any bounded-variation loss family admit the
exact finite-report threshold basis after composition with hypotheses whose
reports lie in one finite report set. -/
theorem finiteReportDerivativeClass_isFiniteApproximateBasis_gridThreshold
    {X : Type*} {gridSize : ℕ} (losses : Set BinaryLoss)
    (hboundedVariation : ∀ loss ∈ losses, IsBoundedVariationBinaryLoss loss)
    (reports : Finset UnitIntervalPoint) (hcard : reports.card = gridSize + 1)
    (hypotheses : Set (X → UnitIntervalPoint))
    (hvalues : ∀ hypothesis ∈ hypotheses, ∀ point, hypothesis point ∈ reports) :
    IsFiniteApproximateBasis
      (functionClassPostcompose (unitIntervalDiscreteDerivativeClass losses) hypotheses)
      (functionClassPostcompose (gridThresholdClass (reports.orderEmbOfFin hcard)) hypotheses)
      0 (gridSize + 2) 3 := by
  apply finiteReportHypothesisClass_isFiniteApproximateBasis_gridThreshold
  · intro function hfunction point
    rcases hfunction with ⟨loss, hloss, rfl⟩
    exact discreteDerivative_abs_le_two_of_unitBounded
      (hboundedVariation loss hloss).1 point.2
  · intro function hfunction
    rcases hfunction with ⟨loss, hloss, rfl⟩
    exact (hboundedVariation loss hloss).2
  · exact hvalues

/--
On any fixed finite sample, a bounded-variation report function has an exact
signed-threshold representation at the sampled reports.  Unlike the printed
continuum construction in OKK25 Lemma 5.6, this result only orders the finite
set of report values actually observed on the sample, so point discontinuities
cause no gap.
-/
theorem boundedVariationFunction_sample_exact_signedThresholdRepresentation
    {X : Type*} {n : ℕ} (function : UnitIntervalPoint → ℝ)
    (hbounded : ∀ point, |function point| ≤ 2)
    (hvariation : HasTotalVariationAtMost function 2)
    (hypothesis : X → UnitIntervalPoint) (sample : Fin n → X) :
    ∃ (terms : ℕ) (coefficient : Fin terms → ℝ)
      (threshold : Fin terms → UnitIntervalPoint),
        (∑ term, |coefficient term|) ≤ 3 ∧
        ∀ index, function (hypothesis (sample index)) =
          ∑ term, coefficient term *
            signedThresholdAt (threshold term) (hypothesis (sample index)) := by
  classical
  by_cases hn : n = 0
  · subst n
    refine ⟨0, Fin.elim0, Fin.elim0, by norm_num, ?_⟩
    intro index
    exact Fin.elim0 index
  · let reports : Finset UnitIntervalPoint :=
      Finset.univ.image (fun index : Fin n => hypothesis (sample index))
    let initial : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
    have hreportsNonempty : reports.Nonempty := by
      refine ⟨hypothesis (sample initial), ?_⟩
      exact Finset.mem_image.mpr ⟨initial, Finset.mem_univ _, rfl⟩
    let gridSize : ℕ := reports.card - 1
    have hcard : reports.card = gridSize + 1 := by
      dsimp [gridSize]
      have hpositive : 0 < reports.card := Finset.card_pos.mpr hreportsNonempty
      omega
    let sampledHypothesis : Fin n → UnitIntervalPoint :=
      fun index => hypothesis (sample index)
    have hvalues : ∀ sampled ∈ ({sampledHypothesis} : Set (Fin n → UnitIntervalPoint)),
        ∀ index, sampled index ∈ reports := by
      intro sampled hsampled index
      have hsampledEq : sampled = sampledHypothesis := by simpa using hsampled
      subst sampled
      exact Finset.mem_image.mpr ⟨index, Finset.mem_univ _, rfl⟩
    have happrox := finiteReportHypothesisClass_isFiniteApproximateBasis_gridThreshold
      ({function} : Set (UnitIntervalPoint → ℝ))
      (by
        intro candidate hcandidate point
        have hcandidateEq : candidate = function := by simpa using hcandidate
        subst candidate
        exact hbounded point)
      (by
        intro candidate hcandidate
        have hcandidateEq : candidate = function := by simpa using hcandidate
        subst candidate
        exact hvariation)
      reports hcard ({sampledHypothesis} : Set (Fin n → UnitIntervalPoint)) hvalues
    have htarget : (fun index => function (hypothesis (sample index))) ∈
        functionClassPostcompose ({function} : Set (UnitIntervalPoint → ℝ))
          ({sampledHypothesis} : Set (Fin n → UnitIntervalPoint)) := by
      refine ⟨function, by simp, sampledHypothesis, by simp, ?_⟩
      rfl
    rcases happrox _ htarget with
      ⟨terms, basis, coefficient, _termsBound, hbasis, _coefficientBound,
        hnorm, herror⟩
    have hthreshold : ∀ term, ∃ threshold : UnitIntervalPoint, ∀ index,
        basis term index =
          signedThresholdAt threshold (hypothesis (sample index)) := by
      intro term
      rcases hbasis term with
        ⟨thresholdFunction, ⟨level, rfl⟩, sampled, hsampled, hbasisEq⟩
      have hsampledEq : sampled = sampledHypothesis := by simpa using hsampled
      subst sampled
      refine ⟨reports.orderEmbOfFin hcard level, ?_⟩
      intro index
      simpa [sampledHypothesis] using congrFun hbasisEq index
    let threshold : Fin terms → UnitIntervalPoint :=
      fun term => Classical.choose (hthreshold term)
    have hthresholdApply : ∀ term index,
        basis term index =
          signedThresholdAt (threshold term) (hypothesis (sample index)) := by
      intro term index
      exact Classical.choose_spec (hthreshold term) index
    refine ⟨terms, coefficient, threshold, hnorm, ?_⟩
    intro index
    have hzero : |function (hypothesis (sample index)) -
        finiteLinearCombination coefficient basis index| = 0 := by
      apply le_antisymm
      · exact herror index
      · exact abs_nonneg _
    calc
      function (hypothesis (sample index)) =
          finiteLinearCombination coefficient basis index := by
            exact sub_eq_zero.mp (abs_eq_zero.mp hzero)
      _ = ∑ term, coefficient term *
          signedThresholdAt (threshold term) (hypothesis (sample index)) := by
            unfold finiteLinearCombination
            apply Finset.sum_congr rfl
            intro term _
            rw [hthresholdApply]

/--
The corrected arbitrary-class, fixed-sample Rademacher reduction for
bounded-variation loss derivatives.  It is exact on the observed reports and
uses the signed closure of threshold-hypothesis pairs; this avoids both the
false continuum construction and the missing signs in the printed OKK25
Corollary 5.8.
-/
theorem boundedVariationDerivative_empiricalOneSidedRademacherSet_le_signedThreshold
    {X : Type*} {n : ℕ} (losses : Set BinaryLoss)
    (hypotheses : Set (X → UnitIntervalPoint)) (sample : Fin n → X)
    (hlosses : losses.Nonempty) (hhypotheses : hypotheses.Nonempty)
    (hboundedVariation : ∀ loss ∈ losses, IsBoundedVariationBinaryLoss loss) :
    AppliedModelingLib.Statistics.FiniteRademacher.empiricalOneSidedRademacherSet n
      (fun (target : { test : X → ℝ // test ∈
        functionClassPostcompose (unitIntervalDiscreteDerivativeClass losses) hypotheses })
        index => target.1 (sample index)) ≤
      3 * AppliedModelingLib.Statistics.FiniteRademacher.empiricalOneSidedRademacherSet n
        (fun (signedBasis : Bool ×
          (UnitIntervalPoint × { hypothesis : X → UnitIntervalPoint //
            hypothesis ∈ hypotheses })) index =>
          if signedBasis.1 then
            signedThresholdAt signedBasis.2.1 (signedBasis.2.2.1 (sample index))
          else -signedThresholdAt signedBasis.2.1 (signedBasis.2.2.1 (sample index))) := by
  classical
  have htargetNonempty : Nonempty { test : X → ℝ // test ∈
      functionClassPostcompose (unitIntervalDiscreteDerivativeClass losses) hypotheses } := by
    rcases hlosses with ⟨loss, hloss⟩
    rcases hhypotheses with ⟨hypothesis, hhypothesis⟩
    refine ⟨fun point => discreteDerivative loss (hypothesis point).1, ?_⟩
    exact ⟨fun report => discreteDerivative loss report.1, ⟨loss, hloss, rfl⟩,
      hypothesis, hhypothesis, rfl⟩
  letI : Nonempty { test : X → ℝ // test ∈
      functionClassPostcompose (unitIntervalDiscreteDerivativeClass losses) hypotheses } :=
    htargetNonempty
  have hbasisNonempty : Nonempty (UnitIntervalPoint ×
      { hypothesis : X → UnitIntervalPoint // hypothesis ∈ hypotheses }) := by
    rcases hhypotheses with ⟨hypothesis, hhypothesis⟩
    exact ⟨(⟨0, by norm_num⟩, ⟨hypothesis, hhypothesis⟩)⟩
  letI : Nonempty (UnitIntervalPoint ×
      { hypothesis : X → UnitIntervalPoint // hypothesis ∈ hypotheses }) := hbasisNonempty
  refine AppliedModelingLib.Statistics.FiniteRademacher.empiricalOneSidedRademacherSet_le_of_finite_l1_representation
      (Target := { test : X → ℝ // test ∈
        functionClassPostcompose (unitIntervalDiscreteDerivativeClass losses) hypotheses })
      (Basis := UnitIntervalPoint ×
        { hypothesis : X → UnitIntervalPoint // hypothesis ∈ hypotheses }) n
      (fun target index => target.1 (sample index))
      (fun basis index => signedThresholdAt basis.1 (basis.2.1 (sample index))) 3 ?_ ?_
  · intro signs
    refine ⟨(n : ℝ), ?_⟩
    rintro score ⟨signedBasis, rfl⟩
    calc
      (∑ index : Fin n, AppliedModelingLib.Probability.RademacherMatrix.rademacherSign
          (signs index) *
          (if signedBasis.1 then
            signedThresholdAt signedBasis.2.1 (signedBasis.2.2.1 (sample index))
          else -signedThresholdAt signedBasis.2.1 (signedBasis.2.2.1 (sample index)))) ≤
          |∑ index : Fin n, AppliedModelingLib.Probability.RademacherMatrix.rademacherSign
            (signs index) *
            (if signedBasis.1 then
              signedThresholdAt signedBasis.2.1 (signedBasis.2.2.1 (sample index))
            else -signedThresholdAt signedBasis.2.1 (signedBasis.2.2.1 (sample index)))| :=
          le_abs_self _
      _ ≤ ∑ index : Fin n, |AppliedModelingLib.Probability.RademacherMatrix.rademacherSign
          (signs index) *
          (if signedBasis.1 then
            signedThresholdAt signedBasis.2.1 (signedBasis.2.2.1 (sample index))
          else -signedThresholdAt signedBasis.2.1 (signedBasis.2.2.1 (sample index)))| := by
          simpa using Finset.abs_sum_le_sum_abs
            (fun index : Fin n =>
              AppliedModelingLib.Probability.RademacherMatrix.rademacherSign (signs index) *
                (if signedBasis.1 then
                  signedThresholdAt signedBasis.2.1 (signedBasis.2.2.1 (sample index))
                else -signedThresholdAt signedBasis.2.1 (signedBasis.2.2.1 (sample index))))
            Finset.univ
      _ = ∑ _index : Fin n, (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro index _
          rw [abs_mul, AppliedModelingLib.Probability.RademacherMatrix.abs_rademacherSign]
          by_cases hsign : signedBasis.1
          · simp [hsign]
          · simp [hsign]
      _ = n := by simp
  · intro target
    rcases target with ⟨targetFunction, htargetFunction⟩
    rcases htargetFunction with
      ⟨derivative, hderivative, hypothesis, hhypothesis, htargetEq⟩
    rcases hderivative with ⟨loss, hloss, hderivativeEq⟩
    have htargetEq' : targetFunction =
        fun point => discreteDerivative loss (hypothesis point).1 := by
      rw [hderivativeEq] at htargetEq
      exact htargetEq
    rcases boundedVariationFunction_sample_exact_signedThresholdRepresentation
      (fun point => discreteDerivative loss point.1)
      (fun point => discreteDerivative_abs_le_two_of_unitBounded
        (hboundedVariation loss hloss).1 point.2)
      (hboundedVariation loss hloss).2 hypothesis sample with
      ⟨terms, coefficient, threshold, hnorm, hrepresentation⟩
    refine ⟨terms, coefficient,
      fun term => (threshold term, ⟨hypothesis, hhypothesis⟩), hnorm, ?_⟩
    intro index
    change targetFunction (sample index) = _
    rw [htargetEq']
    simpa using hrepresentation index

/-- A multiaccuracy bound for finite-report threshold tests transfers to the
bounded-variation derivative-hypothesis class with coefficient factor three.
This is the exact-error finite-report instantiation of the generic
approximate-basis transfer theorem. -/
theorem finiteReportDerivativeClass_multiaccuracyBound_gridThreshold
    {X : Type*} {gridSize horizon : ℕ} (losses : Set BinaryLoss)
    (hboundedVariation : ∀ loss ∈ losses, IsBoundedVariationBinaryLoss loss)
    (reports : Finset UnitIntervalPoint) (hcard : reports.card = gridSize + 1)
    (hypotheses : Set (X → UnitIntervalPoint))
    (hvalues : ∀ hypothesis ∈ hypotheses, ∀ point, hypothesis point ∈ reports)
    (forecasts : ForecastSequence X horizon) (contexts : Fin horizon → X)
    (outcomes : Fin horizon → Bool) (basisError : ℝ)
    (hforecasts : ForecastsInUnitInterval forecasts contexts)
    (hthreshold : MultiaccuracyBound
      (functionClassPostcompose
        (gridThresholdClass (reports.orderEmbOfFin hcard)) hypotheses)
      forecasts contexts outcomes basisError)
    (hbasisError : 0 ≤ basisError) :
    MultiaccuracyBound
      (functionClassPostcompose (unitIntervalDiscreteDerivativeClass losses) hypotheses)
      forecasts contexts outcomes (3 * basisError) := by
  intro target htarget
  simpa using abs_multiaccuracyCorrelation_le_of_finiteApproximateBasis
    (finiteReportDerivativeClass_isFiniteApproximateBasis_gridThreshold losses
      hboundedVariation reports hcard hypotheses hvalues)
    htarget
    (forecastResidual_abs_le_one forecasts contexts outcomes hforecasts)
    hthreshold (by norm_num) hbasisError

/-- A finite family of range-two, variation-two functions on an ordered grid
has one-sided empirical Rademacher complexity controlled by three times the
complexity of its signed threshold coordinates.  The sign closure is required
because the threshold representation has signed coefficients. -/
theorem finiteGrid_boundedVariation_empiricalRademacher_le_signedThreshold
    {Target : Type*} [Fintype Target] [Nonempty Target] (gridSize : ℕ)
    (values : Target → Fin (gridSize + 1) → ℝ)
    (hbounded : ∀ target level, |values target level| ≤ 2)
    (hvariation : ∀ target,
      (∑ level : Fin gridSize,
        |values target level.succ - values target level.castSucc|) ≤ 2) :
    AppliedModelingLib.Statistics.FiniteRademacher.empiricalOneSidedRademacher
      (gridSize + 1) values ≤
      3 * AppliedModelingLib.Statistics.FiniteRademacher.empiricalOneSidedRademacher
        (gridSize + 1)
        (fun (signedLevel : Bool × Fin (gridSize + 2)) report =>
          if signedLevel.1 then
            duplicatedZeroFiniteThresholdBasis signedLevel.2 report
          else -duplicatedZeroFiniteThresholdBasis signedLevel.2 report) := by
  apply AppliedModelingLib.Statistics.FiniteRademacher.empiricalOneSidedRademacher_le_of_finite_l1_representation
  intro target
  rcases finiteGrid_isFiniteApproximateBasis_of_range_and_variation (values target)
    (hbounded target) (hvariation target) (values target) (by simp) with
      ⟨terms, basis, coefficient, _termsBound, hbasis, _coefficientBound,
        hnorm, happrox⟩
  let selected : Fin terms → Fin (gridSize + 2) :=
    fun term => Classical.choose (hbasis term)
  have hselected : ∀ term,
      duplicatedZeroFiniteThresholdBasis (selected term) = basis term := by
    intro term
    exact Classical.choose_spec (hbasis term)
  refine ⟨terms, coefficient, selected, hnorm, ?_⟩
  intro report
  have hzero : |values target report -
      finiteLinearCombination coefficient basis report| = 0 := by
    apply le_antisymm
    · exact happrox report
    · exact abs_nonneg _
  calc
    values target report = finiteLinearCombination coefficient basis report := by
      exact sub_eq_zero.mp (abs_eq_zero.mp hzero)
    _ = ∑ term, coefficient term *
        duplicatedZeroFiniteThresholdBasis (selected term) report := by
      unfold finiteLinearCombination
      apply Finset.sum_congr rfl
      intro term _
      rw [hselected]

/-- Bounded proper losses admit the same exact finite-report threshold
reduction directly.  This avoids the false claim that every such loss has
variation at most two. -/
theorem finiteReportProperDerivativeClass_isFiniteApproximateBasis_gridThreshold
    {X : Type*} {gridSize : ℕ} (losses : Set BinaryLoss)
    (hproper : ∀ loss ∈ losses, IsProperBinaryLoss loss)
    (hbounded : ∀ loss ∈ losses, IsUnitBoundedBinaryLoss loss)
    (reports : Finset UnitIntervalPoint) (hcard : reports.card = gridSize + 1)
    (hypotheses : Set (X → UnitIntervalPoint))
    (hvalues : ∀ hypothesis ∈ hypotheses, ∀ point, hypothesis point ∈ reports) :
    IsFiniteApproximateBasis
      (functionClassPostcompose (unitIntervalDiscreteDerivativeClass losses) hypotheses)
      (functionClassPostcompose (gridThresholdClass (reports.orderEmbOfFin hcard)) hypotheses)
      0 (2 * (gridSize + 1)) 2 := by
  rw [← gridHypothesisClass_finiteReportIndexMapClass_eq reports hcard hypotheses hvalues]
  exact gridHypothesisClass_properDerivative_isFiniteApproximateBasis_gridThreshold
    losses hproper hbounded (reports.orderEmbOfFin hcard)
      (finiteReportIndexMapClass reports hcard hypotheses hvalues)

/-- An antitone function with range in `[-2,2]` has total variation at most
four.  This distinguishes the bounded proper-loss derivative class from the
paper's variation-two class. -/
theorem antitone_hasTotalVariationAtMost_four
    (function : UnitIntervalPoint → ℝ) (hantitone : Antitone function)
    (hbounded : ∀ point, |function point| ≤ 2) :
    HasTotalVariationAtMost function 4 := by
  let zero : UnitIntervalPoint := ⟨0, by norm_num⟩
  let one : UnitIntervalPoint := ⟨1, by norm_num⟩
  have hIcc : Set.Icc zero one = Set.univ := by
    ext point
    constructor
    · intro _
      simp
    · intro _
      constructor
      · exact point.2.1
      · exact point.2.2
  have hnegMonotone : Monotone (fun point => -function point) := by
    intro lower upper hlowerUpper
    exact neg_le_neg (hantitone hlowerUpper)
  have hzero := hbounded zero
  have hone := hbounded one
  rw [abs_le] at hzero hone
  have hendpoint : (-function one) - (-function zero) ≤ 4 := by
    linarith
  have hnegVariation : eVariationOn (fun point => -function point) Set.univ ≤
      ENNReal.ofReal 4 := by
    rw [← hIcc]
    have hnegMonotoneOn : MonotoneOn (fun point => -function point) Set.univ :=
      hnegMonotone.monotoneOn Set.univ
    have hvariation := hnegMonotoneOn.eVariationOn_le
      (a := zero) (b := one) (Set.mem_univ _) (Set.mem_univ _)
    simpa [zero, one] using hvariation.trans (ENNReal.ofReal_le_ofReal hendpoint)
  have hneg_eq : eVariationOn function Set.univ =
      eVariationOn (fun point => -function point) Set.univ := by
    unfold eVariationOn
    congr 1 with pair
    apply Finset.sum_congr rfl
    intro index _
    rw [edist_dist, edist_dist, Real.dist_eq, Real.dist_eq]
    change ENNReal.ofReal |function (pair.2.1 (index + 1)) - function (pair.2.1 index)| =
      ENNReal.ofReal |-function (pair.2.1 (index + 1)) - -function (pair.2.1 index)|
    rw [show -function (pair.2.1 (index + 1)) - -function (pair.2.1 index) =
      -(function (pair.2.1 (index + 1)) - function (pair.2.1 index)) by ring, abs_neg]
  exact hneg_eq.trans_le hnegVariation

/-- A source-bounded proper binary loss has a discrete derivative with total
variation at most four.  The bound follows from antitonicity and the actual
`[-2,2]` derivative range. -/
theorem properDiscreteDerivative_hasTotalVariationAtMost_four
    {loss : BinaryLoss} (hproper : IsProperBinaryLoss loss)
    (hbounded : IsUnitBoundedBinaryLoss loss) :
    HasTotalVariationAtMost (fun point : UnitIntervalPoint => discreteDerivative loss point.1) 4 := by
  apply antitone_hasTotalVariationAtMost_four
  · intro lower upper hlowerUpper
    exact discreteDerivative_antitone_of_proper hproper lower.2 upper.2 hlowerUpper
  · intro point
    exact discreteDerivative_abs_le_two_of_unitBounded hbounded point.2

/-- The centered Brier derivative has total variation exactly four. -/
theorem centeredBrierLoss_derivative_totalVariation_eq_four :
    eVariationOn (fun point : UnitIntervalPoint =>
      discreteDerivative centeredBrierLoss point.1) Set.univ = ENNReal.ofReal 4 := by
  apply le_antisymm
  · exact properDiscreteDerivative_hasTotalVariationAtMost_four
      centeredBrierLoss_isProper centeredBrierLoss_isUnitBounded
  · let zero : UnitIntervalPoint := ⟨0, by norm_num⟩
    let one : UnitIntervalPoint := ⟨1, by norm_num⟩
    have hdistance := eVariationOn.edist_le
      (fun point : UnitIntervalPoint => discreteDerivative centeredBrierLoss point.1)
      (s := Set.univ) (Set.mem_univ zero) (Set.mem_univ one)
    change edist (discreteDerivative centeredBrierLoss zero.1)
      (discreteDerivative centeredBrierLoss one.1) ≤ _ at hdistance
    rw [discreteDerivative_centeredBrierLoss, discreteDerivative_centeredBrierLoss] at hdistance
    norm_num [zero, one, edist_dist, Real.dist_eq] at hdistance ⊢
    exact hdistance

/-- The discrete derivative of a report-wise one-Lipschitz binary loss is
two-Lipschitz: it is a difference of its two outcome-coordinate losses. -/
theorem discreteDerivative_restrict_lipschitz_two
    {loss : BinaryLoss} (hLipschitz : IsUnitIntervalLipschitzBinaryLoss loss) :
    LipschitzWith 2 (fun point : UnitIntervalPoint => discreteDerivative loss point.1) := by
  refine LipschitzWith.of_le_add_mul 2 fun point other => ?_
  have htrue := (hLipschitz true).dist_le_mul point other
  have hfalse := (hLipschitz false).dist_le_mul point other
  have htrue' : |loss point.1 true - loss other.1 true| ≤ dist point other := by
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using htrue
  have hfalse' : |loss point.1 false - loss other.1 false| ≤ dist point other := by
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using hfalse
  have habs : |(loss point.1 true - loss point.1 false) -
      (loss other.1 true - loss other.1 false)| ≤ 2 * dist point other := by
    calc
    |(loss point.1 true - loss point.1 false) -
        (loss other.1 true - loss other.1 false)| =
        |(loss point.1 true - loss other.1 true) -
          (loss point.1 false - loss other.1 false)| := by ring_nf
    _ ≤ |loss point.1 true - loss other.1 true| +
          |loss point.1 false - loss other.1 false| := by
            simpa [abs_sub_comm] using (abs_sub_le (loss point.1 true - loss other.1 true) 0
              (loss point.1 false - loss other.1 false))
    _ ≤ 2 * dist point other := by linarith
  change loss point.1 true - loss point.1 false ≤
    loss other.1 true - loss other.1 false + 2 * dist point other
  calc
    loss point.1 true - loss point.1 false =
        (loss other.1 true - loss other.1 false) +
          ((loss point.1 true - loss point.1 false) -
            (loss other.1 true - loss other.1 false)) := by ring
    _ ≤ (loss other.1 true - loss other.1 false) +
          |(loss point.1 true - loss point.1 false) -
            (loss other.1 true - loss other.1 false)| := by
          gcongr
          exact le_abs_self _
    _ ≤ loss other.1 true - loss other.1 false + 2 * dist point other := by
          linarith

/-- A two-Lipschitz real function on the unit interval has total variation at
most two.  The proof factors through the variation of the identity map, whose
variation is exactly the length of the interval. -/
theorem twoLipschitz_hasTotalVariationAtMost_two
    (function : UnitIntervalPoint → ℝ) (hLipschitz : LipschitzWith 2 function) :
    HasTotalVariationAtMost function 2 := by
  let zero : UnitIntervalPoint := ⟨0, by norm_num⟩
  let one : UnitIntervalPoint := ⟨1, by norm_num⟩
  have hIcc : Set.Icc zero one = Set.univ := by
    ext point
    constructor
    · intro _
      simp
    · intro _
      constructor
      · exact point.2.1
      · exact point.2.2
  have hval : eVariationOn (fun point : UnitIntervalPoint => point.1) Set.univ =
      eVariationOn (id : UnitIntervalPoint → UnitIntervalPoint) Set.univ := by
    unfold eVariationOn
    congr 1 with pair index
  have hidentity : eVariationOn (id : UnitIntervalPoint → UnitIntervalPoint)
      (Set.univ : Set UnitIntervalPoint) ≤ ENNReal.ofReal 1 := by
    rw [← hval, ← hIcc]
    have hmonotone : MonotoneOn (fun point : UnitIntervalPoint => point.1) Set.univ := by
      intro point _ other _ hle
      exact hle
    simpa [zero, one] using hmonotone.eVariationOn_le (a := zero) (b := one)
      (Set.mem_univ _) (Set.mem_univ _)
  calc
    eVariationOn function Set.univ =
        eVariationOn (function ∘ (id : UnitIntervalPoint → UnitIntervalPoint)) Set.univ := by
      rfl
    _ ≤ (2 : NNReal) *
        (eVariationOn (id : UnitIntervalPoint → UnitIntervalPoint) Set.univ) := by
      exact hLipschitz.lipschitzOnWith.comp_eVariationOn_le
        (g := (id : UnitIntervalPoint → UnitIntervalPoint)) (s := Set.univ)
        (Set.mapsTo_univ _ _)
    _ ≤ (2 : NNReal) * ENNReal.ofReal 1 := by gcongr
    _ = ENNReal.ofReal 2 := by norm_num

/-- A report-wise one-Lipschitz binary loss has a discrete derivative with
total variation at most two on the valid report interval. -/
theorem discreteDerivative_hasTotalVariationAtMost_two
    {loss : BinaryLoss} (hLipschitz : IsUnitIntervalLipschitzBinaryLoss loss) :
    HasTotalVariationAtMost (fun point : UnitIntervalPoint => discreteDerivative loss point.1) 2 :=
  twoLipschitz_hasTotalVariationAtMost_two _
    (discreteDerivative_restrict_lipschitz_two hLipschitz)

/-- Every source-bounded, report-wise one-Lipschitz binary loss is a
bounded-variation binary loss. -/
theorem isBoundedVariationBinaryLoss_of_unitIntervalLipschitz
    {loss : BinaryLoss} (hbounded : IsUnitBoundedBinaryLoss loss)
    (hLipschitz : IsUnitIntervalLipschitzBinaryLoss loss) :
    IsBoundedVariationBinaryLoss loss :=
  ⟨hbounded, discreteDerivative_hasTotalVariationAtMost_two hLipschitz⟩

/-- The `level / gridSize` point of a positive uniform grid. -/
noncomputable def uniformGridPoint (gridSize : ℕ) (gridSizePositive : 0 < gridSize)
    (level : Fin (gridSize + 1)) : UnitIntervalPoint :=
  ⟨(level : ℝ) / (gridSize : ℝ), by
    constructor
    · positivity
    · apply (div_le_one (by exact_mod_cast gridSizePositive)).2
      exact_mod_cast Nat.le_of_lt_succ level.isLt⟩

/-- Round a probability report down to the index of its uniform-grid cell. -/
noncomputable def uniformGridFloor (gridSize : ℕ) (point : UnitIntervalPoint) :
    Fin (gridSize + 1) :=
  ⟨⌊(gridSize : ℝ) * point.1⌋₊, Nat.lt_succ_iff.mpr <|
    Nat.floor_le_of_le (by
      have hupper : point.1 ≤ 1 := point.2.2
      calc
        (gridSize : ℝ) * point.1 ≤ (gridSize : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left hupper (Nat.cast_nonneg gridSize)
        _ = (gridSize : ℝ) := by ring)⟩

/-- The continuous and discrete order tests agree after rounding a report
down.  The weak inequality deliberately includes an exact grid threshold, as
in the source convention `sgn (v - θ) = 1` at `v = θ`. -/
theorem uniformGridPoint_le_iff_le_uniformGridFloor
    (gridSize : ℕ) (gridSizePositive : 0 < gridSize)
    (level : Fin (gridSize + 1)) (point : UnitIntervalPoint) :
    (uniformGridPoint gridSize gridSizePositive level).1 ≤ point.1 ↔
      level ≤ uniformGridFloor gridSize point := by
  have hpositive : (0 : ℝ) < gridSize := by
    exact_mod_cast gridSizePositive
  have hnonnegative : 0 ≤ (gridSize : ℝ) * point.1 :=
    mul_nonneg (Nat.cast_nonneg gridSize) point.2.1
  constructor
  · intro hle
    change level.val ≤ ⌊(gridSize : ℝ) * point.1⌋₊
    rw [Nat.le_floor_iff hnonnegative]
    have hdiv : (level.val : ℝ) / (gridSize : ℝ) ≤ point.1 := by
      simpa [uniformGridPoint] using hle
    simpa [mul_comm] using (div_le_iff₀ hpositive).mp hdiv
  · intro hle
    change level.val ≤ ⌊(gridSize : ℝ) * point.1⌋₊ at hle
    have hcast : (level.val : ℝ) ≤
        (↑⌊(gridSize : ℝ) * point.1⌋₊ : ℝ) := by
      exact_mod_cast hle
    have hfloor : (↑⌊(gridSize : ℝ) * point.1⌋₊ : ℝ) ≤
        (gridSize : ℝ) * point.1 :=
      Nat.floor_le hnonnegative
    have hproduct : (level.val : ℝ) ≤ point.1 * (gridSize : ℝ) := by
      simpa [mul_comm] using hcast.trans hfloor
    have hdiv : (level.val : ℝ) / (gridSize : ℝ) ≤ point.1 :=
      (div_le_iff₀ hpositive).2 hproduct
    simpa [uniformGridPoint] using hdiv

/-- A signed threshold at a uniformly spaced point of `[0,1]`, using the
source paper's convention that equality is on the positive side. -/
noncomputable def uniformSignedThreshold
    (gridSize : ℕ) (gridSizePositive : 0 < gridSize)
    (level : Fin (gridSize + 1)) : UnitIntervalPoint → ℝ :=
  fun point => if (uniformGridPoint gridSize gridSizePositive level).1 ≤ point.1 then 1 else -1

/-- Rounding converts every real uniform threshold exactly into its finite
grid counterpart. -/
theorem uniformSignedThreshold_eq_finiteGridThreshold_floor
    (gridSize : ℕ) (gridSizePositive : 0 < gridSize)
    (level : Fin (gridSize + 1)) (point : UnitIntervalPoint) :
    uniformSignedThreshold gridSize gridSizePositive level point =
      finiteGridThreshold level (uniformGridFloor gridSize point) := by
  simp only [uniformSignedThreshold, finiteGridThreshold,
    uniformGridPoint_le_iff_le_uniformGridFloor]

/-- The uniform real threshold family with its constant coordinate duplicated.
The duplication is mathematically redundant, but ensures each coefficient of
the source-scale signed-threshold expansion belongs to `[-1,1]`. -/
noncomputable def duplicatedZeroUniformThresholdBasis
    (gridSize : ℕ) (gridSizePositive : 0 < gridSize) :
    Fin (gridSize + 2) → UnitIntervalPoint → ℝ :=
  Fin.cases (uniformSignedThreshold gridSize gridSizePositive 0)
    (fun coordinate => Fin.cases (uniformSignedThreshold gridSize gridSizePositive 0)
      (fun level => uniformSignedThreshold gridSize gridSizePositive level.succ) coordinate)

/-- The duplicated real threshold family agrees pointwise with the rounded
finite-grid family used by the coefficient calculation. -/
theorem duplicatedZeroUniformThresholdBasis_apply_eq
    (gridSize : ℕ) (gridSizePositive : 0 < gridSize)
    (coordinate : Fin (gridSize + 2)) (point : UnitIntervalPoint) :
    duplicatedZeroUniformThresholdBasis gridSize gridSizePositive coordinate point =
      duplicatedZeroFiniteThresholdBasis coordinate (uniformGridFloor gridSize point) := by
  unfold duplicatedZeroUniformThresholdBasis duplicatedZeroFiniteThresholdBasis
  refine Fin.cases ?_ ?_ coordinate
  · exact uniformSignedThreshold_eq_finiteGridThreshold_floor
      gridSize gridSizePositive 0 point
  · intro remaining
    refine Fin.cases ?_ ?_ remaining
    · exact uniformSignedThreshold_eq_finiteGridThreshold_floor
        gridSize gridSizePositive 0 point
    · intro level
      exact uniformSignedThreshold_eq_finiteGridThreshold_floor
        gridSize gridSizePositive level.succ point

/-- The lower grid representative never exceeds the report it rounds. -/
theorem uniformGridPoint_floor_le (gridSize : ℕ) (gridSizePositive : 0 < gridSize)
    (point : UnitIntervalPoint) :
    (uniformGridPoint gridSize gridSizePositive (uniformGridFloor gridSize point)).1 ≤ point.1 := by
  unfold uniformGridPoint
  dsimp
  apply (div_le_iff₀ (by exact_mod_cast gridSizePositive)).2
  simp only [uniformGridFloor]
  calc
    (↑⌊(gridSize : ℝ) * point.1⌋₊ : ℝ) ≤ (gridSize : ℝ) * point.1 :=
      Nat.floor_le (mul_nonneg (Nat.cast_nonneg gridSize) point.2.1)
    _ = point.1 * (gridSize : ℝ) := by ring

/-- A rounded report is strictly below the next grid point. -/
theorem uniformGridPoint_floor_lt_add_inverse
    (gridSize : ℕ) (gridSizePositive : 0 < gridSize) (point : UnitIntervalPoint) :
    point.1 <
      (uniformGridPoint gridSize gridSizePositive (uniformGridFloor gridSize point)).1 +
        1 / (gridSize : ℝ) := by
  have hnonneg : 0 ≤ (gridSize : ℝ) * point.1 :=
    mul_nonneg (Nat.cast_nonneg gridSize) point.2.1
  have hfloor : ⌊(gridSize : ℝ) * point.1⌋₊ <
      ⌊(gridSize : ℝ) * point.1⌋₊ + 1 := Nat.lt_succ_self _
  have hstrict : (gridSize : ℝ) * point.1 <
      (↑(⌊(gridSize : ℝ) * point.1⌋₊ + 1) : ℝ) :=
    (Nat.floor_lt hnonneg).mp hfloor
  calc
    point.1 = ((gridSize : ℝ) * point.1) / (gridSize : ℝ) := by
      field_simp [show (gridSize : ℝ) ≠ 0 by exact_mod_cast Nat.ne_of_gt gridSizePositive]
    _ < (↑(⌊(gridSize : ℝ) * point.1⌋₊ + 1) : ℝ) / (gridSize : ℝ) :=
      (div_lt_div_iff_of_pos_right (by exact_mod_cast gridSizePositive)).2 hstrict
    _ = (uniformGridPoint gridSize gridSizePositive
          (uniformGridFloor gridSize point)).1 + 1 / (gridSize : ℝ) := by
      simp only [uniformGridPoint, uniformGridFloor]
      push_cast
      ring

/-- Uniform-grid rounding changes a report by at most one grid width. -/
theorem abs_sub_uniformGridPoint_floor_le_inverse
    (gridSize : ℕ) (gridSizePositive : 0 < gridSize) (point : UnitIntervalPoint) :
    |point.1 - (uniformGridPoint gridSize gridSizePositive
      (uniformGridFloor gridSize point)).1| ≤ 1 / (gridSize : ℝ) := by
  have hlower := uniformGridPoint_floor_le gridSize gridSizePositive point
  have hupper := uniformGridPoint_floor_lt_add_inverse gridSize gridSizePositive point
  rw [abs_of_nonneg (sub_nonneg.mpr hlower)]
  linarith

/-- A two-Lipschitz function changes by at most `2 / gridSize` under uniform
rounding. -/
theorem abs_sub_twoLipschitz_uniformGridFloor_le
    (gridSize : ℕ) (gridSizePositive : 0 < gridSize)
    (function : UnitIntervalPoint → ℝ) (hLipschitz : LipschitzWith 2 function)
    (point : UnitIntervalPoint) :
    |function point - function
      (uniformGridPoint gridSize gridSizePositive (uniformGridFloor gridSize point))| ≤
      2 / (gridSize : ℝ) := by
  let rounded := uniformGridPoint gridSize gridSizePositive (uniformGridFloor gridSize point)
  have hdistance := hLipschitz.dist_le_mul point rounded
  have hrounding := abs_sub_uniformGridPoint_floor_le_inverse
    gridSize gridSizePositive point
  change |function point - function rounded| ≤ 2 / (gridSize : ℝ)
  calc
    |function point - function rounded| ≤ 2 * |point.1 - rounded.1| := by
      simpa only [Real.dist_eq, Subtype.dist_eq, NNReal.coe_two] using hdistance
    _ ≤ 2 * (1 / (gridSize : ℝ)) :=
      mul_le_mul_of_nonneg_left (by simpa [rounded, abs_sub_comm] using hrounding) (by norm_num)
    _ = 2 / (gridSize : ℝ) := by ring

/-- Consecutive points of the uniform grid are exactly one grid width apart. -/
theorem abs_sub_uniformGridPoint_succ_castSucc
    (gridSize : ℕ) (gridSizePositive : 0 < gridSize) (level : Fin gridSize) :
    |(uniformGridPoint gridSize gridSizePositive level.succ).1 -
      (uniformGridPoint gridSize gridSizePositive level.castSucc).1| =
      1 / (gridSize : ℝ) := by
  unfold uniformGridPoint
  dsimp
  have hdiff :
      ((↑(level.val + 1) : ℝ) / (gridSize : ℝ) -
        (↑level.val : ℝ) / (gridSize : ℝ)) = 1 / (gridSize : ℝ) := by
    push_cast
    field_simp [show (gridSize : ℝ) ≠ 0 by exact_mod_cast Nat.ne_of_gt gridSizePositive]
    ring
  rw [hdiff, abs_of_nonneg]
  exact one_div_nonneg.mpr (by exact_mod_cast Nat.le_of_lt gridSizePositive)

/-- The values of a two-Lipschitz function along the full uniform grid have
total adjacent variation at most two. -/
theorem sum_abs_sub_twoLipschitz_uniformGridPoint_le_two
    (gridSize : ℕ) (gridSizePositive : 0 < gridSize)
    (function : UnitIntervalPoint → ℝ) (hLipschitz : LipschitzWith 2 function) :
    (∑ level : Fin gridSize,
      |function (uniformGridPoint gridSize gridSizePositive level.succ) -
        function (uniformGridPoint gridSize gridSizePositive level.castSucc)|) ≤ 2 := by
  calc
    (∑ level : Fin gridSize,
      |function (uniformGridPoint gridSize gridSizePositive level.succ) -
        function (uniformGridPoint gridSize gridSizePositive level.castSucc)|) ≤
        ∑ _level : Fin gridSize, 2 * (1 / (gridSize : ℝ)) := by
          apply Finset.sum_le_sum
          intro level _
          have hdistance := hLipschitz.dist_le_mul
            (uniformGridPoint gridSize gridSizePositive level.succ)
            (uniformGridPoint gridSize gridSizePositive level.castSucc)
          calc
            |function (uniformGridPoint gridSize gridSizePositive level.succ) -
                function (uniformGridPoint gridSize gridSizePositive level.castSucc)| ≤
                2 * dist (uniformGridPoint gridSize gridSizePositive level.succ)
                  (uniformGridPoint gridSize gridSizePositive level.castSucc) := by
                    simpa only [Real.dist_eq, Subtype.dist_eq, NNReal.coe_two] using hdistance
            _ = 2 * |(uniformGridPoint gridSize gridSizePositive level.succ).1 -
                (uniformGridPoint gridSize gridSizePositive level.castSucc).1| := by
                  rw [Subtype.dist_eq, Real.dist_eq]
            _ = 2 * (1 / (gridSize : ℝ)) := by
              rw [abs_sub_uniformGridPoint_succ_castSucc gridSize gridSizePositive level]
    _ = (gridSize : ℝ) * (2 * (1 / (gridSize : ℝ))) := by
      simp [nsmul_eq_mul]
    _ = 2 := by
      field_simp [show (gridSize : ℝ) ≠ 0 by exact_mod_cast Nat.ne_of_gt gridSizePositive]

/-- Corrected threshold-basis theorem for one bounded two-Lipschitz function
on `[0,1]`.  Uniform rounding gives error `2 / n`; the duplicated constant
threshold enforces the individual coefficient restriction and yields
coefficient norm three with `n + 2` basis occurrences. -/
theorem twoLipschitz_isFiniteApproximateBasis_uniformThreshold
    (gridSize : ℕ) (gridSizePositive : 0 < gridSize)
    (function : UnitIntervalPoint → ℝ) (hbounded : ∀ point, |function point| ≤ 2)
    (hLipschitz : LipschitzWith 2 function) :
    IsFiniteApproximateBasis ({function} : Set (UnitIntervalPoint → ℝ))
      (Set.range (duplicatedZeroUniformThresholdBasis gridSize gridSizePositive))
      (2 / (gridSize : ℝ)) (gridSize + 2) 3 := by
  have hrounded : IsFiniteApproximateBasis ({function} : Set (UnitIntervalPoint → ℝ))
      (Set.range (fun coordinate point =>
        duplicatedZeroFiniteThresholdBasis coordinate
          (uniformGridFloor gridSize point)))
      (2 / (gridSize : ℝ)) (gridSize + 2) 3 := by
    apply roundedFiniteGrid_isFiniteApproximateBasis_of_range_and_variation
      function (uniformGridFloor gridSize)
      (fun level => function (uniformGridPoint gridSize gridSizePositive level))
      (2 / (gridSize : ℝ))
    · intro point
      exact abs_sub_twoLipschitz_uniformGridFloor_le gridSize gridSizePositive
        function hLipschitz point
    · intro level
      exact hbounded (uniformGridPoint gridSize gridSizePositive level)
    · exact sum_abs_sub_twoLipschitz_uniformGridPoint_le_two
        gridSize gridSizePositive function hLipschitz
  have hbasis : duplicatedZeroUniformThresholdBasis gridSize gridSizePositive =
      fun coordinate point => duplicatedZeroFiniteThresholdBasis coordinate
        (uniformGridFloor gridSize point) := by
    funext coordinate point
    exact duplicatedZeroUniformThresholdBasis_apply_eq gridSize gridSizePositive coordinate point
  rw [hbasis]
  exact hrounded

/-- Uniform signed thresholds form a finite approximate basis simultaneously
for every derivative-shaped function in a class with source-scale range two
and Lipschitz constant two. -/
theorem isFiniteApproximateBasis_uniformThreshold_of_twoLipschitz
    (gridSize : ℕ) (gridSizePositive : 0 < gridSize)
    (target : Set (UnitIntervalPoint → ℝ))
    (hbounded : ∀ function ∈ target, ∀ point, |function point| ≤ 2)
    (hLipschitz : ∀ function ∈ target, LipschitzWith 2 function) :
    IsFiniteApproximateBasis target
      (Set.range (duplicatedZeroUniformThresholdBasis gridSize gridSizePositive))
      (2 / (gridSize : ℝ)) (gridSize + 2) 3 := by
  intro function hfunction
  exact (twoLipschitz_isFiniteApproximateBasis_uniformThreshold gridSize gridSizePositive
    function (hbounded function hfunction) (hLipschitz function hfunction)) function (by simp)

/-- A uniformly bounded, report-wise one-Lipschitz binary-loss class has a
uniform signed-threshold basis for its discrete derivatives.  The derivative
has range `[-2,2]`, rather than `[-1,1]`, so the duplicated constant threshold
is needed to respect the individual coefficient bound. -/
theorem unitIntervalDiscreteDerivativeClass_isFiniteApproximateBasis_uniformThreshold
    (gridSize : ℕ) (gridSizePositive : 0 < gridSize) (losses : Set BinaryLoss)
    (hbounded : ∀ loss ∈ losses, IsUnitBoundedBinaryLoss loss)
    (hLipschitz : ∀ loss ∈ losses, IsUnitIntervalLipschitzBinaryLoss loss) :
    IsFiniteApproximateBasis (unitIntervalDiscreteDerivativeClass losses)
      (Set.range (duplicatedZeroUniformThresholdBasis gridSize gridSizePositive))
      (2 / (gridSize : ℝ)) (gridSize + 2) 3 := by
  apply isFiniteApproximateBasis_uniformThreshold_of_twoLipschitz gridSize gridSizePositive
  · intro derivative hderivative point
    rcases hderivative with ⟨loss, hloss, rfl⟩
    exact discreteDerivative_abs_le_two_of_unitBounded (hbounded loss hloss) point.2
  · intro derivative hderivative
    rcases hderivative with ⟨loss, hloss, rfl⟩
    exact discreteDerivative_restrict_lipschitz_two (hLipschitz loss hloss)

end AppliedModelingLib.Learning.Prediction
