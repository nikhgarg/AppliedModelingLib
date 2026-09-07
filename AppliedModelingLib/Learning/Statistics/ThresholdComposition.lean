import AppliedModelingLib.Learning.Statistics.VC

/-!
# Finite affine-threshold compositions of binary classes

The objects here are the class `C_T(H)` used in the VC analysis of a
`T`-round binary AdaBoost vote: choose `T` functions from `H`, form a real
weighted sum of their Boolean outputs, and apply one affine threshold.  The
definition is independent of AdaBoost's training run so it can also support
general computation-network VC arguments.
-/

namespace AppliedModelingLib
namespace Statistics

open scoped BigOperators

/-- The affine score of a point in `ℝ^dimension`. -/
noncomputable def affineThresholdScore
    {dimension : ℕ} (weights : Fin dimension → ℝ) (offset : ℝ)
    (point : Fin dimension → ℝ) : ℝ :=
  (∑ coordinate, weights coordinate * point coordinate) - offset

/-- A closed affine half-space, represented as a binary classifier. -/
noncomputable def affineThresholdClassifier
    {dimension : ℕ} (weights : Fin dimension → ℝ) (offset : ℝ) :
    BinaryClassifier (Fin dimension → ℝ) :=
  fun point => decide (0 ≤ affineThresholdScore weights offset point)

/-- The class of all closed affine thresholds in `ℝ^dimension`. -/
noncomputable def affineThresholdClass (dimension : ℕ) :
    Set (BinaryClassifier (Fin dimension → ℝ)) :=
  {classifier | ∃ weights : Fin dimension → ℝ, ∃ offset : ℝ,
    classifier = affineThresholdClassifier weights offset}

/-- The zero-one vector of a finite family of binary classifier outputs. -/
noncomputable def binaryFeatureVector
    {X : Type*} (width : ℕ) (hypotheses : Fin width → BinaryClassifier X)
    (feature : X) : Fin width → ℝ :=
  fun index => if hypotheses index feature = true then 1 else 0

/-- The real-valued score of a finite affine combination of binary classifiers. -/
noncomputable def binaryThresholdScore
    {X : Type*} (width : ℕ) (weights : Fin width → ℝ) (offset : ℝ)
    (hypotheses : Fin width → BinaryClassifier X) (feature : X) : ℝ :=
  affineThresholdScore weights offset (binaryFeatureVector width hypotheses feature)

/--
The Boolean affine threshold of a finite family of binary classifiers.  Equality
at the threshold is classified as positive, matching the closed half-space
convention used by the final AdaBoost vote.
-/
noncomputable def binaryThresholdCombination
    {X : Type*} (width : ℕ) (weights : Fin width → ℝ) (offset : ℝ)
    (hypotheses : Fin width → BinaryClassifier X) : BinaryClassifier X :=
  fun feature => decide (0 ≤ binaryThresholdScore width weights offset hypotheses feature)

/--
The `width`-term affine-threshold closure of a binary concept class.  This is
the paper's `C_T(H)`: repetitions among the selected weak hypotheses are
permitted, as they are in a boosting run.
-/
noncomputable def binaryThresholdCombinationClass
    {X : Type*} (concepts : Set (BinaryClassifier X)) (width : ℕ) :
    Set (BinaryClassifier X) :=
  {combined | ∃ hypotheses : Fin width → BinaryClassifier X,
      (∀ index, hypotheses index ∈ concepts) ∧
      ∃ weights : Fin width → ℝ, ∃ offset : ℝ,
        combined = binaryThresholdCombination width weights offset hypotheses}

/-- Constructor membership for the affine-threshold closure. -/
theorem binaryThresholdCombination_mem_class
    {X : Type*} {concepts : Set (BinaryClassifier X)} {width : ℕ}
    (hypotheses : Fin width → BinaryClassifier X)
    (hhypotheses : ∀ index, hypotheses index ∈ concepts)
    (weights : Fin width → ℝ) (offset : ℝ) :
    binaryThresholdCombination width weights offset hypotheses ∈
      binaryThresholdCombinationClass concepts width :=
  ⟨hypotheses, hhypotheses, weights, offset, rfl⟩

/-- A larger weak class gives a larger affine-threshold closure. -/
theorem binaryThresholdCombinationClass_mono
    {X : Type*} {first second : Set (BinaryClassifier X)} {width : ℕ}
    (hsubset : first ⊆ second) :
    binaryThresholdCombinationClass first width ⊆
      binaryThresholdCombinationClass second width := by
  rintro combined ⟨hypotheses, hhypotheses, weights, offset, hcombined⟩
  exact ⟨hypotheses, fun index => hsubset (hhypotheses index), weights, offset, hcombined⟩

/-- A zero affine score is classified as positive by the threshold convention. -/
theorem binaryThresholdCombination_apply_eq_true_iff
    {X : Type*} (width : ℕ) (weights : Fin width → ℝ) (offset : ℝ)
    (hypotheses : Fin width → BinaryClassifier X) (feature : X) :
    binaryThresholdCombination width weights offset hypotheses feature = true ↔
      0 ≤ binaryThresholdScore width weights offset hypotheses feature := by
  simp [binaryThresholdCombination]

/-- The threshold-combination score is the affine score of its Boolean feature vector. -/
theorem binaryThresholdScore_eq_affineThresholdScore
    {X : Type*} (width : ℕ) (weights : Fin width → ℝ) (offset : ℝ)
    (hypotheses : Fin width → BinaryClassifier X) (feature : X) :
    binaryThresholdScore width weights offset hypotheses feature =
      affineThresholdScore weights offset (binaryFeatureVector width hypotheses feature) := rfl

/-- A finite threshold combination is an affine threshold after its weak classifiers
are evaluated into their zero-one feature vector. -/
theorem binaryThresholdCombination_eq_affineThresholdClassifier
    {X : Type*} (width : ℕ) (weights : Fin width → ℝ) (offset : ℝ)
    (hypotheses : Fin width → BinaryClassifier X) (feature : X) :
    binaryThresholdCombination width weights offset hypotheses feature =
      affineThresholdClassifier weights offset
        (binaryFeatureVector width hypotheses feature) := rfl

end Statistics
end AppliedModelingLib
