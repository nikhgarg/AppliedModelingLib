import AppliedModelingLib.Learning.Statistics.ThresholdComposition
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Affine-threshold VC foundations

This module develops the geometric part of the computation-network route used
by Freund--Schapire Theorem 8.  The first lemma is the affine-dependence
certificate behind the upper bound on the VC dimension of thresholds in a
finite-dimensional real vector space.
-/

namespace AppliedModelingLib
namespace Statistics

open scoped BigOperators

/--
An arbitrary finite index family of more than `dimension + 1` points in
`ℝ^dimension` has a nontrivial affine dependence.
-/
theorem exists_affineDependence_of_fintype_card_gt
    {Index : Type*} [Fintype Index] {dimension : ℕ}
    (points : Index → Fin dimension → ℝ)
    (hcard : dimension + 1 < Fintype.card Index) :
    ∃ support : Finset Index, ∃ coefficients : Index → ℝ,
      (∑ index ∈ support, coefficients index) = 0 ∧
      (∑ index ∈ support, coefficients index • points index) = 0 ∧
      ∃ index ∈ support, coefficients index ≠ 0 := by
  have hnot : ¬ LinearIndependent ℝ (fun index => (points index, (1 : ℝ))) := by
    intro hindependent
    have hdimension := hindependent.fintype_card_le_finrank
    rw [Module.finrank_prod, Module.finrank_fin_fun] at hdimension
    norm_num at hdimension
    omega
  rcases not_linearIndependent_iff.mp hnot with
    ⟨support, coefficients, hsum, hnonzero⟩
  refine ⟨support, coefficients, ?_, ?_, hnonzero⟩
  · have hsecond := congrArg Prod.snd hsum
    rw [Prod.snd_sum] at hsecond
    simpa using hsecond
  · have hfirst := congrArg Prod.fst hsum
    rw [Prod.fst_sum] at hfirst
    simpa using hfirst

/--
More than `dimension + 1` points in `ℝ^dimension` have a nontrivial affine
dependence.  The coefficients sum to zero and their weighted vector sum is
zero; both identities are retained explicitly for the threshold-separation
argument that follows.
-/
theorem exists_affineDependence_of_card_gt
    {dimension sampleSize : ℕ} (points : Fin sampleSize → Fin dimension → ℝ)
    (hcard : dimension + 1 < sampleSize) :
    ∃ support : Finset (Fin sampleSize), ∃ coefficients : Fin sampleSize → ℝ,
      (∑ index ∈ support, coefficients index) = 0 ∧
      (∑ index ∈ support, coefficients index • points index) = 0 ∧
      ∃ index ∈ support, coefficients index ≠ 0 := by
  exact exists_affineDependence_of_fintype_card_gt points (by
    simpa using hcard)

/--
Every affine score annihilates an affine dependence.  This is the algebraic
identity that turns the dependence above into an impossible threshold labeling.
-/
theorem affineDependence_sum_mul_affineThresholdScore_eq_zero
    {Index : Type*} {dimension : ℕ} (points : Index → Fin dimension → ℝ)
    (support : Finset Index) (coefficients : Index → ℝ)
    (weights : Fin dimension → ℝ) (offset : ℝ)
    (hsum : (∑ index ∈ support, coefficients index) = 0)
    (hpoints : (∑ index ∈ support, coefficients index • points index) = 0) :
    (∑ index ∈ support, coefficients index *
      affineThresholdScore weights offset (points index)) = 0 := by
  have hcoordinate : ∀ coordinate, (∑ index ∈ support,
      coefficients index * points index coordinate) = 0 := by
    intro coordinate
    have h := congrFun hpoints coordinate
    rw [Finset.sum_apply] at h
    simpa [smul_eq_mul] using h
  have hoffset : (∑ index ∈ support, coefficients index * offset) = 0 := by
    rw [← Finset.sum_mul, hsum, zero_mul]
  simp_rw [affineThresholdScore, mul_sub]
  rw [Finset.sum_sub_distrib]
  rw [show (∑ index ∈ support, coefficients index *
      ∑ coordinate, weights coordinate * points index coordinate) =
      ∑ coordinate, weights coordinate *
        (∑ index ∈ support, coefficients index * points index coordinate) by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro coordinate _
      apply Finset.sum_congr rfl
      intro index _
      ring]
  simp_rw [hcoordinate]
  simp [hoffset]

/--
An affine dependence cannot be separated according to the signs of its
coefficients.  Positive coefficients are allowed on the closed positive side;
a nonzero zero-sum dependence necessarily has a negative coefficient, whose
strictly negative score makes the weighted score sum positive, contradicting
the affine-dependence identity.
-/
theorem affineDependence_sign_constraints_false
    {Index : Type*} (support : Finset Index) (coefficients scores : Index → ℝ)
    (hscoreSum : (∑ index ∈ support, coefficients index * scores index) = 0)
    (hcoefficientSum : (∑ index ∈ support, coefficients index) = 0)
    (hnonzero : ∃ index ∈ support, coefficients index ≠ 0)
    (hpositive : ∀ index ∈ support,
      0 < coefficients index → 0 ≤ scores index)
    (hnonpositive : ∀ index ∈ support,
      coefficients index ≤ 0 → scores index < 0) : False := by
  have htermNonneg : ∀ index ∈ support, 0 ≤ coefficients index * scores index := by
    intro index hindex
    by_cases hpos : 0 < coefficients index
    · exact mul_nonneg hpos.le (hpositive index hindex hpos)
    · exact mul_nonneg_of_nonpos_of_nonpos (le_of_not_gt hpos)
        (hnonpositive index hindex (le_of_not_gt hpos)).le
  have hnegative : ∃ index ∈ support, coefficients index < 0 := by
    by_contra hnot
    push Not at hnot
    have hzero : ∀ index ∈ support, coefficients index = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hnot).mp hcoefficientSum
    rcases hnonzero with ⟨index, hindex, hne⟩
    exact hne (hzero index hindex)
  rcases hnegative with ⟨index, hindex, hnegative⟩
  have htermPos : 0 < coefficients index * scores index :=
    mul_pos_of_neg_of_neg hnegative
      (hnonpositive index hindex hnegative.le)
  have hsumPos : 0 < ∑ index ∈ support, coefficients index * scores index :=
    Finset.sum_pos' htermNonneg ⟨index, hindex, htermPos⟩
  linarith

/--
No closed affine threshold realizes the positive-coefficient labeling of a
nontrivial affine dependence.  The negative coefficients are assigned the
strict negative side, so the closed convention on the positive side causes no
boundary exception.
-/
theorem affineThresholdClassifier_not_realize_affineDependence_signs
    {Index : Type*} {dimension : ℕ} (points : Index → Fin dimension → ℝ)
    (support : Finset Index) (coefficients : Index → ℝ)
    (hcoefficientSum : (∑ index ∈ support, coefficients index) = 0)
    (hpoints : (∑ index ∈ support, coefficients index • points index) = 0)
    (hnonzero : ∃ index ∈ support, coefficients index ≠ 0) :
    ¬ ∃ weights : Fin dimension → ℝ, ∃ offset : ℝ, ∀ index ∈ support,
      affineThresholdClassifier weights offset (points index) =
        decide (0 < coefficients index) := by
  rintro ⟨weights, offset, hrealizes⟩
  apply affineDependence_sign_constraints_false support coefficients
    (fun index => affineThresholdScore weights offset (points index))
  · exact affineDependence_sum_mul_affineThresholdScore_eq_zero points support
      coefficients weights offset hcoefficientSum hpoints
  · exact hcoefficientSum
  · exact hnonzero
  · intro index hindex hpositive
    have hclassifier : affineThresholdClassifier weights offset (points index) = true := by
      rw [hrealizes index hindex]
      simp [hpositive]
    simpa [affineThresholdClassifier] using hclassifier
  · intro index hindex hnonpositive
    have hclassifier : affineThresholdClassifier weights offset (points index) = false := by
      rw [hrealizes index hindex]
      simp [not_lt_of_ge hnonpositive]
    have hnot : ¬ 0 ≤ affineThresholdScore weights offset (points index) := by
      simpa [affineThresholdClassifier] using hclassifier
    exact lt_of_not_ge hnot

/--
The trace of affine thresholds cannot shatter every point of a finite sample
having more than `dimension + 1` distinct points.  This is the geometric
linear-threshold VC upper bound in its full-sample form; the next step lifts
it to arbitrary shattered subsamples.
-/
theorem binaryTrace_affineThresholdClass_not_shatters_univ_of_card_gt
    {dimension : ℕ} (sample : Finset (Fin dimension → ℝ))
    (hcard : dimension + 1 < sample.card) :
    ¬ (binaryTrace (affineThresholdClass dimension) sample).Shatters Finset.univ := by
  intro hshatters
  rcases exists_affineDependence_of_fintype_card_gt
    (fun index : sample => index.1) (by simpa using hcard) with
      ⟨support, coefficients, hcoefficientSum, hpoints, hnonzero⟩
  let positiveLabels : Finset sample :=
    support.filter (fun index => 0 < coefficients index)
  rcases hshatters (t := positiveLabels) (by
    intro index hindex
    simp) with ⟨labels, hlabels, hintersection⟩
  have hlabelsSub : labels ⊆ sample.attach := by
    intro index hindex
    simp
  have hintersectionEq : sample.attach ∩ labels = labels :=
    Finset.inter_eq_right.mpr hlabelsSub
  have hlabelsEq : labels = positiveLabels := by
    calc
      labels = sample.attach ∩ labels := hintersectionEq.symm
      _ = positiveLabels := hintersection
  let classifier := classifierOfBinaryTrace (affineThresholdClass dimension) sample labels
  have hclassifier : classifier ∈ affineThresholdClass dimension :=
    classifierOfBinaryTrace_mem hlabels
  rcases hclassifier with ⟨weights, offset, hclassifierEq⟩
  apply affineThresholdClassifier_not_realize_affineDependence_signs
    (fun index : sample => index.1) support coefficients hcoefficientSum hpoints hnonzero
  refine ⟨weights, offset, ?_⟩
  intro index hindex
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  have hrealizes := classifierOfBinaryTrace_realizes hlabels index
  calc
    affineThresholdClassifier weights offset index.1 = true ↔ classifier index.1 = true := by
      rw [hclassifierEq]
    _ ↔ index ∈ labels := hrealizes.symm
    _ ↔ index ∈ positiveLabels := by rw [hlabelsEq]
    _ ↔ 0 < coefficients index := by simp [positiveLabels, hindex]

/--
No affine-threshold trace can shatter an arbitrary subsample with more than
`dimension + 1` points.  Unlike the preceding full-sample lemma, this version
is directly suited to the `Finset.vcDim` definition, whose shatterers are
subsets of the ambient finite sample.
-/
noncomputable def affineThresholdTraceShatters
    {dimension : ℕ} (sample : Finset (Fin dimension → ℝ))
    (shattered : Finset sample) : Prop := by
  classical
  letI : DecidableEq (Fin dimension → ℝ) := Classical.decEq _
  exact (binaryTrace (affineThresholdClass dimension) sample).Shatters shattered

theorem binaryTrace_affineThresholdClass_not_shatters_of_card_gt
    {dimension : ℕ} (sample : Finset (Fin dimension → ℝ))
    (shattered : Finset sample)
    (hcard : dimension + 1 < shattered.card) :
    ¬ affineThresholdTraceShatters sample shattered := by
  classical
  letI : DecidableEq (Fin dimension → ℝ) := Classical.decEq _
  intro hshatters
  unfold affineThresholdTraceShatters at hshatters
  let inclusion : shattered ↪ sample :=
    { toFun := fun index => index.1
      inj' := fun first second heq =>
        Subtype.ext heq }
  rcases exists_affineDependence_of_fintype_card_gt
    (fun index : shattered => index.1.1) (by simpa using hcard) with
      ⟨support, coefficients, hcoefficientSum, hpoints, hnonzero⟩
  let positiveLabels : Finset sample :=
    (support.filter (fun index => 0 < coefficients index)).map inclusion
  have hpositiveLabelsSub : positiveLabels ⊆ shattered := by
    intro point hpoint
    simp only [positiveLabels, Finset.mem_map] at hpoint
    rcases hpoint with ⟨index, _, rfl⟩
    simpa [inclusion] using index.2
  rcases hshatters hpositiveLabelsSub with ⟨labels, hlabels, hintersection⟩
  let classifier := classifierOfBinaryTrace (affineThresholdClass dimension) sample labels
  have hclassifier : classifier ∈ affineThresholdClass dimension :=
    classifierOfBinaryTrace_mem hlabels
  rcases hclassifier with ⟨weights, offset, hclassifierEq⟩
  apply affineThresholdClassifier_not_realize_affineDependence_signs
    (fun index : shattered => index.1.1) support coefficients hcoefficientSum hpoints hnonzero
  refine ⟨weights, offset, ?_⟩
  intro index hindex
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  have hinclusion : inclusion index ∈ shattered := by
    simpa [inclusion] using index.2
  have hmemLabels : inclusion index ∈ labels ↔ inclusion index ∈ positiveLabels := by
    rw [← hintersection]
    simp [hinclusion]
  have hmemPositive : inclusion index ∈ positiveLabels ↔ 0 < coefficients index := by
    simp [positiveLabels, inclusion, hindex]
  calc
    affineThresholdClassifier weights offset index.1.1 = true ↔ classifier index.1.1 = true := by
      rw [hclassifierEq]
    _ ↔ inclusion index ∈ labels := by
      simpa [inclusion] using (classifierOfBinaryTrace_realizes hlabels index.1).symm
    _ ↔ inclusion index ∈ positiveLabels := hmemLabels
    _ ↔ 0 < coefficients index := hmemPositive

set_option maxHeartbeats 400000 in
-- Unfolding the finite shatterer supremum exposes the full affine-threshold trace.
/--
The class of closed affine thresholds on `ℝ^dimension` has VC dimension at
most `dimension + 1`.  This is the linear-threshold node bound used in the
Baum--Haussler computation-network theorem cited by Freund--Schapire Theorem
8.
-/
theorem vcDimensionAtMost_affineThresholdClass (dimension : ℕ) :
    VCDimensionAtMost (affineThresholdClass dimension) (dimension + 1) := by
  classical
  letI : DecidableEq (Fin dimension → ℝ) := Classical.decEq _
  intro sample
  unfold binaryTraceVCDimension Finset.vcDim
  rw [Finset.sup_le_iff]
  intro shattered hshattered
  by_contra hnot
  exact binaryTrace_affineThresholdClass_not_shatters_of_card_gt sample shattered
    (Nat.lt_of_not_ge hnot) (by
      unfold affineThresholdTraceShatters
      exact Finset.mem_shatterer.mp hshattered)

end Statistics
end AppliedModelingLib
