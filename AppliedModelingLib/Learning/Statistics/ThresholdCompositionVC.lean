import AppliedModelingLib.Learning.Statistics.AffineThresholdVC
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# VC growth for finite affine-threshold compositions

This file gives the finite-trace, two-layer specialization of the
Baum--Haussler computation-network argument.  A trace of a weighted threshold
combination is determined by the `width` weak-hypothesis traces and by one
affine-threshold trace on their resulting zero-one feature vectors.  The
resulting product bound is stated without any network theorem as an axiom.
-/

namespace AppliedModelingLib
namespace Statistics

open scoped BigOperators

/-- The q-ary entropy at its uniform maximizer is `log q`. -/
theorem qaryEntropy_at_uniform_max (q : ℕ) (hq : 2 ≤ q) :
    Real.qaryEntropy q (1 - 1 / (q : ℝ)) = Real.log (q : ℝ) := by
  have hqPos : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hqGtOne : 1 < (q : ℝ) := by exact_mod_cast (show 1 < q by omega)
  have hqSubPos : 0 < (q : ℝ) - 1 := by linarith
  have hp : 1 - 1 / (q : ℝ) = ((q : ℝ) - 1) / (q : ℝ) := by
    field_simp
  have hqSub : ((q - 1 : ℤ) : ℝ) = (q : ℝ) - 1 := by
    push_cast
    ring
  rw [hp]
  simp only [Real.qaryEntropy, Real.binEntropy, hqSub]
  rw [show 1 - ((q : ℝ) - 1) / (q : ℝ) = 1 / (q : ℝ) by
    field_simp <;> ring]
  rw [inv_div]
  rw [Real.log_div hqPos.ne' hqSubPos.ne']
  field_simp <;> ring

/-- The entropy of a `q`-ary probability never exceeds that of the uniform law. -/
theorem qaryEntropy_le_log (q : ℕ) (hq : 2 ≤ q) (p : ℝ)
    (hpNonneg : 0 ≤ p) (hpLeOne : p ≤ 1) :
    Real.qaryEntropy q p ≤ Real.log (q : ℝ) := by
  have hqPos : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hqOne : 1 ≤ (q : ℝ) := by exact_mod_cast (show 1 ≤ q by omega)
  let maximizer : ℝ := 1 - 1 / (q : ℝ)
  have hmaxNonneg : 0 ≤ maximizer := by
    dsimp [maximizer]
    exact sub_nonneg.mpr (by simpa [one_div] using inv_le_one_of_one_le₀ hqOne)
  have hmaxLeOne : maximizer ≤ 1 := by
    dsimp [maximizer]
    linarith [one_div_pos.mpr hqPos]
  by_cases hleft : p ≤ maximizer
  · calc
      Real.qaryEntropy q p ≤ Real.qaryEntropy q maximizer :=
        (Real.qaryEntropy_strictMonoOn hq).monotoneOn
          ⟨hpNonneg, hleft⟩ ⟨hmaxNonneg, le_rfl⟩ hleft
      _ = Real.log (q : ℝ) := qaryEntropy_at_uniform_max q hq
  · have hmaxLt : maximizer < p := lt_of_not_ge hleft
    calc
      Real.qaryEntropy q p ≤ Real.qaryEntropy q maximizer :=
        (Real.qaryEntropy_strictAntiOn hq).antitoneOn
          ⟨le_rfl, hmaxLeOne⟩ ⟨hmaxLt.le, hpLeOne⟩ hmaxLt.le
      _ = Real.log (q : ℝ) := qaryEntropy_at_uniform_max q hq

/-- A small explicit lower bound for `log 2`, derived from Mathlib's certified decimal bound. -/
theorem half_lt_log_two : (1 / 2 : ℝ) < Real.log 2 := by
  exact lt_trans (by norm_num) Real.log_two_gt_d9

/-- Above four, the logarithm is bounded by the line `(log 2) * x / 2`. -/
theorem log_lt_half_mul_log_two_of_four_lt {x : ℝ}
    (hx : 4 < x) : Real.log x < (x / 2) * Real.log 2 := by
  have hxPos : 0 < x := by linarith
  have hyPos : 0 < x / 4 := by positivity
  have hyNeOne : x / 4 ≠ 1 := by
    intro h
    have : x = 4 := by linarith
    linarith
  have hlogQuotient : Real.log (x / 4) < x / 4 - 1 :=
    Real.log_lt_sub_one_of_pos hyPos hyNeOne
  have hlogDecomposition : Real.log x = Real.log 4 + Real.log (x / 4) := by
    rw [← Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hyPos.ne']
    field_simp
  have hlogFour : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hfactorNonneg : 0 ≤ x / 2 - 2 := by linarith
  have hfactor : x / 4 - 1 ≤ (x / 2 - 2) * Real.log 2 := by
    have h := mul_le_mul_of_nonneg_left half_lt_log_two.le hfactorNonneg
    nlinarith
  calc
    Real.log x = Real.log 4 + Real.log (x / 4) := hlogDecomposition
    _ < Real.log 4 + (x / 4 - 1) := by linarith
    _ ≤ (x / 2) * Real.log 2 := by rw [hlogFour]; nlinarith

/-- For at least two computation nodes, `log₂(e * nodes)` is strictly above two. -/
theorem two_lt_logb_exp_one_mul_nat (nodes : ℕ) (hnodes : 2 ≤ nodes) :
    2 < Real.logb 2 (Real.exp 1 * (nodes : ℝ)) := by
  have hnodesPos : 0 < (nodes : ℝ) := by
    exact_mod_cast (show 0 < nodes by omega)
  have hlogTwoPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hENgtFour : 4 < Real.exp 1 * (nodes : ℝ) := by
    calc
      (4 : ℝ) ≤ 2 * (nodes : ℝ) := by
        have : (2 : ℝ) ≤ nodes := by exact_mod_cast hnodes
        nlinarith
      _ < Real.exp 1 * (nodes : ℝ) :=
        mul_lt_mul_of_pos_right Real.exp_one_gt_two hnodesPos
  have hlogENgt : Real.log 4 < Real.log (Real.exp 1 * (nodes : ℝ)) :=
    Real.strictMonoOn_log (Set.mem_Ioi.mpr (by norm_num))
      (Set.mem_Ioi.mpr (mul_pos (Real.exp_pos _) hnodesPos)) hENgtFour
  have hlogFour : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [Real.logb]
  apply (lt_div_iff₀ hlogTwoPos).mpr
  rw [← hlogFour]
  exact hlogENgt

/-- The real-valued VC bound displayed in Freund--Schapire Theorem 8. -/
noncomputable def sourceThresholdCombinationVCBound (width d : ℕ) : ℝ :=
  2 * ((d + 1 : ℕ) : ℝ) * ((width + 1 : ℕ) : ℝ) *
    Real.logb 2 (Real.exp 1 * ((width + 1 : ℕ) : ℝ))

/-- Every zero-term threshold combination is constant. -/
theorem binaryThresholdCombinationClass_zero_constant
    {X : Type*} (concepts : Set (BinaryClassifier X))
    {classifier : BinaryClassifier X}
    (hclassifier : classifier ∈ binaryThresholdCombinationClass concepts 0) :
    ∀ first second, classifier first = classifier second := by
  rcases hclassifier with ⟨hypotheses, _hhypotheses, weights, offset, rfl⟩
  intro first second
  simp [binaryThresholdCombination, binaryThresholdScore, affineThresholdScore,
    binaryFeatureVector]

/-- A class of zero-term thresholds has VC dimension at most one on every finite trace. -/
theorem binaryTraceVCDimension_thresholdCombinationClass_zero_le_one
    {X : Type*} (concepts : Set (BinaryClassifier X)) (sample : Finset X) :
    binaryTraceVCDimension (binaryThresholdCombinationClass concepts 0) sample ≤ 1 := by
  classical
  unfold binaryTraceVCDimension Finset.vcDim
  apply Finset.sup_le
  intro shattered hshattered
  have hshatters := Finset.mem_shatterer.mp hshattered
  by_contra hnot
  have hcard : 1 < shattered.card := by omega
  obtain ⟨first, hfirst, second, hsecond, hne⟩ := Finset.one_lt_card.mp hcard
  obtain ⟨labels, hlabels, hintersection⟩ :=
    hshatters.exists_inter_eq_singleton hfirst
  have hfirst_labels : first ∈ labels := by
    have : first ∈ shattered ∩ labels := by
      rw [hintersection]
      simp
    exact (Finset.mem_inter.mp this).2
  have hsecond_not_labels : second ∉ labels := by
    intro hsecond_labels
    have : second ∈ shattered ∩ labels :=
      Finset.mem_inter.mpr ⟨hsecond, hsecond_labels⟩
    rw [hintersection] at this
    have hsecond_eq : second = first := by simpa using this
    exact hne hsecond_eq.symm
  simp only [binaryTrace, Finset.mem_filter, Finset.mem_univ, true_and] at hlabels
  rcases hlabels with ⟨classifier, hclassifier, hrealizes⟩
  have hfirst_true : classifier first.1 = true :=
    (hrealizes first).mp hfirst_labels
  have hsecond_not_true : classifier second.1 ≠ true := by
    intro hsecond_true
    exact hsecond_not_labels ((hrealizes second).mpr hsecond_true)
  have hconstant := binaryThresholdCombinationClass_zero_constant concepts hclassifier
    first.1 second.1
  exact hsecond_not_true (hconstant ▸ hfirst_true)

/-- The paper's real-valued Theorem-8 bound dominates the zero-term VC dimension. -/
theorem sourceThresholdCombinationVCBound_zero_ge_one
    (d : ℕ) (hd : 2 ≤ d) :
    (1 : ℝ) ≤ sourceThresholdCombinationVCBound 0 d := by
  have hlog_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog_lt_one : Real.log 2 < 1 :=
    lt_trans Real.log_two_lt_d9 (by norm_num)
  have hinv_gt_one : 1 < 1 / Real.log 2 := by
    exact (lt_div_iff₀ hlog_pos).mpr (by simpa)
  have hd_real : (3 : ℝ) ≤ (d + 1 : ℕ) := by
    exact_mod_cast (show 3 ≤ d + 1 by omega)
  simp only [sourceThresholdCombinationVCBound, Nat.cast_add, Nat.cast_one,
    zero_add, Real.logb, mul_one, Real.log_exp]
  nlinarith

/--
The numerical step in the Baum--Haussler VC calculation.  Once the restricted
sample size is at least `2 * D * log₂(e*N)`, the source growth envelope is
strictly smaller than the `2^m` labelings required to shatter that sample.
-/
theorem baumHaussler_envelope_lt_two_pow
    (nodes total sampleSize : ℕ) (hnodes : 2 ≤ nodes) (htotal : 0 < total)
    (hsize : 2 * (total : ℝ) *
        Real.logb 2 (Real.exp 1 * (nodes : ℝ)) ≤ (sampleSize : ℝ)) :
    ((nodes : ℝ) * Real.exp 1 * (sampleSize : ℝ) / (total : ℝ)) ^ total <
      (2 : ℝ) ^ sampleSize := by
  let entropyScale : ℝ := Real.logb 2 (Real.exp 1 * (nodes : ℝ))
  let ratio : ℝ := (sampleSize : ℝ) / (total : ℝ)
  have hnodesPos : 0 < (nodes : ℝ) := by
    exact_mod_cast (show 0 < nodes by omega)
  have htotalPos : 0 < (total : ℝ) := by exact_mod_cast htotal
  have hlogTwoPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hENPos : 0 < Real.exp 1 * (nodes : ℝ) :=
    mul_pos (Real.exp_pos _) hnodesPos
  have hENgtFour : 4 < Real.exp 1 * (nodes : ℝ) := by
    calc
      (4 : ℝ) ≤ 2 * (nodes : ℝ) := by
        have : (2 : ℝ) ≤ nodes := by exact_mod_cast hnodes
        nlinarith
      _ < Real.exp 1 * (nodes : ℝ) :=
        mul_lt_mul_of_pos_right Real.exp_one_gt_two hnodesPos
  have hlogENgt : Real.log 4 < Real.log (Real.exp 1 * (nodes : ℝ)) :=
    Real.strictMonoOn_log (Set.mem_Ioi.mpr (by norm_num))
      (Set.mem_Ioi.mpr hENPos) hENgtFour
  have hlogFour : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hscaleGtTwo : 2 < entropyScale := by
    dsimp [entropyScale]
    rw [Real.logb]
    apply (lt_div_iff₀ hlogTwoPos).mpr
    rw [← hlogFour]
    exact hlogENgt
  have hratioLower : 2 * entropyScale ≤ ratio := by
    dsimp [ratio]
    apply (le_div_iff₀ htotalPos).mpr
    simpa [entropyScale, mul_assoc, mul_left_comm, mul_comm] using hsize
  have hratioGtFour : 4 < ratio := by linarith
  have hratioPos : 0 < ratio := by linarith
  have hlogRatio : Real.log ratio < (ratio / 2) * Real.log 2 :=
    log_lt_half_mul_log_two_of_four_lt hratioGtFour
  have hlogEN : Real.log (Real.exp 1 * (nodes : ℝ)) =
      entropyScale * Real.log 2 := by
    dsimp [entropyScale]
    rw [Real.logb]
    field_simp
  have hscaleLeHalfRatio : entropyScale ≤ ratio / 2 := by linarith
  have hsumBound : entropyScale * Real.log 2 +
      (ratio / 2) * Real.log 2 ≤ ratio * Real.log 2 := by
    have h := mul_le_mul_of_nonneg_right hscaleLeHalfRatio hlogTwoPos.le
    nlinarith
  have hratioRewrite :
      (nodes : ℝ) * Real.exp 1 * (sampleSize : ℝ) / (total : ℝ) =
        (nodes : ℝ) * Real.exp 1 * ratio := by
    dsimp [ratio]
    ring
  rw [hratioRewrite]
  have hbasePos : 0 < (nodes : ℝ) * Real.exp 1 * ratio :=
    mul_pos (mul_pos hnodesPos (Real.exp_pos _)) hratioPos
  apply (Real.log_lt_log_iff (pow_pos hbasePos _)
    (pow_pos (by norm_num) _)).mp
  rw [Real.log_pow, Real.log_pow]
  have hlogBase : Real.log ((nodes : ℝ) * Real.exp 1 * ratio) =
      entropyScale * Real.log 2 + Real.log ratio := by
    rw [show (nodes : ℝ) * Real.exp 1 * ratio =
      (Real.exp 1 * (nodes : ℝ)) * ratio by ring,
      Real.log_mul hENPos.ne' hratioPos.ne', hlogEN]
  calc
    (total : ℝ) * Real.log ((nodes : ℝ) * Real.exp 1 * ratio) =
        (total : ℝ) * (entropyScale * Real.log 2 + Real.log ratio) := by
      rw [hlogBase]
    _ < (total : ℝ) *
        (entropyScale * Real.log 2 + (ratio / 2) * Real.log 2) := by
      gcongr
    _ ≤ (total : ℝ) * (ratio * Real.log 2) := by
      gcongr
    _ = (sampleSize : ℝ) * Real.log 2 := by
      dsimp [ratio]
      field_simp

/-- The raw feature subsample underlying a finite subsample of `sample`. -/
def rawSubsample
    {X : Type*} [DecidableEq X] (sample : Finset X) (subsample : Finset sample) : Finset X :=
  subsample.image Subtype.val

/-- The canonical embedding of a subsample's point type into its raw support. -/
def rawSubsampleEmbedding
    {X : Type*} [DecidableEq X] (sample : Finset X) (subsample : Finset sample) :
    subsample ↪ rawSubsample sample subsample := by
  refine
    { toFun := fun point => ⟨point.1.1, ?_⟩
      inj' := fun first second heq => ?_ }
  · unfold rawSubsample
    exact Finset.mem_image.mpr ⟨point.1, point.2, rfl⟩
  · apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun point : rawSubsample sample subsample => point.1) heq

/-- Passing from a subtype-indexed subsample to raw features preserves its cardinality. -/
theorem card_rawSubsample
    {X : Type*} [DecidableEq X] (sample : Finset X) (subsample : Finset sample) :
    (rawSubsample sample subsample).card = subsample.card := by
  unfold rawSubsample
  exact Finset.card_image_of_injective _ Subtype.val_injective

/--
If a trace family shatters a subsample of an ambient finite sample, then the
same concept class shatters the full raw-feature subsample.  This removes the
ambient subtype bookkeeping before applying a trace-growth contradiction.
-/
theorem binaryTrace_shatters_univ_rawSubsample_of_shatters
    {X : Type*} [instX : DecidableEq X] (concepts : Set (BinaryClassifier X))
    (sample : Finset X) (subsample : Finset sample)
    (hshatters : (binaryTrace concepts sample).Shatters subsample) :
    (binaryTrace concepts (rawSubsample sample subsample)).Shatters Finset.univ := by
  letI : DecidableEq X := instX
  rw [Finset.shatters_univ]
  apply Finset.eq_univ_of_forall
  intro target
  let rawEmbedding := rawSubsampleEmbedding sample subsample
  let inclusion : subsample ↪ sample :=
    { toFun := fun point => point.1
      inj' := fun first second heq => Subtype.ext heq }
  let targetOnSubsample : Finset subsample :=
    Finset.univ.filter fun point => rawEmbedding point ∈ target
  let targetOnSample : Finset sample := targetOnSubsample.map inclusion
  have htargetSub : targetOnSample ⊆ subsample := by
    intro point hpoint
    simp only [targetOnSample, Finset.mem_map] at hpoint
    rcases hpoint with ⟨subpoint, _, rfl⟩
    simpa [inclusion] using subpoint.2
  rcases hshatters htargetSub with ⟨labels, hlabels, hintersection⟩
  let classifier := classifierOfBinaryTrace concepts sample labels
  have hclassifier : classifier ∈ concepts := classifierOfBinaryTrace_mem hlabels
  let outputTrace := binaryClassifierTrace classifier (rawSubsample sample subsample)
  have houtputTrace : outputTrace ∈
      binaryTrace concepts (rawSubsample sample subsample) :=
    binaryClassifierTrace_mem_binaryTrace hclassifier _
  rw [← show outputTrace = target by
    apply Finset.ext
    intro rawPoint
    rcases Finset.mem_image.mp rawPoint.2 with ⟨samplePoint, hsamplePoint, hrawPoint⟩
    let subpoint : subsample := ⟨samplePoint, hsamplePoint⟩
    have hrawEmbeddingEq : rawEmbedding subpoint = rawPoint := by
      apply Subtype.ext
      exact hrawPoint
    rw [← hrawEmbeddingEq]
    have hrealizes := classifierOfBinaryTrace_realizes hlabels subpoint.1
    have hlabelsTarget : subpoint.1 ∈ labels ↔ subpoint ∈ targetOnSubsample := by
      calc
        subpoint.1 ∈ labels ↔ subpoint.1 ∈ subsample ∩ labels := by simp [subpoint.2]
        _ ↔ subpoint.1 ∈ targetOnSample := by rw [hintersection]
        _ ↔ subpoint ∈ targetOnSubsample := by simp [targetOnSample, inclusion]
    calc
      rawEmbedding subpoint ∈ outputTrace ↔ classifier subpoint.1.1 = true := by
        simp [outputTrace, binaryClassifierTrace, rawEmbedding]
        rfl
      _ ↔ subpoint.1 ∈ labels := hrealizes.symm
      _ ↔ subpoint ∈ targetOnSubsample := hlabelsTarget
      _ ↔ rawEmbedding subpoint ∈ target := by simp [targetOnSubsample]
    ]
  exact houtputTrace

/--
The q-ary entropy of the `width` equal first-layer nodes and one output node,
after multiplying by their total VC dimension.  This is the algebraic form of
the entropy step in the Baum--Haussler product-growth proof.
-/
theorem qaryEntropy_twoLayer_ratio
    (width d : ℕ) (hwidth : 0 < width) (hd : 0 < d) :
    (((width * d + (width + 1) : ℕ) : ℝ) *
        Real.qaryEntropy (width + 1)
          ((width * d : ℕ) / (width * d + (width + 1) : ℕ) : ℝ)) =
      ((width * d + (width + 1) : ℕ) : ℝ) *
          Real.log ((width * d + (width + 1) : ℕ) : ℝ) -
        (width * d : ℕ) * Real.log (d : ℝ) -
          (width + 1 : ℕ) * Real.log ((width + 1 : ℕ) : ℝ) := by
  let firstMass : ℝ := (width * d : ℕ)
  let outputMass : ℝ := (width + 1 : ℕ)
  let totalMass : ℝ := (width * d + (width + 1) : ℕ)
  have hfirstMassPos : 0 < firstMass := by
    dsimp [firstMass]
    exact_mod_cast Nat.mul_pos hwidth hd
  have houtputMassPos : 0 < outputMass := by
    dsimp [outputMass]
    exact_mod_cast Nat.succ_pos width
  have htotalMass : totalMass = firstMass + outputMass := by
    dsimp [totalMass, firstMass, outputMass]
    norm_num
  have htotalMassPos : 0 < totalMass := by rw [htotalMass]; positivity
  have honeSub : 1 - firstMass / totalMass = outputMass / totalMass := by
    rw [htotalMass]
    field_simp <;> ring
  have hfirstMass : firstMass = (width : ℝ) * (d : ℝ) := by
    dsimp [firstMass]
    norm_num
  have hnodeLog :
      Real.log (((↑(width + 1) : ℤ) - 1 : ℤ) : ℝ) = Real.log (width : ℝ) := by
    norm_num
  change totalMass * Real.qaryEntropy (width + 1) (firstMass / totalMass) = _
  rw [Real.qaryEntropy, Real.binEntropy, hnodeLog, honeSub]
  rw [inv_div, inv_div]
  rw [Real.log_div htotalMassPos.ne' hfirstMassPos.ne',
    Real.log_div htotalMassPos.ne' houtputMassPos.ne']
  rw [hfirstMass, Real.log_mul (by exact_mod_cast hwidth.ne')
    (by exact_mod_cast hd.ne')]
  field_simp [htotalMassPos.ne']
  rw [htotalMass, hfirstMass]
  push_cast
  dsimp [outputMass]
  push_cast
  ring

/--
Entropy compresses the separate first-layer and output VC denominators into
the Baum--Haussler `width + 1` node factor.
-/
theorem baumHaussler_twoLayer_log_denominator_le
    (width d : ℕ) (hwidth : 0 < width) (hd : 0 < d) :
    ((width * d + (width + 1) : ℕ) : ℝ) *
          Real.log ((width * d + (width + 1) : ℕ) : ℝ) -
        (width * d : ℕ) * Real.log (d : ℝ) -
          (width + 1 : ℕ) * Real.log ((width + 1 : ℕ) : ℝ) ≤
      ((width * d + (width + 1) : ℕ) : ℝ) *
        Real.log ((width + 1 : ℕ) : ℝ) := by
  have htotalPos : 0 < ((width * d + (width + 1) : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_pos (width * d + width)
  have hratioNonneg : 0 ≤
      ((width * d : ℕ) / (width * d + (width + 1) : ℕ) : ℝ) := by
    positivity
  have hratioLeOne :
      ((width * d : ℕ) / (width * d + (width + 1) : ℕ) : ℝ) ≤ 1 := by
    apply (div_le_one₀ htotalPos).mpr
    exact_mod_cast (show width * d ≤ width * d + (width + 1) by omega)
  calc
    ((width * d + (width + 1) : ℕ) : ℝ) *
          Real.log ((width * d + (width + 1) : ℕ) : ℝ) -
        (width * d : ℕ) * Real.log (d : ℝ) -
          (width + 1 : ℕ) * Real.log ((width + 1 : ℕ) : ℝ) =
        ((width * d + (width + 1) : ℕ) : ℝ) *
          Real.qaryEntropy (width + 1)
            ((width * d : ℕ) / (width * d + (width + 1) : ℕ) : ℝ) :=
      (qaryEntropy_twoLayer_ratio width d hwidth hd).symm
    _ ≤ ((width * d + (width + 1) : ℕ) : ℝ) *
          Real.log ((width + 1 : ℕ) : ℝ) := by
      apply mul_le_mul_of_nonneg_left
      · exact qaryEntropy_le_log (width + 1) (by omega) _ hratioNonneg hratioLeOne
      · exact htotalPos.le

/--
The real two-layer product envelope in Baum--Haussler form.  It converts the
separate Sauer denominators for the `width` weak nodes and the output node
into the total-node expression `(width + 1) * e * m / D`.
-/
theorem baumHaussler_twoLayer_envelope
    (width d : ℕ) (hwidth : 0 < width) (hd : 0 < d)
    (m : ℝ) (hm : 0 < m) :
    (Real.exp 1 * m / (d : ℝ)) ^ (width * d) *
        (Real.exp 1 * m / ((width + 1 : ℕ) : ℝ)) ^ (width + 1) ≤
      (((width + 1 : ℕ) : ℝ) * Real.exp 1 * m /
        ((width * d + (width + 1) : ℕ) : ℝ)) ^
          (width * d + (width + 1) : ℕ) := by
  let firstMass : ℕ := width * d
  let outputMass : ℕ := width + 1
  let totalMass : ℕ := firstMass + outputMass
  let common : ℝ := Real.exp 1 * m
  have hfirstMassPos : 0 < (firstMass : ℝ) := by
    dsimp [firstMass]
    exact_mod_cast Nat.mul_pos hwidth hd
  have houtputMassPos : 0 < (outputMass : ℝ) := by
    dsimp [outputMass]
    exact_mod_cast Nat.succ_pos width
  have htotalMassPos : 0 < (totalMass : ℝ) := by
    dsimp [totalMass, firstMass, outputMass]
    exact_mod_cast Nat.succ_pos (width * d + width)
  have htotalMassSum : (totalMass : ℝ) =
      (firstMass : ℝ) + (outputMass : ℝ) := by
    dsimp [totalMass, firstMass, outputMass]
    norm_num
  have hcommonPos : 0 < common := by
    dsimp [common]
    exact mul_pos (Real.exp_pos _) hm
  have hdPos : 0 < (d : ℝ) := by exact_mod_cast hd
  have hfirstBasePos : 0 < common / (d : ℝ) := div_pos hcommonPos hdPos
  have houtputBasePos : 0 < common / (outputMass : ℝ) :=
    div_pos hcommonPos houtputMassPos
  have hcombinedBasePos : 0 <
      (outputMass : ℝ) * common / (totalMass : ℝ) :=
    div_pos (mul_pos houtputMassPos hcommonPos) htotalMassPos
  have hdenominatorEntropy :
      (totalMass : ℝ) * Real.log (totalMass : ℝ) -
          (firstMass : ℝ) * Real.log (d : ℝ) -
            (outputMass : ℝ) * Real.log (outputMass : ℝ) ≤
        (totalMass : ℝ) * Real.log (outputMass : ℝ) := by
    simpa [firstMass, outputMass, totalMass] using
      baumHaussler_twoLayer_log_denominator_le width d hwidth hd
  suffices hcomparison : (common / (d : ℝ)) ^ firstMass *
      (common / (outputMass : ℝ)) ^ outputMass ≤
    ((outputMass : ℝ) * common / (totalMass : ℝ)) ^ totalMass by
    simpa [common, firstMass, outputMass, totalMass, mul_assoc] using hcomparison
  apply (Real.log_le_log_iff
    (mul_pos (pow_pos hfirstBasePos _) (pow_pos houtputBasePos _))
    (pow_pos hcombinedBasePos _)).mp
  rw [Real.log_mul (pow_ne_zero _ hfirstBasePos.ne')
      (pow_ne_zero _ houtputBasePos.ne'), Real.log_pow, Real.log_pow,
    Real.log_pow]
  rw [Real.log_div hcommonPos.ne' hdPos.ne',
    Real.log_div hcommonPos.ne' houtputMassPos.ne',
    Real.log_div (mul_ne_zero houtputMassPos.ne' hcommonPos.ne') htotalMassPos.ne',
    Real.log_mul houtputMassPos.ne' hcommonPos.ne']
  have hcommonMass : (totalMass : ℝ) * Real.log common =
      (firstMass : ℝ) * Real.log common + (outputMass : ℝ) * Real.log common := by
    rw [htotalMassSum]
    ring
  linarith [hdenominatorEntropy, hcommonMass]

/-- The zero-one feature vector generated by a fixed tuple of weak traces. -/
noncomputable def traceFeatureVector
    {X : Type*} {width : ℕ} (sample : Finset X)
    (inputTraces : Fin width → Finset sample) :
    sample → Fin width → ℝ := by
  classical
  exact fun point index => if point ∈ inputTraces index then 1 else 0

/-- The distinct zero-one feature vectors generated by a tuple of weak traces. -/
noncomputable def traceFeatureSupport
    {X : Type*} {width : ℕ} (sample : Finset X)
    (inputTraces : Fin width → Finset sample) : Finset (Fin width → ℝ) :=
  finiteFeatureSupport (traceFeatureVector sample inputTraces)

/-- Every sampled zero-one trace vector belongs to its finite support. -/
theorem mem_traceFeatureSupport
    {X : Type*} {width : ℕ} (sample : Finset X)
    (inputTraces : Fin width → Finset sample) (point : sample) :
    traceFeatureVector sample inputTraces point ∈
      traceFeatureSupport sample inputTraces := by
  exact mem_finiteFeatureSupport (traceFeatureVector sample inputTraces) point

/-- Pull a labeling of the distinct trace vectors back to the original sample. -/
noncomputable def thresholdOutputLabelPullback
    {X : Type*} {width : ℕ} (sample : Finset X)
    (inputTraces : Fin width → Finset sample)
    (labels : Finset (traceFeatureSupport sample inputTraces)) : Finset sample := by
  classical
  exact sample.attach.filter fun point =>
    (⟨traceFeatureVector sample inputTraces point,
      mem_traceFeatureSupport sample inputTraces point⟩ :
        traceFeatureSupport sample inputTraces) ∈ labels

/--
All sample labelings obtainable by placing an affine threshold above a fixed
tuple of weak traces.
-/
noncomputable def affineThresholdOutputLabels
    {X : Type*} {width : ℕ} (sample : Finset X)
    (inputTraces : Fin width → Finset sample) : Finset (Finset sample) := by
  classical
  exact (binaryTrace (affineThresholdClass width)
    (traceFeatureSupport sample inputTraces)).image
      (thresholdOutputLabelPullback sample inputTraces)

/--
When weak traces come from actual classifiers, their trace feature vector is
exactly the Boolean feature vector used by `binaryThresholdCombination`.
-/
theorem traceFeatureVector_eq_binaryFeatureVector
    {X : Type*} {width : ℕ} (sample : Finset X)
    (hypotheses : Fin width → BinaryClassifier X) (point : sample) :
    traceFeatureVector sample
        (fun index => binaryClassifierTrace (hypotheses index) sample) point =
      binaryFeatureVector width hypotheses point.1 := by
  funext index
  simp [traceFeatureVector, binaryFeatureVector, binaryClassifierTrace]

/--
The trace of a concrete weighted threshold combination is one of the output
labelings associated with its tuple of weak traces.
-/
theorem binaryThresholdCombination_trace_mem_affineThresholdOutputLabels
    {X : Type*} {width : ℕ} (sample : Finset X)
    (hypotheses : Fin width → BinaryClassifier X)
    (weights : Fin width → ℝ) (offset : ℝ) :
    binaryClassifierTrace (binaryThresholdCombination width weights offset hypotheses) sample ∈
      affineThresholdOutputLabels sample
        (fun index => binaryClassifierTrace (hypotheses index) sample) := by
  classical
  let outputClassifier := affineThresholdClassifier weights offset
  let outputLabels := binaryClassifierTrace outputClassifier
    (traceFeatureSupport sample
      (fun index => binaryClassifierTrace (hypotheses index) sample))
  refine Finset.mem_image.mpr ⟨outputLabels, ?_, ?_⟩
  · exact binaryClassifierTrace_mem_binaryTrace
      (concepts := affineThresholdClass width) (classifier := outputClassifier)
      (by
        dsimp [outputClassifier, affineThresholdClass]
        exact ⟨weights, offset, rfl⟩) _
  · apply Finset.ext
    intro point
    let inputTraces : Fin width → Finset sample :=
      fun index => binaryClassifierTrace (hypotheses index) sample
    let featureSupport := traceFeatureSupport sample inputTraces
    have hfeature : traceFeatureVector sample inputTraces point =
        binaryFeatureVector width hypotheses point.1 :=
      traceFeatureVector_eq_binaryFeatureVector sample hypotheses point
    have hbinaryMem : binaryFeatureVector width hypotheses point.1 ∈ featureSupport := by
      rw [← hfeature]
      exact mem_traceFeatureSupport sample inputTraces point
    have hsubtype :
        (⟨traceFeatureVector sample inputTraces point,
          mem_traceFeatureSupport sample inputTraces point⟩ : featureSupport) =
          ⟨binaryFeatureVector width hypotheses point.1, hbinaryMem⟩ :=
      Subtype.ext hfeature
    simp only [thresholdOutputLabelPullback, Finset.mem_filter,
      Finset.mem_attach, true_and]
    change (⟨traceFeatureVector sample inputTraces point,
        mem_traceFeatureSupport sample inputTraces point⟩ : featureSupport) ∈ outputLabels ↔
      point ∈ binaryClassifierTrace
        (binaryThresholdCombination width weights offset hypotheses) sample
    rw [hsubtype]
    change (⟨binaryFeatureVector width hypotheses point.1, hbinaryMem⟩ : featureSupport) ∈
        binaryClassifierTrace outputClassifier featureSupport ↔
      point ∈ binaryClassifierTrace
        (binaryThresholdCombination width weights offset hypotheses) sample
    simp [binaryClassifierTrace, outputClassifier, binaryThresholdCombination,
      binaryThresholdScore, affineThresholdClassifier, affineThresholdScore]

/--
For fixed weak traces, affine-threshold output labelings are no more numerous
than the usual VC binomial envelope for `width + 1` dimensions.
-/
theorem card_affineThresholdOutputLabels_le_sum_choose
    {X : Type*} {width : ℕ} (sample : Finset X)
    (inputTraces : Fin width → Finset sample) :
    (affineThresholdOutputLabels sample inputTraces).card ≤
      ∑ k ∈ Finset.Iic (width + 1), sample.card.choose k := by
  classical
  have hfeatureCard : (traceFeatureSupport sample inputTraces).card ≤ sample.card := by
    simpa [traceFeatureSupport, Fintype.card_coe] using
      card_finiteFeatureSupport_le_fintype_card
        (traceFeatureVector sample inputTraces)
  calc
    (affineThresholdOutputLabels sample inputTraces).card ≤
        (binaryTrace (affineThresholdClass width)
          (traceFeatureSupport sample inputTraces)).card := by
      exact Finset.card_image_le
    _ = binaryGrowth (affineThresholdClass width)
          (traceFeatureSupport sample inputTraces) := rfl
    _ ≤ ∑ k ∈ Finset.Iic (width + 1), sample.card.choose k :=
      binaryGrowth_le_sum_choose_of_vcDimensionAtMost_le_card
        (vcDimensionAtMost_affineThresholdClass width)
        (traceFeatureSupport sample inputTraces) hfeatureCard

/--
Every trace of a finite affine-threshold composition belongs to the union over
its possible tuple of weak traces of the corresponding output labelings.
-/
theorem binaryTrace_thresholdCombinationClass_subset_twoLayerOutput
    {X : Type*} [DecidableEq X] {width : ℕ} (concepts : Set (BinaryClassifier X))
    (sample : Finset X) :
    binaryTrace (binaryThresholdCombinationClass concepts width) sample ⊆
      (Fintype.piFinset fun _ : Fin width => binaryTrace concepts sample).biUnion
        (affineThresholdOutputLabels sample) := by
  classical
  intro labels hlabels
  let classifier := classifierOfBinaryTrace
    (binaryThresholdCombinationClass concepts width) sample labels
  have hclassifier : classifier ∈ binaryThresholdCombinationClass concepts width :=
    classifierOfBinaryTrace_mem hlabels
  rcases hclassifier with ⟨hypotheses, hhypotheses, weights, offset, hclassifierEq⟩
  let inputTraces : Fin width → Finset sample :=
    fun index => binaryClassifierTrace (hypotheses index) sample
  refine Finset.mem_biUnion.mpr ⟨inputTraces, ?_, ?_⟩
  · simp only [Fintype.mem_piFinset]
    intro index
    exact binaryClassifierTrace_mem_binaryTrace (hhypotheses index) sample
  · have htraceEq : binaryClassifierTrace classifier sample = labels := by
      apply Finset.ext
      intro point
      simpa [binaryClassifierTrace] using
        (classifierOfBinaryTrace_realizes hlabels point).symm
    rw [← htraceEq, hclassifierEq]
    simpa [inputTraces] using
      binaryThresholdCombination_trace_mem_affineThresholdOutputLabels
        sample hypotheses weights offset

/--
Finite two-layer trace-growth bound: choose one realized weak trace at every
first-layer node, then choose one affine-threshold output trace.  This is the
two-layer product step underlying the Baum--Haussler route.
-/
theorem binaryGrowth_thresholdCombinationClass_le_twoLayer
    {X : Type*} {width : ℕ} (concepts : Set (BinaryClassifier X))
    (sample : Finset X) :
    binaryGrowth (binaryThresholdCombinationClass concepts width) sample ≤
      (binaryGrowth concepts sample) ^ width *
        (∑ k ∈ Finset.Iic (width + 1), sample.card.choose k) := by
  classical
  let inputTraceTuples : Finset (Fin width → Finset sample) :=
    Fintype.piFinset fun _ : Fin width => binaryTrace concepts sample
  let outputBound : ℕ := ∑ k ∈ Finset.Iic (width + 1), sample.card.choose k
  calc
    binaryGrowth (binaryThresholdCombinationClass concepts width) sample =
        (binaryTrace (binaryThresholdCombinationClass concepts width) sample).card := rfl
    _ ≤ (inputTraceTuples.biUnion (affineThresholdOutputLabels sample)).card :=
      Finset.card_le_card
        (by simpa [inputTraceTuples] using
          binaryTrace_thresholdCombinationClass_subset_twoLayerOutput concepts sample)
    _ ≤ ∑ inputTraces ∈ inputTraceTuples,
          (affineThresholdOutputLabels sample inputTraces).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _ ∈ inputTraceTuples, outputBound := by
      apply Finset.sum_le_sum
      intro inputTraces _
      exact card_affineThresholdOutputLabels_le_sum_choose sample inputTraces
    _ = inputTraceTuples.card * outputBound := by
      exact Finset.sum_const_nat fun _ _ => rfl
    _ = (binaryGrowth concepts sample) ^ width *
          (∑ k ∈ Finset.Iic (width + 1), sample.card.choose k) := by
      rw [show inputTraceTuples.card = (binaryTrace concepts sample).card ^ width by
        simp [inputTraceTuples, Fintype.card_piFinset_const]]
      simp only [outputBound, binaryGrowth]

/--
Source-independent VC-binomial form of the two-layer trace-growth bound.  It
combines the preceding exact trace factorization with Sauer--Shelah for the
weak class.
-/
theorem binaryGrowth_thresholdCombinationClass_le_vcBinomial
    {X : Type*} {width d : ℕ} (concepts : Set (BinaryClassifier X))
    (hvc : VCDimensionAtMost concepts d) (sample : Finset X) :
    binaryGrowth (binaryThresholdCombinationClass concepts width) sample ≤
      (∑ k ∈ Finset.Iic d, sample.card.choose k) ^ width *
        (∑ k ∈ Finset.Iic (width + 1), sample.card.choose k) := by
  calc
    binaryGrowth (binaryThresholdCombinationClass concepts width) sample ≤
        (binaryGrowth concepts sample) ^ width *
          (∑ k ∈ Finset.Iic (width + 1), sample.card.choose k) :=
      binaryGrowth_thresholdCombinationClass_le_twoLayer concepts sample
    _ ≤ (∑ k ∈ Finset.Iic d, sample.card.choose k) ^ width *
          (∑ k ∈ Finset.Iic (width + 1), sample.card.choose k) := by
      apply Nat.mul_le_mul_right
      exact Nat.pow_le_pow_left
        (binaryGrowth_le_sum_choose_of_vcDimensionAtMost hvc sample) width

/--
Baum--Haussler's two-layer growth bound, proved here from the finite trace
factorization, Sauer--Shelah, the affine-threshold VC bound, and the checked
entropy compression above.  `sample.card` is the source's restriction size
`m`, and `D = width*d + (width+1)` is the sum of node VC dimensions.
-/
theorem binaryGrowth_thresholdCombinationClass_le_baumHaussler
    {X : Type*} {width d : ℕ} (concepts : Set (BinaryClassifier X))
    (hwidth : 0 < width) (hd : 0 < d)
    (hvc : VCDimensionAtMost concepts d) (sample : Finset X)
    (hdSample : d ≤ sample.card) (houtputSample : width + 1 ≤ sample.card) :
    (binaryGrowth (binaryThresholdCombinationClass concepts width) sample : ℝ) ≤
      ((((width + 1 : ℕ) : ℝ) * Real.exp 1 * (sample.card : ℝ) /
        ((width * d + (width + 1) : ℕ) : ℝ)) ^
          (width * d + (width + 1) : ℕ)) := by
  have hnat := binaryGrowth_thresholdCombinationClass_le_vcBinomial
    (width := width) concepts hvc sample
  have hsamplePos : 0 < (sample.card : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (Nat.succ_pos width) houtputSample
  have hfirstEnvelope := sum_choose_le_exp_one_mul_div_pow hd hdSample
  have houtputEnvelope := sum_choose_le_exp_one_mul_div_pow
    (Nat.succ_pos width) houtputSample
  calc
    (binaryGrowth (binaryThresholdCombinationClass concepts width) sample : ℝ) ≤
        ((∑ k ∈ Finset.Iic d, sample.card.choose k : ℕ) ^ width *
          (∑ k ∈ Finset.Iic (width + 1), sample.card.choose k : ℕ) : ℕ) := by
      exact_mod_cast hnat
    _ = (∑ k ∈ Finset.Iic d, (sample.card.choose k : ℝ)) ^ width *
          (∑ k ∈ Finset.Iic (width + 1), (sample.card.choose k : ℝ)) := by
      norm_cast
    _ ≤ (Real.exp 1 * (sample.card : ℝ) / (d : ℝ)) ^ (d * width) *
          (Real.exp 1 * (sample.card : ℝ) /
            ((width + 1 : ℕ) : ℝ)) ^ (width + 1) := by
      gcongr
      · calc
          (∑ k ∈ Finset.Iic d, (sample.card.choose k : ℝ)) ^ width ≤
              ((Real.exp 1 * (sample.card : ℝ) / (d : ℝ)) ^ d) ^ width :=
            pow_le_pow_left₀
              (by positivity : 0 ≤ ∑ k ∈ Finset.Iic d, (sample.card.choose k : ℝ))
              hfirstEnvelope width
          _ = (Real.exp 1 * (sample.card : ℝ) / (d : ℝ)) ^ (d * width) := by
            rw [← pow_mul]
    _ = (Real.exp 1 * (sample.card : ℝ) / (d : ℝ)) ^ (width * d) *
          (Real.exp 1 * (sample.card : ℝ) /
            ((width + 1 : ℕ) : ℝ)) ^ (width + 1) := by
      rw [Nat.mul_comm d width]
    _ ≤ (((width + 1 : ℕ) : ℝ) * Real.exp 1 * (sample.card : ℝ) /
          ((width * d + (width + 1) : ℕ) : ℝ)) ^
            (width * d + (width + 1) : ℕ) :=
      baumHaussler_twoLayer_envelope width d hwidth hd _ hsamplePos

/--
The Baum--Haussler growth calculation rules out shattering a full finite
sample once its cardinality reaches the displayed source threshold.
-/
theorem binaryTrace_thresholdCombinationClass_not_shatters_univ_of_source_size
    {X : Type*} [DecidableEq X] {width d : ℕ} (concepts : Set (BinaryClassifier X))
    (hwidth : 0 < width) (hd : 0 < d)
    (hvc : VCDimensionAtMost concepts d) (sample : Finset X)
    (hdSample : d ≤ sample.card) (houtputSample : width + 1 ≤ sample.card)
    (hsize : 2 * ((width * d + (width + 1) : ℕ) : ℝ) *
        Real.logb 2 (Real.exp 1 * ((width + 1 : ℕ) : ℝ)) ≤
          (sample.card : ℝ)) :
    ¬ (binaryTrace (binaryThresholdCombinationClass concepts width) sample).Shatters
      Finset.univ := by
  intro hshatters
  have htotal : 0 < width * d + (width + 1) := by omega
  have hgrowth := binaryGrowth_thresholdCombinationClass_le_baumHaussler
    concepts hwidth hd hvc sample hdSample houtputSample
  have hsourceStrict := baumHaussler_envelope_lt_two_pow
    (width + 1) (width * d + (width + 1)) sample.card (by omega) htotal hsize
  have hstrict :
      (binaryGrowth (binaryThresholdCombinationClass concepts width) sample : ℝ) <
        (2 : ℝ) ^ sample.card :=
    hgrowth.trans_lt hsourceStrict
  have hfull : binaryTrace (binaryThresholdCombinationClass concepts width) sample =
      Finset.univ := Finset.shatters_univ.mp hshatters
  have hgrowthEq : binaryGrowth (binaryThresholdCombinationClass concepts width) sample =
      2 ^ sample.card := by
    unfold binaryGrowth
    rw [hfull]
    simp [Fintype.card_coe]
  rw [hgrowthEq] at hstrict
  norm_num at hstrict

/--
Freund--Schapire Theorem 8: if the weak binary class has VC dimension at most
`d ≥ 2`, then the VC dimension of its `width`-term affine-threshold closure is
at most `2 (d+1) (width+1) log₂(e (width+1))`.  The proof is the checked
finite-trace specialization of their Baum--Haussler argument; no network or
linear-threshold VC statement is introduced as an opaque premise.
-/
theorem vcDimension_thresholdCombinationClass_le_source_theorem8
    {X : Type*} {width d : ℕ} (concepts : Set (BinaryClassifier X))
    (hwidth : 0 < width) (hd : 2 ≤ d)
    (hvc : VCDimensionAtMost concepts d) :
    ∀ sample : Finset X,
      (binaryTraceVCDimension (binaryThresholdCombinationClass concepts width) sample : ℝ) ≤
        sourceThresholdCombinationVCBound width d := by
  intro sample
  classical
  let traceFamily := binaryTrace (binaryThresholdCombinationClass concepts width) sample
  by_cases hnonempty : traceFamily.shatterer.Nonempty
  · rcases Finset.exists_mem_eq_sup traceFamily.shatterer hnonempty Finset.card with
      ⟨subsample, hsubsample, hsup⟩
    change (traceFamily.vcDim : ℝ) ≤ sourceThresholdCombinationVCBound width d
    unfold Finset.vcDim
    rw [hsup]
    by_contra hnot
    have hboundLt : sourceThresholdCombinationVCBound width d < (subsample.card : ℝ) :=
      lt_of_not_ge hnot
    have hshatters : traceFamily.Shatters subsample :=
      Finset.mem_shatterer.mp hsubsample
    let rawSample : Finset X := rawSubsample sample subsample
    have hrawCard : rawSample.card = subsample.card :=
      card_rawSubsample sample subsample
    have hrawShatters :
        (binaryTrace (binaryThresholdCombinationClass concepts width) rawSample).Shatters
          Finset.univ := by
      simpa [rawSample] using
        binaryTrace_shatters_univ_rawSubsample_of_shatters
          (binaryThresholdCombinationClass concepts width) sample subsample hshatters
    let totalDimension : ℕ := width * d + (width + 1)
    let nodeCount : ℕ := width + 1
    let sourceScale : ℝ :=
      Real.logb 2 (Real.exp 1 * (nodeCount : ℝ))
    let coarseDimension : ℕ := nodeCount * (d + 1)
    have htotalLeCoarse : totalDimension ≤ coarseDimension := by
      dsimp [totalDimension, coarseDimension, nodeCount]
      calc
        width * d + (width + 1) ≤ width * d + (width + 1) + d :=
          Nat.le_add_right _ _
        _ = (width + 1) * (d + 1) := by ring
    have hdLeCoarse : d ≤ coarseDimension := by
      dsimp [coarseDimension, nodeCount]
      calc
        d ≤ d + 1 := Nat.le_succ _
        _ ≤ (width + 1) * (d + 1) :=
          Nat.le_mul_of_pos_left _ (Nat.succ_pos width)
    have hnodesLeCoarse : nodeCount ≤ coarseDimension := by
      dsimp [coarseDimension]
      exact Nat.le_mul_of_pos_right _ (Nat.succ_pos d)
    have hcoarsePos : 0 < (coarseDimension : ℝ) := by
      dsimp [coarseDimension, nodeCount]
      positivity
    have hscaleGtTwo : 2 < sourceScale := by
      dsimp [sourceScale, nodeCount]
      exact two_lt_logb_exp_one_mul_nat (width + 1) (by omega)
    have hcoarseLtBound : (coarseDimension : ℝ) <
        sourceThresholdCombinationVCBound width d := by
      unfold sourceThresholdCombinationVCBound
      dsimp [coarseDimension, nodeCount, sourceScale] at hcoarsePos hscaleGtTwo ⊢
      have hfactor : 1 < 2 * Real.logb 2
          (Real.exp 1 * ((width + 1 : ℕ) : ℝ)) := by linarith
      calc
        (((width + 1) * (d + 1) : ℕ) : ℝ) =
            (((width + 1) * (d + 1) : ℕ) : ℝ) * 1 := by ring
        _ < (((width + 1) * (d + 1) : ℕ) : ℝ) *
            (2 * Real.logb 2 (Real.exp 1 * ((width + 1 : ℕ) : ℝ)) : ℝ) := by
          exact mul_lt_mul_of_pos_left hfactor hcoarsePos
        _ = 2 * ((d + 1 : ℕ) : ℝ) * ((width + 1 : ℕ) : ℝ) *
            Real.logb 2 (Real.exp 1 * ((width + 1 : ℕ) : ℝ)) := by
          push_cast
          ring
    have hcoarseLtRaw : (coarseDimension : ℝ) < (rawSample.card : ℝ) := by
      rw [hrawCard]
      exact hcoarseLtBound.trans hboundLt
    have hcoarseLtRawNat : coarseDimension < rawSample.card := by
      exact_mod_cast hcoarseLtRaw
    have hdRaw : d ≤ rawSample.card :=
      hdLeCoarse.trans hcoarseLtRawNat.le
    have hnodesRaw : nodeCount ≤ rawSample.card :=
      hnodesLeCoarse.trans hcoarseLtRawNat.le
    have hsourceSize : 2 * (totalDimension : ℝ) * sourceScale ≤
        (rawSample.card : ℝ) := by
      have htotalLeCoarseReal : (totalDimension : ℝ) ≤ (coarseDimension : ℝ) := by
        exact_mod_cast htotalLeCoarse
      have hscaleNonneg : 0 ≤ sourceScale := by linarith
      have hmul := mul_le_mul_of_nonneg_right htotalLeCoarseReal
        (by positivity : 0 ≤ 2 * sourceScale)
      calc
        2 * (totalDimension : ℝ) * sourceScale =
            (totalDimension : ℝ) * (2 * sourceScale) := by ring
        _ ≤ (coarseDimension : ℝ) * (2 * sourceScale) := hmul
        _ = sourceThresholdCombinationVCBound width d := by
          unfold sourceThresholdCombinationVCBound
          dsimp [coarseDimension, nodeCount, sourceScale]
          push_cast
          ring
        _ ≤ (rawSample.card : ℝ) := by
          rw [hrawCard]
          exact hboundLt.le
    have hnoShatter :=
      binaryTrace_thresholdCombinationClass_not_shatters_univ_of_source_size
        concepts hwidth (by omega : 0 < d) hvc rawSample hdRaw
        (by simpa [nodeCount] using hnodesRaw)
        (by simpa [totalDimension, nodeCount, sourceScale] using hsourceSize)
    exact hnoShatter hrawShatters
  · change (traceFamily.vcDim : ℝ) ≤ sourceThresholdCombinationVCBound width d
    have hempty : traceFamily.shatterer = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnonempty
    rw [Finset.vcDim, hempty]
    simp only [Finset.sup_empty]
    unfold sourceThresholdCombinationVCBound
    change ((⊥ : ℕ) : ℝ) ≤ 2 * ((d + 1 : ℕ) : ℝ) * ((width + 1 : ℕ) : ℝ) *
      Real.logb 2 (Real.exp 1 * ((width + 1 : ℕ) : ℝ))
    rw [show (⊥ : ℕ) = 0 by rfl]
    have hscalePos : 0 < Real.logb 2
        (Real.exp 1 * ((width + 1 : ℕ) : ℝ)) := by
      linarith [two_lt_logb_exp_one_mul_nat (width + 1) (by omega)]
    have hfactor : 0 ≤ 2 * ((d + 1 : ℕ) : ℝ) * ((width + 1 : ℕ) : ℝ) := by
      positivity
    simpa using (mul_nonneg hfactor hscalePos.le)

end Statistics
end AppliedModelingLib
