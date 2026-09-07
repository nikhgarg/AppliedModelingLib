import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic
import AppliedModelingLib.Foundations.Math.ExponentialBounds
import AppliedModelingLib.Foundations.Math.LinearCompressedSensing
import AppliedModelingLib.Foundations.Probability.FairCoin
import AppliedModelingLib.Foundations.Probability.MeasureInequalities
import AppliedModelingLib.Foundations.Probability.SubgaussianSquares

/-!
# Scaled Rademacher Matrices

Reusable probability and deterministic wrappers for matrices with independent
entries in `{-1/sqrt d, 1/sqrt d}`.  These are the random incoherent matrix
constructions used by LRH-style linear compressed-sensing arguments.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace AppliedModelingLib
namespace Probability
namespace RademacherMatrix

open AppliedModelingLib.Math.LinearCompressedSensing

variable {Feature Coord : Type*}

/-- The symmetric Rademacher sign encoded by a Boolean. -/
def rademacherSign (b : Bool) : ℝ :=
  if b then 1 else -1

@[simp] theorem rademacherSign_sq (b : Bool) :
    rademacherSign b ^ 2 = (1 : ℝ) := by
  cases b <;> simp [rademacherSign]

@[simp] theorem rademacherSign_mul_self (b : Bool) :
    rademacherSign b * rademacherSign b = (1 : ℝ) := by
  simpa [pow_two] using rademacherSign_sq b

@[simp] theorem abs_rademacherSign (b : Bool) :
    |rademacherSign b| = (1 : ℝ) := by
  cases b <;> simp [rademacherSign]

/-- Product sign from two feature coordinates in a sampled row. -/
def pairSign (row : Feature → Bool) (i j : Feature) : ℝ :=
  rademacherSign (row i) * rademacherSign (row j)

@[simp] theorem pairSign_mem_Icc (row : Feature → Bool) (i j : Feature) :
    pairSign row i j ∈ Set.Icc (-1 : ℝ) 1 := by
  dsimp [pairSign]
  cases row i <;> cases row j <;> norm_num [rademacherSign]

/--
Row-product fair-coin law for a random `Coord × Feature` Boolean matrix.
Rows are sampled independently, and each row is a fair Boolean vector over
features.
-/
noncomputable def rowsMeasure (Feature Coord : Type*) :
    Measure (Coord → Feature → Bool) :=
  Measure.infinitePi fun _ : Coord => FairCoin.productMeasure Feature

theorem rowsMeasure_isProbabilityMeasure (Feature Coord : Type*) :
    IsProbabilityMeasure (rowsMeasure Feature Coord) := by
  let P : Coord → Measure (Feature → Bool) :=
    fun _ => FairCoin.productMeasure Feature
  let hP : ∀ r : Coord, IsProbabilityMeasure (P r) := by
    intro r
    simpa [P] using FairCoin.productMeasure_isProbabilityMeasure Feature
  simpa [rowsMeasure, P] using
    @MeasureTheory.Measure.instIsProbabilityMeasureForallInfinitePi
      (ι := Coord) (X := fun _ : Coord => Feature → Bool)
      (mX := fun _ => by infer_instance) (μ := P) hP

/-- The marginal law of any sampled row is the fair-product law. -/
theorem map_eval_rowsMeasure (Feature Coord : Type*) (r : Coord) :
    Measure.map (fun omega : Coord → Feature → Bool => omega r)
      (rowsMeasure Feature Coord) = FairCoin.productMeasure Feature := by
  let P : Coord → Measure (Feature → Bool) :=
    fun _ => FairCoin.productMeasure Feature
  let hP : ∀ q : Coord, IsProbabilityMeasure (P q) := by
    intro q
    simpa [P] using FairCoin.productMeasure_isProbabilityMeasure Feature
  simpa [rowsMeasure, P] using
    (@MeasureTheory.Measure.infinitePi_map_eval
      (ι := Coord) (X := fun _ => Feature → Bool)
      (mX := fun _ => by infer_instance) (μ := P) hP r)

/-- Integrals of a function of one sampled row reduce to that row's fair-product law. -/
theorem integral_comp_row_rowsMeasure [Fintype Feature]
    (r : Coord) (f : (Feature → Bool) → ℝ) :
    (∫ omega : Coord → Feature → Bool, f (omega r) ∂rowsMeasure Feature Coord) =
      ∫ row : Feature → Bool, f row ∂FairCoin.productMeasure Feature := by
  calc
    (∫ omega : Coord → Feature → Bool, f (omega r) ∂rowsMeasure Feature Coord) =
        ∫ row : Feature → Bool, f row ∂Measure.map
          (fun omega : Coord → Feature → Bool => omega r)
          (rowsMeasure Feature Coord) := by
            exact (integral_map (μ := rowsMeasure Feature Coord)
              (φ := fun omega : Coord → Feature → Bool => omega r) (f := f)
              (measurable_pi_apply r).aemeasurable
              (measurable_of_finite f).aestronglyMeasurable).symm
    _ = ∫ row : Feature → Bool, f row ∂FairCoin.productMeasure Feature := by
      rw [map_eval_rowsMeasure Feature Coord r]

/-- The fair Boolean coordinates of one sampled row are independent. -/
theorem boolCoord_iIndepFun (Feature : Type*) :
    iIndepFun (fun i (row : Feature → Bool) => row i)
      (FairCoin.productMeasure Feature) := by
  let P : Feature → Measure Bool := fun _ => FairCoin.fairMeasure
  let hP : ∀ i : Feature, IsProbabilityMeasure (P i) := by
    intro i
    simpa [P] using FairCoin.fairMeasure_isProbabilityMeasure
  simpa [FairCoin.productMeasure, P] using
    @ProbabilityTheory.iIndepFun_infinitePi
      (ι := Feature) (𝓧 := fun _ : Feature => Bool)
      (m𝓧 := fun _ => by infer_instance)
      (Ω := fun _ : Feature => Bool) (mΩ := fun _ => by infer_instance)
      (P := P) hP (X := fun _ : Feature => id)
      (mX := fun _ => measurable_id)

/-- A single fair Rademacher sign has mean zero. -/
theorem integral_rademacherSign_fairMeasure :
    (∫ b : Bool, rademacherSign b ∂FairCoin.fairMeasure) = 0 := by
  simp [rademacherSign, FairCoin.fairMeasure, PMF.integral_eq_sum, PMF.bernoulli]

/-- A fair-product Boolean coordinate, mapped to a Rademacher sign, has mean zero. -/
theorem integral_rademacherSign_productMeasure
    (Feature : Type*) (i : Feature) :
    (∫ row : Feature → Bool,
        rademacherSign (row i) ∂FairCoin.productMeasure Feature) = 0 := by
  let P : Feature → Measure Bool := fun _ => FairCoin.fairMeasure
  let hP : ∀ i : Feature, IsProbabilityMeasure (P i) := by
    intro i
    simpa [P] using FairCoin.fairMeasure_isProbabilityMeasure
  let f : Bool → ℝ := rademacherSign
  have hf :
      AEStronglyMeasurable f
        (Measure.map (fun row : Feature → Bool => row i)
          (FairCoin.productMeasure Feature)) :=
    (measurable_of_finite f).aestronglyMeasurable
  calc
    (∫ row : Feature → Bool,
        rademacherSign (row i) ∂FairCoin.productMeasure Feature)
        = ∫ row : Feature → Bool, f (row i) ∂FairCoin.productMeasure Feature := by
          rfl
    _ = ∫ b : Bool, f b ∂Measure.map
          (fun row : Feature → Bool => row i)
          (FairCoin.productMeasure Feature) := by
          exact (integral_map
            (μ := FairCoin.productMeasure Feature)
            (φ := fun row : Feature → Bool => row i)
            (f := f) (measurable_pi_apply i).aemeasurable hf).symm
    _ = ∫ b : Bool, f b ∂FairCoin.fairMeasure := by
          rw [show
              Measure.map (fun row : Feature → Bool => row i)
                  (FairCoin.productMeasure Feature) =
                FairCoin.fairMeasure from by
              simpa [FairCoin.productMeasure, P] using
                (@MeasureTheory.Measure.infinitePi_map_eval
                  (ι := Feature) (X := fun _ : Feature => Bool)
                  (mX := fun _ => by infer_instance) (μ := P) hP i)]
    _ = 0 := integral_rademacherSign_fairMeasure

/-- A weighted Rademacher coordinate in one sampled row. -/
def weightedSign (x : Feature → ℝ) (row : Feature → Bool) (i : Feature) : ℝ :=
  rademacherSign (row i) * x i

/-- A Rademacher coordinate times a fixed scalar lies in its symmetric interval. -/
theorem weightedSign_mem_Icc (x : Feature → ℝ) (row : Feature → Bool) (i : Feature) :
    weightedSign x row i ∈ Set.Icc (-|x i|) |x i| := by
  cases h : row i
  · norm_num [weightedSign, rademacherSign, h]
    exact ⟨le_abs_self _, neg_le_abs _⟩
  · norm_num [weightedSign, rademacherSign, h]
    exact ⟨neg_abs_le _, le_abs_self _⟩

/-- Independent fair row coordinates remain independent after fixed scalar weights. -/
theorem weightedSign_iIndepFun (x : Feature → ℝ) :
    iIndepFun (fun i (row : Feature → Bool) => weightedSign x row i)
      (FairCoin.productMeasure Feature) := by
  simpa [weightedSign] using
    (boolCoord_iIndepFun Feature).comp
      (fun i b => rademacherSign b * x i)
      (fun _ => measurable_of_finite _)

/-- Every weighted Rademacher coordinate has mean zero. -/
theorem integral_weightedSign_productMeasure
    (Feature : Type*) (x : Feature → ℝ) (i : Feature) :
    (∫ row : Feature → Bool,
        weightedSign x row i ∂FairCoin.productMeasure Feature) = 0 := by
  simp only [weightedSign, integral_mul_const,
    integral_rademacherSign_productMeasure Feature i, zero_mul]

/--
Hoeffding's lemma for an arbitrary weighted Rademacher coordinate.  The
parameter is deliberately retained in the exact interval-width form supplied
by Mathlib; the finite `l2` simplification is a separate algebraic layer.
-/
theorem hasSubgaussianMGF_weightedSign
    (x : Feature → ℝ) (i : Feature) :
    HasSubgaussianMGF (fun row : Feature → Bool => weightedSign x row i)
      ((‖|x i| - (-|x i|)‖₊ / 2) ^ 2)
      (FairCoin.productMeasure Feature) := by
  letI : IsProbabilityMeasure (FairCoin.productMeasure Feature) :=
    FairCoin.productMeasure_isProbabilityMeasure Feature
  apply hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
  · exact
      (((measurable_of_finite rademacherSign).comp (measurable_pi_apply i)).mul
        measurable_const).aemeasurable
  · exact ae_of_all _ fun row => weightedSign_mem_Icc x row i
  · exact integral_weightedSign_productMeasure Feature x i

/-- The scalar Hoeffding parameter of a weighted sign is exactly its square. -/
theorem weightedSign_subgaussianParameter_coe_eq_sq (a : ℝ) :
    (((‖|a| - (-|a|)‖₊ / 2) ^ 2 : NNReal) : ℝ) = a ^ 2 := by
  change (abs (|a| - (-|a|)) / 2) ^ 2 = a ^ 2
  have hrewrite : |a| - (-|a|) = 2 * |a| := by ring
  rw [hrewrite, abs_of_nonneg]
  · rw [show 2 * |a| / 2 = |a| by ring]
    exact sq_abs a
  · positivity

/--
An arbitrary linear form of a fair Rademacher row is sub-Gaussian.  This
packages the fixed-vector concentration input needed before a supportwise RIP
argument can pass from finitely many net points to a whole coordinate
subspace.
-/
theorem hasSubgaussianMGF_sum_weightedSign
    [Fintype Feature] (x : Feature → ℝ) :
    HasSubgaussianMGF
      (fun row : Feature → Bool => ∑ i : Feature, weightedSign x row i)
      (∑ i : Feature, ((‖|x i| - (-|x i|)‖₊ / 2) ^ 2))
      (FairCoin.productMeasure Feature) := by
  exact HasSubgaussianMGF.sum_of_iIndepFun
    (weightedSign_iIndepFun x)
    (fun i _ => hasSubgaussianMGF_weightedSign x i)

/-- The summed Rademacher Hoeffding parameter is the squared Euclidean norm. -/
theorem sum_weightedSign_subgaussianParameter_coe_eq_l2Sq
    [Fintype Feature] (x : Feature → ℝ) :
    ((∑ i : Feature, ((‖|x i| - (-|x i|)‖₊ / 2) ^ 2) : NNReal) : ℝ) =
      AppliedModelingLib.FiniteDimensionalNorms.l2Sq x := by
  rw [AppliedModelingLib.FiniteDimensionalNorms.l2Sq]
  simp only [NNReal.coe_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  exact weightedSign_subgaussianParameter_coe_eq_sq (x i)

/-- A Rademacher row linear form has variance proxy exactly `l2Sq x`. -/
theorem hasSubgaussianMGF_sum_weightedSign_l2Sq
    [Fintype Feature] (x : Feature → ℝ) :
    HasSubgaussianMGF
      (fun row : Feature → Bool => ∑ i : Feature, weightedSign x row i)
      ⟨AppliedModelingLib.FiniteDimensionalNorms.l2Sq x,
        by
          rw [AppliedModelingLib.FiniteDimensionalNorms.l2Sq]
          exact Finset.sum_nonneg fun i _hi => sq_nonneg (x i)⟩
      (FairCoin.productMeasure Feature) := by
  let c : NNReal :=
    ⟨AppliedModelingLib.FiniteDimensionalNorms.l2Sq x,
      by
        rw [AppliedModelingLib.FiniteDimensionalNorms.l2Sq]
        exact Finset.sum_nonneg fun i _hi => sq_nonneg (x i)⟩
  have hparameter :
      (∑ i : Feature, ((‖|x i| - (-|x i|)‖₊ / 2) ^ 2)) = c := by
    apply NNReal.eq
    simpa [c] using sum_weightedSign_subgaussianParameter_coe_eq_l2Sq x
  have hsub := hasSubgaussianMGF_sum_weightedSign x
  rw [hparameter] at hsub
  exact hsub

/--
For a unit `l2` coefficient vector, the centered squared Rademacher-row
linear form has the local quadratic MGF bound used by independent-row
concentration arguments.
-/
theorem integral_exp_mul_centered_sq_sum_weightedSign_le_exp_four_mul_sq
    [Fintype Feature] (x : Feature → ℝ)
    (hunit : AppliedModelingLib.FiniteDimensionalNorms.l2Sq x = 1)
    (lambda : ℝ) (hlambda : 0 ≤ lambda) (hlambda_quarter : lambda ≤ 1 / 4) :
    (∫ row : Feature → Bool,
        Real.exp (lambda * ((∑ i : Feature, weightedSign x row i) ^ 2 - 1))
          ∂FairCoin.productMeasure Feature) ≤ Real.exp (4 * lambda ^ 2) := by
  letI : IsProbabilityMeasure (FairCoin.productMeasure Feature) :=
    FairCoin.productMeasure_isProbabilityMeasure Feature
  let c : NNReal := ⟨AppliedModelingLib.FiniteDimensionalNorms.l2Sq x,
    by
      rw [AppliedModelingLib.FiniteDimensionalNorms.l2Sq]
      exact Finset.sum_nonneg fun i _hi => sq_nonneg (x i)⟩
  have hc : c = 1 := by
    apply Subtype.ext
    dsimp [c]
    exact hunit
  have hsub : HasSubgaussianMGF
      (fun row : Feature → Bool => ∑ i : Feature, weightedSign x row i)
      1 (FairCoin.productMeasure Feature) := by
    simpa [c, hc] using hasSubgaussianMGF_sum_weightedSign_l2Sq x
  exact
    integral_exp_mul_centered_sq_le_exp_four_mul_sq_of_hasSubgaussianMGF_one
      (FairCoin.productMeasure Feature) _ hsub lambda hlambda hlambda_quarter

/--
One-sided fixed-vector concentration for a fair Rademacher row.  Unlike the
entrywise coherence estimate, its exponent scales with the Euclidean norm of
the vector and is the scalar ingredient needed for RIP-scale arguments.
-/
theorem measure_sum_weightedSign_ge_le_exp_l2Sq
    [Fintype Feature] (x : Feature → ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    (FairCoin.productMeasure Feature).real
        {row | ε ≤ ∑ i : Feature, weightedSign x row i} ≤
      Real.exp (-ε ^ 2 /
        (2 * AppliedModelingLib.FiniteDimensionalNorms.l2Sq x)) := by
  simpa only [NNReal.coe_mk] using
    (hasSubgaussianMGF_sum_weightedSign_l2Sq x).measure_ge_le hε

/--
A finite family of deterministic Rademacher linear forms has a uniform tail
given by the sum of its individual sub-Gaussian tails.  This is the reusable
conditional union-bound layer for random-trace arguments: the coefficients
may depend on an already-fixed sample, while the fair signs remain random.
-/
theorem measure_exists_sum_weightedSign_ge_le_sum_exp_l2Sq
    {Hypothesis : Type*} [Fintype Hypothesis] [Fintype Feature]
    (coefficient : Hypothesis → Feature → ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    (FairCoin.productMeasure Feature).real {row | ∃ hypothesis,
      ε ≤ ∑ index : Feature, weightedSign (coefficient hypothesis) row index} ≤
      ∑ hypothesis : Hypothesis,
        Real.exp (-ε ^ 2 /
          (2 * AppliedModelingLib.FiniteDimensionalNorms.l2Sq (coefficient hypothesis))) := by
  classical
  let bad : Hypothesis → Set (Feature → Bool) := fun hypothesis => {row |
    ε ≤ ∑ index : Feature, weightedSign (coefficient hypothesis) row index}
  have hbad : ∀ hypothesis,
      (FairCoin.productMeasure Feature).real (bad hypothesis) ≤
        Real.exp (-ε ^ 2 /
          (2 * AppliedModelingLib.FiniteDimensionalNorms.l2Sq (coefficient hypothesis))) := by
    intro hypothesis
    exact measure_sum_weightedSign_ge_le_exp_l2Sq (coefficient hypothesis) hε
  have hbad_union : {row | ∃ hypothesis,
      ε ≤ ∑ index : Feature, weightedSign (coefficient hypothesis) row index} =
      ⋃ hypothesis ∈ (Finset.univ : Finset Hypothesis), bad hypothesis := by
    ext row
    simp [bad]
  rw [hbad_union]
  calc
    (FairCoin.productMeasure Feature).real
        (⋃ hypothesis ∈ (Finset.univ : Finset Hypothesis), bad hypothesis) ≤
        ∑ hypothesis ∈ (Finset.univ : Finset Hypothesis),
          (FairCoin.productMeasure Feature).real (bad hypothesis) := by
      simpa using (measureReal_biUnion_finset_le (μ := FairCoin.productMeasure Feature)
        (Finset.univ : Finset Hypothesis) bad)
    _ ≤ ∑ hypothesis : Hypothesis,
        Real.exp (-ε ^ 2 /
          (2 * AppliedModelingLib.FiniteDimensionalNorms.l2Sq (coefficient hypothesis))) := by
      apply Finset.sum_le_sum
      intro hypothesis _
      exact hbad hypothesis

/--
If every coefficient has absolute value at most one, a Rademacher linear form
has the cardinality-normalized tail `exp (-ε² / (2 |Feature|))`.  Giving every
coordinate the unit sub-Gaussian proxy keeps the statement valid even when a
particular coefficient vector is identically zero.
-/
theorem measure_sum_weightedSign_ge_le_exp_card_of_forall_abs_le_one
    [Fintype Feature] (x : Feature → ℝ) (hbound : ∀ index, |x index| ≤ 1)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (FairCoin.productMeasure Feature).real
        {row | ε ≤ ∑ index : Feature, weightedSign x row index} ≤
      Real.exp (-ε ^ 2 / (2 * (Fintype.card Feature : ℝ))) := by
  letI : IsProbabilityMeasure (FairCoin.productMeasure Feature) :=
    FairCoin.productMeasure_isProbabilityMeasure Feature
  have hsubgaussian : ∀ index : Feature,
      HasSubgaussianMGF (fun row => weightedSign x row index) (1 : NNReal)
        (FairCoin.productMeasure Feature) := by
    intro index
    convert
      (hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
        (measurable_of_finite (fun row : Feature → Bool => weightedSign x row index)).aemeasurable
        (ae_of_all _ fun row => by
          have hweighted := weightedSign_mem_Icc x row index
          exact ⟨(neg_le_neg (hbound index)).trans hweighted.1,
            hweighted.2.trans (hbound index)⟩)
        (integral_weightedSign_productMeasure Feature x index)) using 1
    all_goals norm_num
  simpa only [NNReal.coe_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] using
    (HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
      (weightedSign_iIndepFun x) (s := Finset.univ)
      (fun index _ => hsubgaussian index) hε)

/--
Uniform cardinality-normalized Rademacher tail for a finite family of
unit-bounded coefficient vectors.
-/
theorem measure_exists_sum_weightedSign_ge_le_card_mul_exp_card_of_forall_abs_le_one
    {Hypothesis : Type*} [Fintype Hypothesis] [Fintype Feature]
    (coefficient : Hypothesis → Feature → ℝ)
    (hbound : ∀ hypothesis index, |coefficient hypothesis index| ≤ 1)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (FairCoin.productMeasure Feature).real {row | ∃ hypothesis,
      ε ≤ ∑ index : Feature, weightedSign (coefficient hypothesis) row index} ≤
      (Fintype.card Hypothesis : ℝ) *
        Real.exp (-ε ^ 2 / (2 * (Fintype.card Feature : ℝ))) := by
  classical
  let bad : Hypothesis → Set (Feature → Bool) := fun hypothesis => {row |
    ε ≤ ∑ index : Feature, weightedSign (coefficient hypothesis) row index}
  have hbad : ∀ hypothesis,
      (FairCoin.productMeasure Feature).real (bad hypothesis) ≤
        Real.exp (-ε ^ 2 / (2 * (Fintype.card Feature : ℝ))) := by
    intro hypothesis
    exact measure_sum_weightedSign_ge_le_exp_card_of_forall_abs_le_one
      (coefficient hypothesis) (hbound hypothesis) hε
  have hbad_union : {row | ∃ hypothesis,
      ε ≤ ∑ index : Feature, weightedSign (coefficient hypothesis) row index} =
      ⋃ hypothesis ∈ (Finset.univ : Finset Hypothesis), bad hypothesis := by
    ext row
    simp [bad]
  rw [hbad_union]
  calc
    (FairCoin.productMeasure Feature).real
        (⋃ hypothesis ∈ (Finset.univ : Finset Hypothesis), bad hypothesis) ≤
        ∑ hypothesis ∈ (Finset.univ : Finset Hypothesis),
          (FairCoin.productMeasure Feature).real (bad hypothesis) := by
      simpa using (measureReal_biUnion_finset_le (μ := FairCoin.productMeasure Feature)
        (Finset.univ : Finset Hypothesis) bad)
    _ ≤ ∑ _hypothesis ∈ (Finset.univ : Finset Hypothesis),
        Real.exp (-ε ^ 2 / (2 * (Fintype.card Feature : ℝ))) := by
      apply Finset.sum_le_sum
      intro hypothesis _
      exact hbad hypothesis
    _ = (Fintype.card Hypothesis : ℝ) *
        Real.exp (-ε ^ 2 / (2 * (Fintype.card Feature : ℝ))) := by
      simp [mul_comm]

/-- Product signs from two distinct fair-product Boolean coordinates have mean zero. -/
theorem integral_pairSign_productMeasure
    [Fintype Feature] {i j : Feature} (hij : i ≠ j) :
    (∫ row : Feature → Bool,
        pairSign row i j ∂FairCoin.productMeasure Feature) = 0 := by
  have hcoord := boolCoord_iIndepFun Feature
  have hindep :
      (fun row : Feature → Bool => row i) ⟂ᵢ[FairCoin.productMeasure Feature]
        (fun row : Feature → Bool => row j) :=
    hcoord.indepFun hij
  have hX : AEMeasurable (fun row : Feature → Bool => row i)
      (FairCoin.productMeasure Feature) :=
    (measurable_pi_apply i).aemeasurable
  have hY : AEMeasurable (fun row : Feature → Bool => row j)
      (FairCoin.productMeasure Feature) :=
    (measurable_pi_apply j).aemeasurable
  have hf :
      AEStronglyMeasurable rademacherSign
        (Measure.map (fun row : Feature → Bool => row i)
          (FairCoin.productMeasure Feature)) :=
    (measurable_of_finite rademacherSign).aestronglyMeasurable
  have hg :
      AEStronglyMeasurable rademacherSign
        (Measure.map (fun row : Feature → Bool => row j)
          (FairCoin.productMeasure Feature)) :=
    (measurable_of_finite rademacherSign).aestronglyMeasurable
  have hmul :=
    hindep.integral_fun_comp_mul_comp hX hY hf hg
  rw [integral_rademacherSign_productMeasure Feature i,
    integral_rademacherSign_productMeasure Feature j] at hmul
  simpa [pairSign] using hmul

/-- The squared norm of a Rademacher row applied to a fixed vector is unbiased. -/
theorem integral_sq_sum_weightedSign_productMeasure
    [Fintype Feature] (x : Feature → ℝ) :
    (∫ row : Feature → Bool,
        (∑ i : Feature, weightedSign x row i) ^ 2
          ∂FairCoin.productMeasure Feature) =
      AppliedModelingLib.FiniteDimensionalNorms.l2Sq x := by
  classical
  let μ := FairCoin.productMeasure Feature
  letI : IsProbabilityMeasure μ := by
    simpa [μ] using FairCoin.productMeasure_isProbabilityMeasure Feature
  have hterm_integrable : ∀ i j : Feature,
      Integrable (fun row : Feature → Bool => weightedSign x row i * weightedSign x row j) μ := by
    intro i j
    apply Integrable.of_bound
    · exact (measurable_of_finite _).aestronglyMeasurable
    · filter_upwards [] with row
      rw [Real.norm_eq_abs, abs_mul, weightedSign, weightedSign,
        abs_mul, abs_mul, abs_rademacherSign, abs_rademacherSign]
  have hterm_integral : ∀ i j : Feature,
      (∫ row : Feature → Bool, weightedSign x row i * weightedSign x row j ∂μ) =
        if i = j then x i ^ 2 else 0 := by
    intro i j
    by_cases hij : i = j
    · subst j
      have hrewrite :
          (fun row : Feature → Bool => weightedSign x row i * weightedSign x row i) =
            fun _row => x i ^ 2 := by
              funext row
              change rademacherSign (row i) * x i *
                (rademacherSign (row i) * x i) = x i ^ 2
              calc
                rademacherSign (row i) * x i * (rademacherSign (row i) * x i) =
                    (rademacherSign (row i) * rademacherSign (row i)) * (x i * x i) := by
                      ring
                _ = x i ^ 2 := by simp [pow_two]
      rw [hrewrite]
      simp
    · have hrewrite :
          (fun row : Feature → Bool => weightedSign x row i * weightedSign x row j) =
            fun row => (x i * x j) * pairSign row i j := by
              funext row
              simp [weightedSign, pairSign]
              ring
      rw [hrewrite, integral_const_mul,
        integral_pairSign_productMeasure (Feature := Feature) hij]
      simp [hij]
  have hsum_integral :
      (∫ row : Feature → Bool,
          ∑ i : Feature, ∑ j : Feature,
            weightedSign x row i * weightedSign x row j ∂μ) =
        ∑ i : Feature, ∑ j : Feature,
          ∫ row : Feature → Bool, weightedSign x row i * weightedSign x row j ∂μ := by
    rw [integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro i _hi
      rw [integral_finset_sum]
      intro j _hj
      exact hterm_integrable i j
    · intro i _hi
      exact integrable_finset_sum _ fun j _hj => hterm_integrable i j
  calc
    (∫ row : Feature → Bool,
        (∑ i : Feature, weightedSign x row i) ^ 2 ∂μ) =
      ∫ row : Feature → Bool,
        ∑ i : Feature, ∑ j : Feature,
          weightedSign x row i * weightedSign x row j ∂μ := by
            apply integral_congr_ae
            filter_upwards [] with row
            rw [pow_two, Finset.sum_mul_sum]
    _ = ∑ i : Feature, ∑ j : Feature,
        ∫ row : Feature → Bool, weightedSign x row i * weightedSign x row j ∂μ := hsum_integral
    _ = ∑ i : Feature, x i ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.sum_eq_single i]
      · simp [hterm_integral]
      · intro j _hj hji
        have hij : i ≠ j := Ne.symm hji
        simp [hterm_integral, hij]
      · simp
    _ = AppliedModelingLib.FiniteDimensionalNorms.l2Sq x := rfl

/--
For a unit coefficient vector, truncating the squared Rademacher row energy
at `64` preserves at least `15/16` of its expectation.  This is the bounded
surrogate used for lower-tail concentration.
-/
theorem fifteen_sixteenths_le_integral_min_sq_sum_weightedSign
    [Fintype Feature] (x : Feature → ℝ)
    (hunit : AppliedModelingLib.FiniteDimensionalNorms.l2Sq x = 1) :
    15 / 16 ≤
      (∫ row : Feature → Bool,
        min ((∑ i : Feature, weightedSign x row i) ^ 2) 64
          ∂FairCoin.productMeasure Feature) := by
  letI : IsProbabilityMeasure (FairCoin.productMeasure Feature) :=
    FairCoin.productMeasure_isProbabilityMeasure Feature
  let c : NNReal := ⟨AppliedModelingLib.FiniteDimensionalNorms.l2Sq x,
    by
      rw [AppliedModelingLib.FiniteDimensionalNorms.l2Sq]
      exact Finset.sum_nonneg fun i _hi => sq_nonneg (x i)⟩
  have hc : c = 1 := by
    apply Subtype.ext
    dsimp [c]
    exact hunit
  have hsub : HasSubgaussianMGF
      (fun row : Feature → Bool => ∑ i : Feature, weightedSign x row i)
      1 (FairCoin.productMeasure Feature) := by
    simpa [c, hc] using hasSubgaussianMGF_sum_weightedSign_l2Sq x
  have hsecond :
      (∫ row : Feature → Bool,
        (∑ i : Feature, weightedSign x row i) ^ 2
          ∂FairCoin.productMeasure Feature) = 1 := by
    rw [integral_sq_sum_weightedSign_productMeasure]
    exact hunit
  exact
    AppliedModelingLib.Probability.integral_min_sq_sixty_four_ge_fifteen_sixteenths_of_hasSubgaussianMGF_one
      (FairCoin.productMeasure Feature) _ hsub hsecond

/-- The expected squared Rademacher linear form is unchanged when one row is sampled from a row product law. -/
theorem integral_sq_sum_weightedSign_rowsMeasure
    [Fintype Feature] (x : Feature → ℝ) (r : Coord) :
    (∫ ω : Coord → Feature → Bool,
        (∑ i : Feature, weightedSign x (ω r) i) ^ 2
          ∂rowsMeasure Feature Coord) =
      AppliedModelingLib.FiniteDimensionalNorms.l2Sq x := by
  let P : Coord → Measure (Feature → Bool) :=
    fun _ => FairCoin.productMeasure Feature
  let hP : ∀ r : Coord, IsProbabilityMeasure (P r) := by
    intro r
    simpa [P] using FairCoin.productMeasure_isProbabilityMeasure Feature
  let f : (Feature → Bool) → ℝ :=
    fun row => (∑ i : Feature, weightedSign x row i) ^ 2
  have hf : AEStronglyMeasurable f
      (Measure.map (fun ω : Coord → Feature → Bool => ω r)
        (rowsMeasure Feature Coord)) :=
    (measurable_of_finite f).aestronglyMeasurable
  calc
    (∫ ω : Coord → Feature → Bool,
        (∑ i : Feature, weightedSign x (ω r) i) ^ 2
        ∂rowsMeasure Feature Coord) =
        ∫ row : Feature → Bool, f row ∂Measure.map
          (fun ω : Coord → Feature → Bool => ω r)
          (rowsMeasure Feature Coord) := by
            exact (integral_map
              (μ := rowsMeasure Feature Coord)
              (φ := fun ω : Coord → Feature → Bool => ω r)
              (f := f) (measurable_pi_apply r).aemeasurable hf).symm
    _ = ∫ row : Feature → Bool, f row ∂FairCoin.productMeasure Feature := by
          rw [show
              Measure.map (fun ω : Coord → Feature → Bool => ω r)
                  (rowsMeasure Feature Coord) =
                FairCoin.productMeasure Feature from by
              simpa [rowsMeasure, P] using
                (@MeasureTheory.Measure.infinitePi_map_eval
                  (ι := Coord) (X := fun _ : Coord => Feature → Bool)
                  (mX := fun _ => by infer_instance) (μ := P) hP r)]
    _ = AppliedModelingLib.FiniteDimensionalNorms.l2Sq x := by
          exact integral_sq_sum_weightedSign_productMeasure x

/-- Each row-product sign has mean zero under the row-product matrix law. -/
theorem integral_pairSign_rowsMeasure
    [Fintype Feature] {i j : Feature} (hij : i ≠ j) (r : Coord) :
    (∫ ω : Coord → Feature → Bool,
        pairSign (ω r) i j ∂rowsMeasure Feature Coord) = 0 := by
  let P : Coord → Measure (Feature → Bool) :=
    fun _ => FairCoin.productMeasure Feature
  let hP : ∀ r : Coord, IsProbabilityMeasure (P r) := by
    intro r
    simpa [P] using FairCoin.productMeasure_isProbabilityMeasure Feature
  let f : (Feature → Bool) → ℝ := fun row => pairSign row i j
  have hf :
      AEStronglyMeasurable f
        (Measure.map (fun ω : Coord → Feature → Bool => ω r)
          (rowsMeasure Feature Coord)) :=
    (measurable_of_finite f).aestronglyMeasurable
  calc
    (∫ ω : Coord → Feature → Bool,
        pairSign (ω r) i j ∂rowsMeasure Feature Coord)
        = ∫ row : Feature → Bool, f row ∂Measure.map
          (fun ω : Coord → Feature → Bool => ω r)
          (rowsMeasure Feature Coord) := by
          exact (integral_map
            (μ := rowsMeasure Feature Coord)
            (φ := fun ω : Coord → Feature → Bool => ω r)
            (f := f) (measurable_pi_apply r).aemeasurable hf).symm
    _ = ∫ row : Feature → Bool, f row ∂FairCoin.productMeasure Feature := by
          rw [show
              Measure.map (fun ω : Coord → Feature → Bool => ω r)
                  (rowsMeasure Feature Coord) =
                FairCoin.productMeasure Feature from by
              simpa [rowsMeasure, P] using
                (@MeasureTheory.Measure.infinitePi_map_eval
                  (ι := Coord) (X := fun _ : Coord => Feature → Bool)
                  (mX := fun _ => by infer_instance) (μ := P) hP r)]
    _ = 0 := integral_pairSign_productMeasure (Feature := Feature) hij

/-- A scaled Rademacher matrix, with columns indexed by `Feature`. -/
noncomputable def scaledMatrix [Fintype Coord]
    (ω : Coord → Feature → Bool) : Feature → Coord → ℝ :=
  fun j r =>
    (Real.sqrt (Fintype.card Coord : ℝ))⁻¹ * rademacherSign (ω r j)

/-- A scaled Rademacher matrix preserves squared Euclidean norm in expectation. -/
theorem integral_l2Sq_measurement_scaledMatrix_rowsMeasure
    [Fintype Feature] [Fintype Coord]
    (hd : 0 < Fintype.card Coord) (x : Feature → ℝ) :
    (∫ ω : Coord → Feature → Bool,
        AppliedModelingLib.FiniteDimensionalNorms.l2Sq
          (measurement (scaledMatrix (Feature := Feature) (Coord := Coord) ω) x)
        ∂rowsMeasure Feature Coord) =
      AppliedModelingLib.FiniteDimensionalNorms.l2Sq x := by
  classical
  letI : IsProbabilityMeasure (rowsMeasure Feature Coord) :=
    rowsMeasure_isProbabilityMeasure Feature Coord
  let dR : ℝ := Fintype.card Coord
  have hdR_pos : 0 < dR := by
    dsimp [dR]
    exact_mod_cast hd
  have hsqrt_ne : Real.sqrt dR ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hdR_pos)
  have hrow_integral : ∀ r : Coord,
      (∫ ω : Coord → Feature → Bool,
          (∑ i : Feature, weightedSign x (ω r) i) ^ 2
          ∂rowsMeasure Feature Coord) =
        AppliedModelingLib.FiniteDimensionalNorms.l2Sq x :=
    integral_sq_sum_weightedSign_rowsMeasure x
  change (∫ ω : Coord → Feature → Bool,
      ∑ r : Coord,
        (measurement (scaledMatrix (Feature := Feature) (Coord := Coord) ω) x r) ^ 2
        ∂rowsMeasure Feature Coord) =
    ∑ i : Feature, x i ^ 2
  rw [integral_finset_sum]
  · have hscale : (Real.sqrt dR)⁻¹ ^ 2 = dR⁻¹ := by
      field_simp [hsqrt_ne]
      exact (Real.sq_sqrt (le_of_lt hdR_pos)).symm
    calc
      ∑ r : Coord,
          ∫ ω : Coord → Feature → Bool,
            (measurement (scaledMatrix (Feature := Feature) (Coord := Coord) ω) x r) ^ 2
              ∂rowsMeasure Feature Coord =
          ∑ r : Coord,
            (Real.sqrt dR)⁻¹ ^ 2 *
              ∫ ω : Coord → Feature → Bool,
                (∑ i : Feature, weightedSign x (ω r) i) ^ 2
                  ∂rowsMeasure Feature Coord := by
            apply Finset.sum_congr rfl
            intro r _hr
            have hpoint :
                (fun ω : Coord → Feature → Bool =>
                  measurement (scaledMatrix (Feature := Feature) (Coord := Coord) ω) x r ^ 2) =
                  fun ω => (Real.sqrt dR)⁻¹ ^ 2 *
                    (∑ i : Feature, weightedSign x (ω r) i) ^ 2 := by
              funext ω
              have hmeasurement :
                  measurement (scaledMatrix (Feature := Feature) (Coord := Coord) ω) x r =
                    (Real.sqrt dR)⁻¹ *
                      ∑ i : Feature, weightedSign x (ω r) i := by
                change (∑ i : Feature,
                    x i * ((Real.sqrt dR)⁻¹ * rademacherSign (ω r i))) = _
                calc
                  ∑ i : Feature,
                      x i * ((Real.sqrt dR)⁻¹ * rademacherSign (ω r i)) =
                      ∑ i : Feature,
                        (Real.sqrt dR)⁻¹ * weightedSign x (ω r) i := by
                          apply Finset.sum_congr rfl
                          intro i _hi
                          simp [weightedSign]
                          ring
                  _ = (Real.sqrt dR)⁻¹ *
                      ∑ i : Feature, weightedSign x (ω r) i := by
                        rw [Finset.mul_sum]
              rw [hmeasurement, mul_pow, hscale]
            rw [hpoint, integral_const_mul]
      _ = ∑ _r : Coord, (Real.sqrt dR)⁻¹ ^ 2 *
          AppliedModelingLib.FiniteDimensionalNorms.l2Sq x := by
            apply Finset.sum_congr rfl
            intro r _hr
            rw [hrow_integral r]
      _ = AppliedModelingLib.FiniteDimensionalNorms.l2Sq x := by
            rw [hscale]
            simp [dR]
            field_simp [show (Fintype.card Coord : ℝ) ≠ 0 by exact_mod_cast Nat.ne_of_gt hd]
  · intro r _hr
    exact Integrable.of_finite

/--
The squared value of a Rademacher linear form is bounded by the squared `l1`
norm of its coefficient vector.  This is the elementary boundedness input for
row-wise quadratic-energy concentration.
-/
theorem sq_sum_weightedSign_mem_Icc
    [Fintype Feature] (x : Feature → ℝ) (row : Feature → Bool) :
    (∑ i : Feature, weightedSign x row i) ^ 2 ∈
      Set.Icc 0 ((AppliedModelingLib.FiniteDimensionalNorms.l1 x) ^ 2) := by
  constructor
  · positivity
  · rw [sq_le_sq]
    simp only [abs_of_nonneg (AppliedModelingLib.FiniteDimensionalNorms.normL1_nonneg x)]
    calc
      |∑ i : Feature, weightedSign x row i| ≤
          ∑ i : Feature, |weightedSign x row i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = AppliedModelingLib.FiniteDimensionalNorms.l1 x := by
        simp [weightedSign, AppliedModelingLib.FiniteDimensionalNorms.normL1_eq_sum_abs]

/-- Squared fixed-vector row energies are independent across independently sampled rows. -/
theorem sq_sum_weightedSign_iIndepFun [Fintype Feature] (x : Feature → ℝ) :
    iIndepFun
      (fun r (ω : Coord → Feature → Bool) =>
        (∑ i : Feature, weightedSign x (ω r) i) ^ 2)
      (rowsMeasure Feature Coord) := by
  let P : Coord → Measure (Feature → Bool) :=
    fun _ => FairCoin.productMeasure Feature
  let hP : ∀ r : Coord, IsProbabilityMeasure (P r) := by
    intro r
    simpa [P] using FairCoin.productMeasure_isProbabilityMeasure Feature
  have hrow :
      iIndepFun (fun r (ω : Coord → Feature → Bool) => ω r)
        (Measure.infinitePi P) := by
    exact
      @ProbabilityTheory.iIndepFun_infinitePi
        (ι := Coord) (𝓧 := fun _ : Coord => Feature → Bool)
        (m𝓧 := fun _ => by infer_instance)
        (Ω := fun _ : Coord => Feature → Bool)
        (mΩ := fun _ => by infer_instance)
        (P := P) hP (X := fun _ : Coord => id)
        (mX := fun _ => measurable_id)
  simpa [rowsMeasure, P] using hrow.comp
    (fun _ row => (∑ i : Feature, weightedSign x row i) ^ 2)
    (fun _ => measurable_of_finite _)

/-- Truncated squared row energies remain independent across sampled rows. -/
theorem min_sq_sum_weightedSign_iIndepFun [Fintype Feature] (x : Feature → ℝ) :
    iIndepFun
      (fun r (omega : Coord → Feature → Bool) =>
        min ((∑ i : Feature, weightedSign x (omega r) i) ^ 2) 64)
      (rowsMeasure Feature Coord) := by
  exact (sq_sum_weightedSign_iIndepFun (Feature := Feature) (Coord := Coord) x).comp
    (fun _ z => min z 64) (fun _ => measurable_id.min measurable_const)

/-- Each sampled row has the same truncated-energy lower expectation bound. -/
theorem fifteen_sixteenths_le_integral_min_sq_sum_weightedSign_rowsMeasure
    [Fintype Feature] (x : Feature → ℝ)
    (hunit : AppliedModelingLib.FiniteDimensionalNorms.l2Sq x = 1) (r : Coord) :
    15 / 16 ≤
      (∫ omega,
        min ((∑ i : Feature, weightedSign x (omega r) i) ^ 2) 64
          ∂rowsMeasure Feature Coord) := by
  let g : (Feature → Bool) → ℝ := fun row =>
    min ((∑ i : Feature, weightedSign x row i) ^ 2) 64
  change 15 / 16 ≤ ∫ omega, g (omega r) ∂rowsMeasure Feature Coord
  rw [integral_comp_row_rowsMeasure (Feature := Feature) (Coord := Coord) r g]
  exact fifteen_sixteenths_le_integral_min_sq_sum_weightedSign x hunit

/--
Upper concentration for the empirical squared energy of a unit Rademacher
linear form.  This is the independent-row consequence of the local centered
square MGF bound, with an explicit dimension-free quadratic exponent.
-/
theorem measure_card_mul_ge_sum_centered_sq_sum_weightedSign_le_exp
    [Fintype Feature] [Fintype Coord]
    (x : Feature → ℝ)
    (hunit : AppliedModelingLib.FiniteDimensionalNorms.l2Sq x = 1)
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) (hepsilon_four : epsilon ≤ 4) :
    (rowsMeasure Feature Coord).real
        {omega | (Fintype.card Coord : ℝ) * epsilon ≤
          ∑ r : Coord, ((∑ i : Feature, weightedSign x (omega r) i) ^ 2 - 1)} ≤
      Real.exp (-3 * (Fintype.card Coord : ℝ) * epsilon ^ 2 / 64) := by
  letI : IsProbabilityMeasure (rowsMeasure Feature Coord) :=
    rowsMeasure_isProbabilityMeasure Feature Coord
  let t : ℝ := epsilon / 16
  have ht : 0 ≤ t := by
    dsimp [t]
    positivity
  have ht_quarter : t ≤ 1 / 4 := by
    dsimp [t]
    linarith
  let Y : Coord → (Coord → Feature → Bool) → ℝ := fun r omega =>
    (∑ i : Feature, weightedSign x (omega r) i) ^ 2 - 1
  have h_indep : iIndepFun Y (rowsMeasure Feature Coord) := by
    exact (sq_sum_weightedSign_iIndepFun (Feature := Feature) (Coord := Coord) x).comp
      (fun _ z => z - 1) (fun _ => measurable_id.sub measurable_const)
  have h_meas : ∀ r, Measurable (Y r) := fun _ => measurable_of_finite _
  have h_int : ∀ r ∈ Finset.univ,
      Integrable (fun omega => Real.exp (t * Y r omega)) (rowsMeasure Feature Coord) := by
    intro r _
    exact Integrable.of_finite
  have h_mgf : ∀ r ∈ Finset.univ,
      mgf (Y r) (rowsMeasure Feature Coord) t ≤ Real.exp (4 * t ^ 2) := by
    intro r _
    let g : (Feature → Bool) → ℝ := fun row =>
      Real.exp (t * ((∑ i : Feature, weightedSign x row i) ^ 2 - 1))
    change (∫ omega, Real.exp (t * ((∑ i : Feature,
      weightedSign x (omega r) i) ^ 2 - 1)) ∂rowsMeasure Feature Coord) ≤ _
    change (∫ omega, g (omega r) ∂rowsMeasure Feature Coord) ≤ _
    rw [integral_comp_row_rowsMeasure (Feature := Feature) (Coord := Coord) r g]
    exact integral_exp_mul_centered_sq_sum_weightedSign_le_exp_four_mul_sq
      x hunit t ht ht_quarter
  have htail := measure_sum_ge_le_exp_of_iIndepFun_mgf_le
    (μ := rowsMeasure Feature Coord) h_indep h_meas Finset.univ t
    ((Fintype.card Coord : ℝ) * epsilon) (4 * t ^ 2) ht h_int h_mgf
  change (rowsMeasure Feature Coord).real
      {omega | (Fintype.card Coord : ℝ) * epsilon ≤ ∑ r ∈ Finset.univ, Y r omega} ≤ _
  refine htail.trans_eq ?_
  dsimp [t]
  ring_nf

/--
Pointwise energy identity for a scaled Rademacher measurement matrix.  It
turns the squared `l2` norm of the measurement into the empirical average of
the independently sampled row energies.
-/
theorem l2Sq_measurement_scaledMatrix_eq_inv_card_mul_sum_sq_weightedSign
    [Fintype Feature] [Fintype Coord]
    (hd : 0 < Fintype.card Coord) (omega : Coord → Feature → Bool)
    (x : Feature → ℝ) :
    AppliedModelingLib.FiniteDimensionalNorms.l2Sq
      (measurement (scaledMatrix (Feature := Feature) (Coord := Coord) omega) x) =
      (Fintype.card Coord : ℝ)⁻¹ *
        ∑ r : Coord, (∑ i : Feature, weightedSign x (omega r) i) ^ 2 := by
  let dR : ℝ := Fintype.card Coord
  have hdR_pos : 0 < dR := by
    dsimp [dR]
    exact_mod_cast hd
  have hsqrt_ne : Real.sqrt dR ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hdR_pos)
  have hscale : (Real.sqrt dR)⁻¹ ^ 2 = dR⁻¹ := by
    field_simp [hsqrt_ne]
    exact (Real.sq_sqrt (le_of_lt hdR_pos)).symm
  change (∑ r : Coord,
      (measurement (scaledMatrix (Feature := Feature) (Coord := Coord) omega) x r) ^ 2) = _
  have hrow : ∀ r : Coord,
      measurement (scaledMatrix (Feature := Feature) (Coord := Coord) omega) x r =
        (Real.sqrt dR)⁻¹ * ∑ i : Feature, weightedSign x (omega r) i := by
    intro r
    change (∑ i : Feature,
        x i * ((Real.sqrt dR)⁻¹ * rademacherSign (omega r i))) = _
    calc
      ∑ i : Feature,
          x i * ((Real.sqrt dR)⁻¹ * rademacherSign (omega r i)) =
          ∑ i : Feature,
            (Real.sqrt dR)⁻¹ * weightedSign x (omega r) i := by
              apply Finset.sum_congr rfl
              intro i _hi
              simp [weightedSign]
              ring
      _ = (Real.sqrt dR)⁻¹ * ∑ i : Feature, weightedSign x (omega r) i := by
            rw [Finset.mul_sum]
  calc
    ∑ r : Coord,
        (measurement (scaledMatrix (Feature := Feature) (Coord := Coord) omega) x r) ^ 2 =
        ∑ r : Coord,
          (Real.sqrt dR)⁻¹ ^ 2 *
            (∑ i : Feature, weightedSign x (omega r) i) ^ 2 := by
          apply Finset.sum_congr rfl
          intro r _hr
          rw [hrow r, mul_pow]
    _ = dR⁻¹ * ∑ r : Coord,
          (∑ i : Feature, weightedSign x (omega r) i) ^ 2 := by
          rw [hscale, Finset.mul_sum]
    _ = _ := by simp [dR]

/--
The upper fixed-vector energy tail for a unit Rademacher measurement.  Its
exponent is linear in the number of rows and quadratic in the deviation,
without an `l1`-width dependence.
-/
theorem measure_l2Sq_measurement_scaledMatrix_sub_one_ge_le_exp_unit
    [Fintype Feature] [Fintype Coord]
    (hd : 0 < Fintype.card Coord) (x : Feature → ℝ)
    (hunit : AppliedModelingLib.FiniteDimensionalNorms.l2Sq x = 1)
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) (hepsilon_four : epsilon ≤ 4) :
    (rowsMeasure Feature Coord).real
        {omega | epsilon ≤
          AppliedModelingLib.FiniteDimensionalNorms.l2Sq
            (measurement (scaledMatrix (Feature := Feature) (Coord := Coord) omega) x) - 1} ≤
      Real.exp (-3 * (Fintype.card Coord : ℝ) * epsilon ^ 2 / 64) := by
  letI : IsProbabilityMeasure (rowsMeasure Feature Coord) :=
    rowsMeasure_isProbabilityMeasure Feature Coord
  have hdR : 0 < (Fintype.card Coord : ℝ) := by exact_mod_cast hd
  have htail := measure_card_mul_ge_sum_centered_sq_sum_weightedSign_le_exp
    (Feature := Feature) (Coord := Coord) x hunit epsilon hepsilon hepsilon_four
  refine le_trans ?_ htail
  refine measureReal_mono (μ := rowsMeasure Feature Coord) ?_ (measure_ne_top _ _)
  intro omega homega
  change epsilon ≤ AppliedModelingLib.FiniteDimensionalNorms.l2Sq
    (measurement (scaledMatrix (Feature := Feature) (Coord := Coord) omega) x) - 1 at homega
  have henergy := l2Sq_measurement_scaledMatrix_eq_inv_card_mul_sum_sq_weightedSign
    (Feature := Feature) (Coord := Coord) hd omega x
  rw [henergy] at homega
  have hfactor :
      (Fintype.card Coord : ℝ) *
          ((Fintype.card Coord : ℝ)⁻¹ *
            ∑ r : Coord, (∑ i : Feature, weightedSign x (omega r) i) ^ 2 - 1) =
        ∑ r : Coord, ((∑ i : Feature, weightedSign x (omega r) i) ^ 2 - 1) := by
    field_simp [hdR.ne']
    simp
  change (Fintype.card Coord : ℝ) * epsilon ≤
    ∑ r : Coord, ((∑ i : Feature, weightedSign x (omega r) i) ^ 2 - 1)
  rw [← hfactor]
  exact mul_le_mul_of_nonneg_left homega hdR.le

/--
Lower concentration at deviation `1/8` for the empirical energy of a unit
Rademacher linear form.  The proof truncates row energies before applying the
bounded independent-sum inequality, so it does not require a fourth moment.
-/
theorem measure_sum_sq_sum_weightedSign_le_seven_eighths_card_le_exp
    [Fintype Feature] [Fintype Coord]
    (x : Feature → ℝ)
    (hunit : AppliedModelingLib.FiniteDimensionalNorms.l2Sq x = 1) :
    (rowsMeasure Feature Coord).real
        {omega | ∑ r : Coord, (∑ i : Feature, weightedSign x (omega r) i) ^ 2 ≤
          (7 / 8 : ℝ) * (Fintype.card Coord : ℝ)} ≤
      Real.exp (-(Fintype.card Coord : ℝ) / 524288) := by
  letI : IsProbabilityMeasure (rowsMeasure Feature Coord) :=
    rowsMeasure_isProbabilityMeasure Feature Coord
  let T : Coord → (Coord → Feature → Bool) → ℝ := fun r omega =>
    min ((∑ i : Feature, weightedSign x (omega r) i) ^ 2) 64
  have h_indep : iIndepFun T (rowsMeasure Feature Coord) :=
    min_sq_sum_weightedSign_iIndepFun (Feature := Feature) (Coord := Coord) x
  have h_indep_neg : iIndepFun (fun r omega => -T r omega)
      (rowsMeasure Feature Coord) :=
    h_indep.comp (fun _ z => -z) (fun _ => measurable_id.neg)
  have htail := AppliedModelingLib.measure_sum_centered_bounded_ge_le_exp_of_iIndepFun
    (μ := rowsMeasure Feature Coord) (X := fun r omega => -T r omega)
    h_indep_neg (s := Finset.univ) (a := (-64 : ℝ)) (b := 0)
    (ε := (Fintype.card Coord : ℝ) / 16) ?_ ?_ (by positivity)
  · have hsub :
      {omega | ∑ r : Coord, (∑ i : Feature, weightedSign x (omega r) i) ^ 2 ≤
          (7 / 8 : ℝ) * (Fintype.card Coord : ℝ)} ⊆
        {omega | (Fintype.card Coord : ℝ) / 16 ≤
          ∑ r : Coord, (-T r omega - ∫ z, -T r z ∂rowsMeasure Feature Coord)} := by
      intro omega homega
      have hsumT :
          (∑ r : Coord, T r omega) ≤ (7 / 8 : ℝ) * (Fintype.card Coord : ℝ) := by
        calc
          (∑ r : Coord, T r omega) ≤
              ∑ r : Coord, (∑ i : Feature, weightedSign x (omega r) i) ^ 2 := by
                apply Finset.sum_le_sum
                intro r _hr
                exact min_le_left _ _
          _ ≤ _ := homega
      have hmean : ∀ r : Coord, 15 / 16 ≤ ∫ omega, T r omega ∂rowsMeasure Feature Coord := by
        intro r
        exact fifteen_sixteenths_le_integral_min_sq_sum_weightedSign_rowsMeasure
          (Feature := Feature) (Coord := Coord) x hunit r
      have hmean_sum :
          (Fintype.card Coord : ℝ) * (15 / 16 : ℝ) ≤
            ∑ r : Coord, ∫ omega, T r omega ∂rowsMeasure Feature Coord := by
        calc
          (Fintype.card Coord : ℝ) * (15 / 16 : ℝ) =
              ∑ _r : Coord, (15 / 16 : ℝ) := by simp
          _ ≤ _ := by
              apply Finset.sum_le_sum
              intro r _hr
              exact hmean r
      have hcenter :
          (∑ r : Coord,
              (-T r omega - ∫ z, -T r z ∂rowsMeasure Feature Coord)) =
            (∑ r : Coord, ∫ z, T r z ∂rowsMeasure Feature Coord) -
              ∑ r : Coord, T r omega := by
        rw [Finset.sum_sub_distrib]
        simp_rw [integral_neg]
        rw [Finset.sum_neg_distrib, Finset.sum_neg_distrib]
        ring
      change (Fintype.card Coord : ℝ) / 16 ≤
        ∑ r ∈ Finset.univ,
          (-T r omega - ∫ z, -T r z ∂rowsMeasure Feature Coord)
      rw [hcenter]
      nlinarith
    refine (measureReal_mono (μ := rowsMeasure Feature Coord) hsub (measure_ne_top _ _)).trans ?_
    refine htail.trans_eq ?_
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    by_cases hcard : Fintype.card Coord = 0
    · simp [hcard]
    · have hd : (Fintype.card Coord : ℝ) ≠ 0 := by exact_mod_cast hcard
      congr 1
      norm_num
      field_simp [hd]
      ring
  · intro r _hr
    exact (measurable_of_finite _).aemeasurable
  · intro r _hr
    filter_upwards [] with omega
    have hnonneg : 0 ≤ T r omega := by
      exact le_min (sq_nonneg _) (by norm_num)
    have hle : T r omega ≤ 64 := min_le_right _ _
    exact ⟨by linarith, by linarith⟩

/--
Lower concentration at deviation `1/8` for a unit scaled Rademacher
measurement.  The exponent is linear in the number of rows and has no
coefficient-width dependence.
-/
theorem measure_one_sub_l2Sq_measurement_scaledMatrix_ge_one_eighth_le_exp_unit
    [Fintype Feature] [Fintype Coord]
    (hd : 0 < Fintype.card Coord) (x : Feature → ℝ)
    (hunit : AppliedModelingLib.FiniteDimensionalNorms.l2Sq x = 1) :
    (rowsMeasure Feature Coord).real
        {omega | (1 / 8 : ℝ) ≤ 1 -
          AppliedModelingLib.FiniteDimensionalNorms.l2Sq
            (measurement (scaledMatrix (Feature := Feature) (Coord := Coord) omega) x)} ≤
      Real.exp (-(Fintype.card Coord : ℝ) / 524288) := by
  letI : IsProbabilityMeasure (rowsMeasure Feature Coord) :=
    rowsMeasure_isProbabilityMeasure Feature Coord
  have hdR : 0 < (Fintype.card Coord : ℝ) := by exact_mod_cast hd
  have htail := measure_sum_sq_sum_weightedSign_le_seven_eighths_card_le_exp
    (Feature := Feature) (Coord := Coord) x hunit
  refine (measureReal_mono (μ := rowsMeasure Feature Coord) ?_ (measure_ne_top _ _)).trans htail
  intro omega homega
  change (1 / 8 : ℝ) ≤ 1 -
    AppliedModelingLib.FiniteDimensionalNorms.l2Sq
      (measurement (scaledMatrix (Feature := Feature) (Coord := Coord) omega) x) at homega
  have henergy := l2Sq_measurement_scaledMatrix_eq_inv_card_mul_sum_sq_weightedSign
    (Feature := Feature) (Coord := Coord) hd omega x
  rw [henergy] at homega
  have hbound :
      (Fintype.card Coord : ℝ)⁻¹ *
        ∑ r : Coord, (∑ i : Feature, weightedSign x (omega r) i) ^ 2 ≤ 7 / 8 := by
    linarith
  calc
    ∑ r : Coord, (∑ i : Feature, weightedSign x (omega r) i) ^ 2 =
        (Fintype.card Coord : ℝ) *
          ((Fintype.card Coord : ℝ)⁻¹ *
            ∑ r : Coord, (∑ i : Feature, weightedSign x (omega r) i) ^ 2) := by
              field_simp [hdR.ne']
    _ ≤ (Fintype.card Coord : ℝ) * (7 / 8) := by
              gcongr
    _ = (7 / 8 : ℝ) * (Fintype.card Coord : ℝ) := by ring

/--
Fixed-support restricted-isometry failure for a scaled Rademacher matrix.
The proof combines sharp unit-vector concentration, a finite Euclidean net,
and the deterministic Gram-operator lifting.  The bound is intentionally
stated per support so it can be combined with any finite support-family count.
-/
theorem measure_not_restrictedIsometryOnSupport_scaledMatrix_three_eighths_le
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    (hd : 0 < Fintype.card Coord) (S : Finset Feature) :
    measureProb (rowsMeasure Feature Coord)
      (fun omega => ¬ RestrictedIsometryOnSupport
        (scaledMatrix (Feature := Feature) (Coord := Coord) omega) S (3 / 8 : ℝ)) ≤
      2 * ((9 ^ S.card : ℕ) : ℝ) *
        Real.exp (-(Fintype.card Coord : ℝ) / 524288) := by
  obtain ⟨N, hNcard, hNunit, hnet⟩ :
      ∃ N : Finset (EuclideanSpace ℝ {i : Feature // i ∈ S}),
        N.card ≤ 9 ^ Fintype.card {i : Feature // i ∈ S} ∧
        (∀ y ∈ N, ‖y‖ = 1) ∧
        ∀ v, ‖v‖ = 1 → ∃ y ∈ N, ‖v - y‖ < (5 : ℝ) / 16 := by
    by_cases hS : S.Nonempty
    · letI : Nonempty {i : Feature // i ∈ S} := Finset.nonempty_coe_sort.mpr hS
      simpa [finrank_euclideanSpace] using
        (AppliedModelingLib.Math.EuclideanNets.exists_finset_unit_sphere_five_sixteenths_net
          (E := EuclideanSpace ℝ {i : Feature // i ∈ S}))
    · have hSempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
      subst S
      refine ⟨∅, by simp, by simp, ?_⟩
      intro v hv
      have hvzero : v = 0 := Subsingleton.elim _ _
      rw [hvzero] at hv
      simp at hv
  have hNcard' : N.card ≤ 9 ^ S.card := by
    simpa [finrank_euclideanSpace, Fintype.card_coe] using hNcard
  letI : IsProbabilityMeasure (rowsMeasure Feature Coord) :=
    rowsMeasure_isProbabilityMeasure Feature Coord
  let bad : (Coord → Feature → Bool) → Prop := fun omega =>
    ¬ RestrictedIsometryOnSupport
      (scaledMatrix (Feature := Feature) (Coord := Coord) omega) S (3 / 8 : ℝ)
  let pointBad : (EuclideanSpace ℝ {i : Feature // i ∈ S}) →
      (Coord → Feature → Bool) → Prop := fun y omega =>
    (1 / 8 : ℝ) ≤ |AppliedModelingLib.FiniteDimensionalNorms.l2Sq
      (measurement (scaledMatrix (Feature := Feature) (Coord := Coord) omega)
        (extendByZero S y.ofLp)) - 1|
  have hbad_subset : {omega | bad omega} ⊆
      {omega | ∃ y ∈ N, pointBad y omega} := by
    intro omega homega
    by_contra hnot
    apply homega
    apply restrictedIsometryOnSupport_three_eighths_of_unit_sphere_net
      (scaledMatrix (Feature := Feature) (Coord := Coord) omega) S N hnet hNunit
    intro y hy
    have hnotbad : ¬ pointBad y omega := by
      intro hpoint
      exact hnot ⟨y, hy, hpoint⟩
    dsimp [pointBad] at hnotbad
    exact (lt_of_not_ge hnotbad).le
  have hpoint : ∀ y ∈ N,
      measureProb (rowsMeasure Feature Coord) (pointBad y) ≤
        2 * Real.exp (-(Fintype.card Coord : ℝ) / 524288) := by
    intro y hy
    let upper : Set (Coord → Feature → Bool) := {omega | (1 / 8 : ℝ) ≤
      AppliedModelingLib.FiniteDimensionalNorms.l2Sq
        (measurement (scaledMatrix (Feature := Feature) (Coord := Coord) omega)
          (extendByZero S y.ofLp)) - 1}
    let lower : Set (Coord → Feature → Bool) := {omega | (1 / 8 : ℝ) ≤ 1 -
      AppliedModelingLib.FiniteDimensionalNorms.l2Sq
        (measurement (scaledMatrix (Feature := Feature) (Coord := Coord) omega)
          (extendByZero S y.ofLp))}
    have hunit : AppliedModelingLib.FiniteDimensionalNorms.l2Sq (extendByZero S y.ofLp) = 1 := by
      calc
        AppliedModelingLib.FiniteDimensionalNorms.l2Sq (extendByZero S y.ofLp) =
            AppliedModelingLib.FiniteDimensionalNorms.l2Sq y.ofLp := l2Sq_extendByZero S y.ofLp
        _ = ‖y‖ ^ 2 := (norm_sq_eq_l2Sq_ofEuclideanSpace y).symm
        _ = 1 := by rw [hNunit y hy]; norm_num
    have hupper := measure_l2Sq_measurement_scaledMatrix_sub_one_ge_le_exp_unit
      (Feature := Feature) (Coord := Coord) hd (extendByZero S y.ofLp) hunit
      (1 / 8 : ℝ) (by norm_num) (by norm_num)
    have hlower := measure_one_sub_l2Sq_measurement_scaledMatrix_ge_one_eighth_le_exp_unit
      (Feature := Feature) (Coord := Coord) hd (extendByZero S y.ofLp) hunit
    have hsubset : {omega | pointBad y omega} ⊆ upper ∪ lower := by
      intro omega homega
      dsimp [pointBad, upper, lower] at homega ⊢
      by_cases hsign : 0 ≤ AppliedModelingLib.FiniteDimensionalNorms.l2Sq
          (measurement (scaledMatrix (Feature := Feature) (Coord := Coord) omega)
            (extendByZero S y.ofLp)) - 1
      · left
        simpa [abs_of_nonneg hsign] using homega
      · right
        have hsign' : AppliedModelingLib.FiniteDimensionalNorms.l2Sq
            (measurement (scaledMatrix (Feature := Feature) (Coord := Coord) omega)
              (extendByZero S y.ofLp)) - 1 < 0 := lt_of_not_ge hsign
        simpa [abs_of_neg hsign', neg_sub] using homega
    have hrate : Real.exp (-3 * (Fintype.card Coord : ℝ) * (1 / 8 : ℝ) ^ 2 / 64) ≤
        Real.exp (-(Fintype.card Coord : ℝ) / 524288) := by
      apply Real.exp_le_exp.mpr
      have hcard_nonneg : 0 ≤ (Fintype.card Coord : ℝ) := Nat.cast_nonneg _
      nlinarith
    calc
      measureProb (rowsMeasure Feature Coord) (pointBad y) ≤
          (rowsMeasure Feature Coord).real (upper ∪ lower) :=
        measureReal_mono hsubset (measure_ne_top _ _)
      _ ≤ (rowsMeasure Feature Coord).real upper +
          (rowsMeasure Feature Coord).real lower := measureReal_union_le _ _
      _ ≤ Real.exp (-3 * (Fintype.card Coord : ℝ) * (1 / 8 : ℝ) ^ 2 / 64) +
          Real.exp (-(Fintype.card Coord : ℝ) / 524288) := by
            gcongr
      _ ≤ 2 * Real.exp (-(Fintype.card Coord : ℝ) / 524288) := by linarith
  calc
    measureProb (rowsMeasure Feature Coord) bad ≤
        measureProb (rowsMeasure Feature Coord)
          (fun omega => ∃ y ∈ N, pointBad y omega) :=
      measureReal_mono hbad_subset (measure_ne_top _ _)
    _ ≤ ∑ y ∈ N, measureProb (rowsMeasure Feature Coord) (pointBad y) :=
      measureProb_biUnion_finset_le _ _ _
    _ ≤ ∑ _y ∈ N, 2 * Real.exp (-(Fintype.card Coord : ℝ) / 524288) := by
      exact Finset.sum_le_sum fun y hy => hpoint y hy
    _ = (N.card : ℝ) * (2 * Real.exp (-(Fintype.card Coord : ℝ) / 524288)) := by simp
    _ ≤ ((9 ^ S.card : ℕ) : ℝ) *
        (2 * Real.exp (-(Fintype.card Coord : ℝ) / 524288)) := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hNcard') (by positivity)
    _ = 2 * ((9 ^ S.card : ℕ) : ℝ) *
        Real.exp (-(Fintype.card Coord : ℝ) / 524288) := by ring

/--
Hoeffding concentration for the sum of squared fixed-vector Rademacher row
energies.  Its `l1`-dependent width is the bounded starting point for a later
subexponential refinement; no RIP-scale claim is encoded here.
-/
theorem measure_sum_centered_sq_sum_weightedSign_ge_le_exp
    [Fintype Feature] [Fintype Coord]
    (x : Feature → ℝ) {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) :
    (rowsMeasure Feature Coord).real
        {ω | epsilon ≤ ∑ r : Coord,
          ((∑ i : Feature, weightedSign x (ω r) i) ^ 2 -
            ∫ z, (∑ i : Feature, weightedSign x (z r) i) ^ 2
              ∂rowsMeasure Feature Coord)} ≤
      Real.exp (-epsilon ^ 2 /
        (2 * ((∑ _r : Coord,
          ((‖(AppliedModelingLib.FiniteDimensionalNorms.l1 x) ^ 2 - 0‖₊ / 2) ^ 2 : NNReal)) : ℝ))) := by
  letI : IsProbabilityMeasure (rowsMeasure Feature Coord) :=
    rowsMeasure_isProbabilityMeasure Feature Coord
  refine AppliedModelingLib.measure_sum_centered_bounded_ge_le_exp_of_iIndepFun
    (μ := rowsMeasure Feature Coord)
    (X := fun r (ω : Coord → Feature → Bool) =>
      (∑ i : Feature, weightedSign x (ω r) i) ^ 2)
    (sq_sum_weightedSign_iIndepFun (Feature := Feature) (Coord := Coord) x)
    (s := Finset.univ) (a := 0)
    (b := AppliedModelingLib.FiniteDimensionalNorms.l1 x ^ 2) ?_ ?_ hepsilon
  · intro r _hr
    exact (measurable_of_finite _).aemeasurable
  · intro r _hr
    exact ae_of_all _ fun omega => sq_sum_weightedSign_mem_Icc x (omega r)

/--
The preceding centered quadratic-energy tail with the expectation evaluated:
the row-energy sum deviates above its exact mean by at most the same
Hoeffding bound.
-/
theorem measure_sum_sq_sum_weightedSign_sub_card_mul_l2Sq_ge_le_exp
    [Fintype Feature] [Fintype Coord]
    (x : Feature → ℝ) {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) :
    (rowsMeasure Feature Coord).real
        {omega | epsilon ≤
          (∑ r : Coord, (∑ i : Feature, weightedSign x (omega r) i) ^ 2) -
            (Fintype.card Coord : ℝ) * AppliedModelingLib.FiniteDimensionalNorms.l2Sq x} ≤
      Real.exp (-epsilon ^ 2 /
        (2 * ((∑ _r : Coord,
          ((‖(AppliedModelingLib.FiniteDimensionalNorms.l1 x) ^ 2 - 0‖₊ / 2) ^ 2 : NNReal)) : ℝ))) := by
  letI : IsProbabilityMeasure (rowsMeasure Feature Coord) :=
    rowsMeasure_isProbabilityMeasure Feature Coord
  have htail := measure_sum_centered_sq_sum_weightedSign_ge_le_exp
    (Feature := Feature) (Coord := Coord) x hepsilon
  refine le_trans ?_ htail
  refine measureReal_mono (μ := rowsMeasure Feature Coord) ?_
    (measure_ne_top _ _)
  intro omega homega
  have hcenter :
      (∑ r : Coord,
          ((∑ i : Feature, weightedSign x (omega r) i) ^ 2 -
            ∫ z, (∑ i : Feature, weightedSign x (z r) i) ^ 2
              ∂rowsMeasure Feature Coord)) =
        (∑ r : Coord, (∑ i : Feature, weightedSign x (omega r) i) ^ 2) -
          (Fintype.card Coord : ℝ) * AppliedModelingLib.FiniteDimensionalNorms.l2Sq x := by
    rw [Finset.sum_sub_distrib]
    simp_rw [integral_sq_sum_weightedSign_rowsMeasure]
    simp
  change epsilon ≤ ∑ r : Coord,
    ((∑ i : Feature, weightedSign x (omega r) i) ^ 2 -
      ∫ z, (∑ i : Feature, weightedSign x (z r) i) ^ 2
        ∂rowsMeasure Feature Coord)
  rw [hcenter]
  exact homega

/--
One-sided fixed-vector concentration for the quadratic energy of a scaled
Rademacher measurement.  This is a fully proved Hoeffding-scale estimate; its
`l1` width records exactly why a sharper subexponential square theorem is
needed for RIP-optimal dimensions.
-/
theorem measure_l2Sq_measurement_scaledMatrix_sub_l2Sq_ge_le_exp
    [Fintype Feature] [Fintype Coord]
    (hd : 0 < Fintype.card Coord) (x : Feature → ℝ)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) :
    (rowsMeasure Feature Coord).real
        {omega | epsilon ≤
          AppliedModelingLib.FiniteDimensionalNorms.l2Sq
            (measurement (scaledMatrix (Feature := Feature) (Coord := Coord) omega) x) -
              AppliedModelingLib.FiniteDimensionalNorms.l2Sq x} ≤
      Real.exp (-(((Fintype.card Coord : ℝ) * epsilon) ^ 2) /
        (2 * ((∑ _r : Coord,
          ((‖(AppliedModelingLib.FiniteDimensionalNorms.l1 x) ^ 2 - 0‖₊ / 2) ^ 2 : NNReal)) : ℝ))) := by
  letI : IsProbabilityMeasure (rowsMeasure Feature Coord) :=
    rowsMeasure_isProbabilityMeasure Feature Coord
  have hdR : 0 < (Fintype.card Coord : ℝ) := by exact_mod_cast hd
  have htail := measure_sum_sq_sum_weightedSign_sub_card_mul_l2Sq_ge_le_exp
    (Feature := Feature) (Coord := Coord) x
    (epsilon := (Fintype.card Coord : ℝ) * epsilon)
    (mul_nonneg (Nat.cast_nonneg _) hepsilon)
  refine le_trans ?_ htail
  refine measureReal_mono (μ := rowsMeasure Feature Coord) ?_
    (measure_ne_top _ _)
  intro omega homega
  have henergy :=
    l2Sq_measurement_scaledMatrix_eq_inv_card_mul_sum_sq_weightedSign
      (Feature := Feature) (Coord := Coord) hd omega x
  change epsilon ≤
    AppliedModelingLib.FiniteDimensionalNorms.l2Sq
      (measurement (scaledMatrix (Feature := Feature) (Coord := Coord) omega) x) -
        AppliedModelingLib.FiniteDimensionalNorms.l2Sq x at homega
  rw [henergy] at homega
  have hfactor :
      (Fintype.card Coord : ℝ) *
          ((Fintype.card Coord : ℝ)⁻¹ *
            ∑ r : Coord, (∑ i : Feature, weightedSign x (omega r) i) ^ 2 -
              AppliedModelingLib.FiniteDimensionalNorms.l2Sq x) =
        (∑ r : Coord, (∑ i : Feature, weightedSign x (omega r) i) ^ 2) -
          (Fintype.card Coord : ℝ) * AppliedModelingLib.FiniteDimensionalNorms.l2Sq x := by
    field_simp [hdR.ne']
  change (Fintype.card Coord : ℝ) * epsilon ≤
    (∑ r : Coord, (∑ i : Feature, weightedSign x (omega r) i) ^ 2) -
      (Fintype.card Coord : ℝ) * AppliedModelingLib.FiniteDimensionalNorms.l2Sq x
  rw [← hfactor]
  exact mul_le_mul_of_nonneg_left homega hdR.le

/--
The matching lower quadratic-energy tail for a scaled Rademacher measurement.
It is obtained by applying the same bounded concentration argument to negated
row energies.
-/
theorem measure_l2Sq_sub_l2Sq_measurement_scaledMatrix_ge_le_exp
    [Fintype Feature] [Fintype Coord]
    (hd : 0 < Fintype.card Coord) (x : Feature → ℝ)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) :
    (rowsMeasure Feature Coord).real
        {omega | epsilon ≤ AppliedModelingLib.FiniteDimensionalNorms.l2Sq x -
          AppliedModelingLib.FiniteDimensionalNorms.l2Sq
            (measurement (scaledMatrix (Feature := Feature) (Coord := Coord) omega) x)} ≤
      Real.exp (-(((Fintype.card Coord : ℝ) * epsilon) ^ 2) /
        (2 * ((∑ _r : Coord,
          ((‖0 - (-(AppliedModelingLib.FiniteDimensionalNorms.l1 x ^ 2))‖₊ / 2) ^ 2 : NNReal)) : ℝ))) := by
  letI : IsProbabilityMeasure (rowsMeasure Feature Coord) :=
    rowsMeasure_isProbabilityMeasure Feature Coord
  have hdR : 0 < (Fintype.card Coord : ℝ) := by exact_mod_cast hd
  have hindep :
      iIndepFun
        (fun r (omega : Coord → Feature → Bool) =>
          -((∑ i : Feature, weightedSign x (omega r) i) ^ 2))
        (rowsMeasure Feature Coord) := by
    exact (sq_sum_weightedSign_iIndepFun (Feature := Feature) (Coord := Coord) x).comp
      (fun _ z => -z) (fun _ => measurable_id.neg)
  have htail :
      (rowsMeasure Feature Coord).real
          {omega | (Fintype.card Coord : ℝ) * epsilon ≤ ∑ r : Coord,
            (-((∑ i : Feature, weightedSign x (omega r) i) ^ 2) -
              ∫ z, -((∑ i : Feature, weightedSign x (z r) i) ^ 2)
                ∂rowsMeasure Feature Coord)} ≤
        Real.exp (-(((Fintype.card Coord : ℝ) * epsilon) ^ 2) /
          (2 * ((∑ _r : Coord,
            ((‖0 - (-(AppliedModelingLib.FiniteDimensionalNorms.l1 x ^ 2))‖₊ / 2) ^ 2 : NNReal)) : ℝ))) := by
    refine AppliedModelingLib.measure_sum_centered_bounded_ge_le_exp_of_iIndepFun
      (μ := rowsMeasure Feature Coord)
      (X := fun r (omega : Coord → Feature → Bool) =>
        -((∑ i : Feature, weightedSign x (omega r) i) ^ 2))
      hindep (s := Finset.univ)
      (a := -(AppliedModelingLib.FiniteDimensionalNorms.l1 x ^ 2)) (b := 0) ?_ ?_
      (mul_nonneg (Nat.cast_nonneg _) hepsilon)
    · intro r _hr
      exact (measurable_of_finite _).aemeasurable
    · intro r _hr
      filter_upwards [] with omega
      have h := sq_sum_weightedSign_mem_Icc x (omega r)
      exact ⟨by linarith [h.2], by linarith [h.1]⟩
  refine le_trans ?_ htail
  refine measureReal_mono (μ := rowsMeasure Feature Coord) ?_
    (measure_ne_top _ _)
  intro omega homega
  have henergy :=
    l2Sq_measurement_scaledMatrix_eq_inv_card_mul_sum_sq_weightedSign
      (Feature := Feature) (Coord := Coord) hd omega x
  change epsilon ≤ AppliedModelingLib.FiniteDimensionalNorms.l2Sq x -
    AppliedModelingLib.FiniteDimensionalNorms.l2Sq
      (measurement (scaledMatrix (Feature := Feature) (Coord := Coord) omega) x) at homega
  rw [henergy] at homega
  have hcenter :
      (∑ r : Coord,
          (-((∑ i : Feature, weightedSign x (omega r) i) ^ 2) -
            ∫ z, -((∑ i : Feature, weightedSign x (z r) i) ^ 2)
              ∂rowsMeasure Feature Coord)) =
        (Fintype.card Coord : ℝ) * AppliedModelingLib.FiniteDimensionalNorms.l2Sq x -
          (∑ r : Coord, (∑ i : Feature, weightedSign x (omega r) i) ^ 2) := by
    rw [Finset.sum_sub_distrib]
    simp_rw [integral_neg, integral_sq_sum_weightedSign_rowsMeasure]
    simp
    ring
  change (Fintype.card Coord : ℝ) * epsilon ≤ ∑ r : Coord,
    (-((∑ i : Feature, weightedSign x (omega r) i) ^ 2) -
      ∫ z, -((∑ i : Feature, weightedSign x (z r) i) ^ 2)
        ∂rowsMeasure Feature Coord)
  rw [hcenter]
  have hfactor :
      (Fintype.card Coord : ℝ) *
        (AppliedModelingLib.FiniteDimensionalNorms.l2Sq x -
          (Fintype.card Coord : ℝ)⁻¹ *
            ∑ r : Coord, (∑ i : Feature, weightedSign x (omega r) i) ^ 2) =
        (Fintype.card Coord : ℝ) * AppliedModelingLib.FiniteDimensionalNorms.l2Sq x -
          ∑ r : Coord, (∑ i : Feature, weightedSign x (omega r) i) ^ 2 := by
    field_simp [hdR.ne']
  rw [← hfactor]
  exact mul_le_mul_of_nonneg_left homega hdR.le

/--
Two-sided fixed-vector energy concentration for a scaled Rademacher matrix.
This combines the proved upper and lower Hoeffding tails.  The explicit
`l1`-width makes this statement useful as a safe bounded baseline while
distinguishing it from the future RIP-optimal subexponential estimate.
-/
theorem measure_abs_l2Sq_measurement_scaledMatrix_sub_l2Sq_ge_le_two_mul_exp
    [Fintype Feature] [Fintype Coord]
    (hd : 0 < Fintype.card Coord) (x : Feature → ℝ)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) :
    (rowsMeasure Feature Coord).real
        {omega | epsilon ≤ abs (
          AppliedModelingLib.FiniteDimensionalNorms.l2Sq
            (measurement (scaledMatrix (Feature := Feature) (Coord := Coord) omega) x) -
              AppliedModelingLib.FiniteDimensionalNorms.l2Sq x)} ≤
      2 * Real.exp (-(((Fintype.card Coord : ℝ) * epsilon) ^ 2) /
        (2 * ((∑ _r : Coord,
          ((‖(AppliedModelingLib.FiniteDimensionalNorms.l1 x) ^ 2 - 0‖₊ / 2) ^ 2 : NNReal)) : ℝ))) := by
  letI : IsProbabilityMeasure (rowsMeasure Feature Coord) :=
    rowsMeasure_isProbabilityMeasure Feature Coord
  let upper : Set (Coord → Feature → Bool) :=
    {omega | epsilon ≤
      AppliedModelingLib.FiniteDimensionalNorms.l2Sq
        (measurement (scaledMatrix (Feature := Feature) (Coord := Coord) omega) x) -
          AppliedModelingLib.FiniteDimensionalNorms.l2Sq x}
  let lower : Set (Coord → Feature → Bool) :=
    {omega | epsilon ≤ AppliedModelingLib.FiniteDimensionalNorms.l2Sq x -
      AppliedModelingLib.FiniteDimensionalNorms.l2Sq
        (measurement (scaledMatrix (Feature := Feature) (Coord := Coord) omega) x)}
  let bad : Set (Coord → Feature → Bool) :=
    {omega | epsilon ≤ abs (
      AppliedModelingLib.FiniteDimensionalNorms.l2Sq
        (measurement (scaledMatrix (Feature := Feature) (Coord := Coord) omega) x) -
          AppliedModelingLib.FiniteDimensionalNorms.l2Sq x)}
  have hsubset : bad ⊆ upper ∪ lower := by
    intro omega homega
    dsimp [bad, upper, lower] at homega ⊢
    by_cases hsign : 0 ≤
        AppliedModelingLib.FiniteDimensionalNorms.l2Sq
          (measurement (scaledMatrix (Feature := Feature) (Coord := Coord) omega) x) -
            AppliedModelingLib.FiniteDimensionalNorms.l2Sq x
    · left
      simpa [abs_of_nonneg hsign] using homega
    · right
      have hsign' :
          AppliedModelingLib.FiniteDimensionalNorms.l2Sq
            (measurement (scaledMatrix (Feature := Feature) (Coord := Coord) omega) x) -
              AppliedModelingLib.FiniteDimensionalNorms.l2Sq x < 0 := lt_of_not_ge hsign
      simpa [abs_of_neg hsign', neg_sub] using homega
  have hupper := measure_l2Sq_measurement_scaledMatrix_sub_l2Sq_ge_le_exp
    (Feature := Feature) (Coord := Coord) hd x hepsilon
  have hlower := measure_l2Sq_sub_l2Sq_measurement_scaledMatrix_ge_le_exp
    (Feature := Feature) (Coord := Coord) hd x hepsilon
  have hlower' :
      (rowsMeasure Feature Coord).real lower ≤
        Real.exp (-(((Fintype.card Coord : ℝ) * epsilon) ^ 2) /
          (2 * ((∑ _r : Coord,
            ((‖(AppliedModelingLib.FiniteDimensionalNorms.l1 x) ^ 2 - 0‖₊ / 2) ^ 2 : NNReal)) : ℝ))) := by
    simpa [lower] using hlower
  have hupper' :
      (rowsMeasure Feature Coord).real upper ≤
        Real.exp (-(((Fintype.card Coord : ℝ) * epsilon) ^ 2) /
          (2 * ((∑ _r : Coord,
            ((‖(AppliedModelingLib.FiniteDimensionalNorms.l1 x) ^ 2 - 0‖₊ / 2) ^ 2 : NNReal)) : ℝ))) := by
    simpa [upper] using hupper
  calc
    (rowsMeasure Feature Coord).real bad ≤
        (rowsMeasure Feature Coord).real (upper ∪ lower) :=
      measureReal_mono (μ := rowsMeasure Feature Coord) hsubset (measure_ne_top _ _)
    _ ≤ (rowsMeasure Feature Coord).real upper +
          (rowsMeasure Feature Coord).real lower :=
      measureReal_union_le (μ := rowsMeasure Feature Coord) upper lower
    _ ≤ _ := by
      calc
        (rowsMeasure Feature Coord).real upper +
            (rowsMeasure Feature Coord).real lower ≤
            Real.exp (-(((Fintype.card Coord : ℝ) * epsilon) ^ 2) /
              (2 * ((∑ _r : Coord,
                ((‖(AppliedModelingLib.FiniteDimensionalNorms.l1 x) ^ 2 - 0‖₊ / 2) ^ 2 : NNReal)) : ℝ))) +
              Real.exp (-(((Fintype.card Coord : ℝ) * epsilon) ^ 2) /
                (2 * ((∑ _r : Coord,
                  ((‖(AppliedModelingLib.FiniteDimensionalNorms.l1 x) ^ 2 - 0‖₊ / 2) ^ 2 : NNReal)) : ℝ))) :=
          add_le_add hupper' hlower'
        _ = _ := by ring

/-- Every scaled Rademacher column has squared norm one when `Coord` is nonempty. -/
theorem inner_scaledMatrix_self [Fintype Coord]
    (hd : 0 < Fintype.card Coord) (ω : Coord → Feature → Bool)
    (i : Feature) :
    inner (scaledMatrix (Feature := Feature) (Coord := Coord) ω i)
      (scaledMatrix (Feature := Feature) (Coord := Coord) ω i) = 1 := by
  classical
  let dR : ℝ := Fintype.card Coord
  have hdR_pos : 0 < dR := by
    dsimp [dR]
    exact_mod_cast hd
  have hsqrt_sq : (Real.sqrt dR) ^ 2 = dR := by
    exact Real.sq_sqrt (le_of_lt hdR_pos)
  have hsqrt_ne : Real.sqrt dR ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.mpr hdR_pos)
  calc
    inner (scaledMatrix (Feature := Feature) (Coord := Coord) ω i)
        (scaledMatrix (Feature := Feature) (Coord := Coord) ω i)
        = ∑ r : Coord,
            ((Real.sqrt dR)⁻¹ * rademacherSign (ω r i)) *
              ((Real.sqrt dR)⁻¹ * rademacherSign (ω r i)) := by
          simp [AppliedModelingLib.Math.LinearCompressedSensing.inner, scaledMatrix, dR]
    _ = ∑ _r : Coord, (Real.sqrt dR)⁻¹ * (Real.sqrt dR)⁻¹ := by
          refine Finset.sum_congr rfl ?_
          intro r _hr
          simp [mul_left_comm, mul_comm]
    _ = dR * ((Real.sqrt dR)⁻¹ * (Real.sqrt dR)⁻¹) := by
          simp [dR]
    _ = (Real.sqrt dR * Real.sqrt dR) *
          ((Real.sqrt dR)⁻¹ * (Real.sqrt dR)⁻¹) := by
          rw [show Real.sqrt dR * Real.sqrt dR = dR from by
            simpa [pow_two] using hsqrt_sq]
    _ = 1 := by
          field_simp [hsqrt_ne]

/-- Off-diagonal inner products are scaled sums of independent product signs. -/
theorem inner_scaledMatrix_eq_inv_card_mul_sum_pairSign [Fintype Coord]
    (hd : 0 < Fintype.card Coord) (ω : Coord → Feature → Bool)
    (i j : Feature) :
    inner (scaledMatrix (Feature := Feature) (Coord := Coord) ω i)
      (scaledMatrix (Feature := Feature) (Coord := Coord) ω j) =
        (Fintype.card Coord : ℝ)⁻¹ *
          ∑ r : Coord, pairSign (ω r) i j := by
  classical
  let dR : ℝ := Fintype.card Coord
  have hdR_pos : 0 < dR := by
    dsimp [dR]
    exact_mod_cast hd
  have hsqrt_sq : (Real.sqrt dR) ^ 2 = dR := by
    exact Real.sq_sqrt (le_of_lt hdR_pos)
  have hsqrt_ne : Real.sqrt dR ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.mpr hdR_pos)
  have hsqrt_mul : Real.sqrt dR * Real.sqrt dR = dR := by
    simpa [pow_two] using hsqrt_sq
  have hscale :
      (Real.sqrt dR)⁻¹ * (Real.sqrt dR)⁻¹ = dR⁻¹ := by
    calc
      (Real.sqrt dR)⁻¹ * (Real.sqrt dR)⁻¹ =
          (Real.sqrt dR * Real.sqrt dR)⁻¹ := by
            field_simp [hsqrt_ne]
      _ = dR⁻¹ := by
            rw [hsqrt_mul]
  calc
    inner (scaledMatrix (Feature := Feature) (Coord := Coord) ω i)
        (scaledMatrix (Feature := Feature) (Coord := Coord) ω j)
        = ∑ r : Coord,
            ((Real.sqrt dR)⁻¹ * rademacherSign (ω r i)) *
              ((Real.sqrt dR)⁻¹ * rademacherSign (ω r j)) := by
          simp [AppliedModelingLib.Math.LinearCompressedSensing.inner, scaledMatrix, dR]
    _ = ∑ r : Coord,
          ((Real.sqrt dR)⁻¹ * (Real.sqrt dR)⁻¹) *
            pairSign (ω r) i j := by
          refine Finset.sum_congr rfl ?_
          intro r _hr
          dsimp [pairSign]
          ring
    _ = ((Real.sqrt dR)⁻¹ * (Real.sqrt dR)⁻¹) *
          ∑ r : Coord, pairSign (ω r) i j := by
          rw [Finset.mul_sum]
    _ = dR⁻¹ * ∑ r : Coord, pairSign (ω r) i j := by
          rw [hscale]
    _ = (Fintype.card Coord : ℝ)⁻¹ *
          ∑ r : Coord, pairSign (ω r) i j := by
          simp [dR]

/--
Deterministic package: once all off-diagonal inner products are bounded by
`mu`, a scaled Rademacher matrix is `mu`-incoherent.
-/
theorem scaledMatrix_muIncoherentLE_of_offdiag [Fintype Feature] [Fintype Coord]
    {μ : ℝ} (hd : 0 < Fintype.card Coord)
    (ω : Coord → Feature → Bool)
    (hoff :
      ∀ ⦃i j : Feature⦄, i ≠ j →
        |inner (scaledMatrix (Feature := Feature) (Coord := Coord) ω i)
            (scaledMatrix (Feature := Feature) (Coord := Coord) ω j)| ≤ μ) :
    MuIncoherentLE
      (scaledMatrix (Feature := Feature) (Coord := Coord) ω) μ where
  self_inner := inner_scaledMatrix_self (Feature := Feature) (Coord := Coord) hd ω
  offdiag_abs_le := hoff

/-- The row-product signs are independent across rows. -/
theorem pairSign_iIndepFun [Fintype Feature]
    (i j : Feature) :
    iIndepFun
      (fun r (ω : Coord → Feature → Bool) => pairSign (ω r) i j)
      (rowsMeasure Feature Coord) := by
  let P : Coord → Measure (Feature → Bool) :=
    fun _ => FairCoin.productMeasure Feature
  let hP : ∀ r : Coord, IsProbabilityMeasure (P r) := by
    intro r
    simpa [P] using FairCoin.productMeasure_isProbabilityMeasure Feature
  have hrow :
      iIndepFun (fun r (ω : Coord → Feature → Bool) => ω r)
        (Measure.infinitePi P) := by
    exact
      @ProbabilityTheory.iIndepFun_infinitePi
        (ι := Coord) (𝓧 := fun _ : Coord => Feature → Bool)
        (m𝓧 := fun _ => by infer_instance)
        (Ω := fun _ : Coord => Feature → Bool)
        (mΩ := fun _ => by infer_instance)
        (P := P) hP (X := fun _ : Coord => id)
        (mX := fun _ => measurable_id)
  simpa [rowsMeasure, P] using hrow.comp
    (fun _ row => pairSign row i j)
    (fun _ => measurable_of_finite _)

/--
Hoeffding upper tail for one fixed off-diagonal pair, stated for centered
row-product signs.  The mean-zero simplification is a separate reusable lemma.
-/
theorem measure_sum_centered_pairSign_ge_le_exp
    [Fintype Feature] [Fintype Coord]
    (i j : Feature) {ε : ℝ} (hε : 0 ≤ ε) :
    (rowsMeasure Feature Coord).real
        {ω | ε ≤
          ∑ r : Coord,
            (pairSign (ω r) i j -
              ∫ x, pairSign (x r) i j ∂rowsMeasure Feature Coord)} ≤
      Real.exp
        (-ε ^ 2 /
          (2 * ((∑ _r : Coord,
            ((‖(1 : ℝ) - (-1)‖₊ / 2) ^ 2 : NNReal)) : ℝ))) := by
  classical
  haveI : IsProbabilityMeasure (rowsMeasure Feature Coord) :=
    rowsMeasure_isProbabilityMeasure Feature Coord
  refine
    AppliedModelingLib.measure_sum_centered_bounded_ge_le_exp_of_iIndepFun
      (μ := rowsMeasure Feature Coord)
      (X := fun r (ω : Coord → Feature → Bool) => pairSign (ω r) i j)
      (pairSign_iIndepFun (Feature := Feature) (Coord := Coord) i j)
      (s := Finset.univ) (a := (-1 : ℝ)) (b := 1) ?_ ?_ hε
  · intro r _hr
    exact (measurable_of_finite _).aemeasurable
  · intro r _hr
    exact ae_of_all _ fun ω => pairSign_mem_Icc (ω r) i j

/-- Hoeffding upper tail for the uncentered sum of one fixed off-diagonal pair. -/
theorem measure_sum_pairSign_ge_le_exp
    [Fintype Feature] [Fintype Coord]
    {i j : Feature} (hij : i ≠ j) {ε : ℝ} (hε : 0 ≤ ε) :
    (rowsMeasure Feature Coord).real
        {ω | ε ≤ ∑ r : Coord, pairSign (ω r) i j} ≤
      Real.exp
        (-ε ^ 2 /
          (2 * ((∑ _r : Coord,
            ((‖(1 : ℝ) - (-1)‖₊ / 2) ^ 2 : NNReal)) : ℝ))) := by
  classical
  haveI : IsProbabilityMeasure (rowsMeasure Feature Coord) :=
    rowsMeasure_isProbabilityMeasure Feature Coord
  have htail :=
    measure_sum_centered_pairSign_ge_le_exp
      (Feature := Feature) (Coord := Coord) i j hε
  refine le_trans ?_ htail
  refine measureReal_mono (μ := rowsMeasure Feature Coord) ?_
    (measure_ne_top _ _)
  intro ω hω
  have hcenter :
      (∑ r : Coord,
          (pairSign (ω r) i j -
            ∫ x, pairSign (x r) i j ∂rowsMeasure Feature Coord)) =
        ∑ r : Coord, pairSign (ω r) i j := by
    rw [Finset.sum_sub_distrib]
    simp [integral_pairSign_rowsMeasure (Feature := Feature) (Coord := Coord) hij]
  change ε ≤
    ∑ r : Coord,
      (pairSign (ω r) i j -
        ∫ x, pairSign (x r) i j ∂rowsMeasure Feature Coord)
  change ε ≤ ∑ r : Coord, pairSign (ω r) i j at hω
  rw [hcenter]
  exact hω

/-- Hoeffding lower tail for the uncentered sum of one fixed off-diagonal pair. -/
theorem measure_neg_sum_pairSign_ge_le_exp
    [Fintype Feature] [Fintype Coord]
    {i j : Feature} (hij : i ≠ j) {ε : ℝ} (hε : 0 ≤ ε) :
    (rowsMeasure Feature Coord).real
        {ω | ε ≤ -∑ r : Coord, pairSign (ω r) i j} ≤
      Real.exp
        (-ε ^ 2 /
          (2 * ((∑ _r : Coord,
            ((‖(1 : ℝ) - (-1)‖₊ / 2) ^ 2 : NNReal)) : ℝ))) := by
  classical
  haveI : IsProbabilityMeasure (rowsMeasure Feature Coord) :=
    rowsMeasure_isProbabilityMeasure Feature Coord
  have hindep :
      iIndepFun
        (fun r (ω : Coord → Feature → Bool) => -pairSign (ω r) i j)
        (rowsMeasure Feature Coord) := by
    exact (pairSign_iIndepFun (Feature := Feature) (Coord := Coord) i j).comp
      (fun _ x => -x) (fun _ => measurable_id.neg)
  have htail :
      (rowsMeasure Feature Coord).real
          {ω | ε ≤
            ∑ r : Coord,
              (-pairSign (ω r) i j -
                ∫ x, -pairSign (x r) i j ∂rowsMeasure Feature Coord)} ≤
        Real.exp
          (-ε ^ 2 /
            (2 * ((∑ _r : Coord,
              ((‖(1 : ℝ) - (-1)‖₊ / 2) ^ 2 : NNReal)) : ℝ))) := by
    refine
      AppliedModelingLib.measure_sum_centered_bounded_ge_le_exp_of_iIndepFun
        (μ := rowsMeasure Feature Coord)
        (X := fun r (ω : Coord → Feature → Bool) => -pairSign (ω r) i j)
        hindep
        (s := Finset.univ) (a := (-1 : ℝ)) (b := 1) ?_ ?_ hε
    · intro r _hr
      exact (measurable_of_finite _).aemeasurable
    · intro r _hr
      exact ae_of_all _ fun ω => by
        have h := pairSign_mem_Icc (ω r) i j
        change -1 ≤ -pairSign (ω r) i j ∧ -pairSign (ω r) i j ≤ 1
        constructor <;> linarith [h.1, h.2]
  refine le_trans ?_ htail
  refine measureReal_mono (μ := rowsMeasure Feature Coord) ?_
    (measure_ne_top _ _)
  intro ω hω
  have hcenter :
      (∑ r : Coord,
          (-pairSign (ω r) i j -
            ∫ x, -pairSign (x r) i j ∂rowsMeasure Feature Coord)) =
        -∑ r : Coord, pairSign (ω r) i j := by
    rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    simp [integral_neg, integral_pairSign_rowsMeasure
      (Feature := Feature) (Coord := Coord) hij]
  change ε ≤
    ∑ r : Coord,
      (-pairSign (ω r) i j -
        ∫ x, -pairSign (x r) i j ∂rowsMeasure Feature Coord)
  change ε ≤ -∑ r : Coord, pairSign (ω r) i j at hω
  rw [hcenter]
  exact hω

/-- Two-sided Hoeffding tail for the row-product sign sum. -/
theorem measure_abs_sum_pairSign_ge_le_two_mul_exp
    [Fintype Feature] [Fintype Coord]
    {i j : Feature} (hij : i ≠ j) {ε : ℝ} (hε : 0 ≤ ε) :
    (rowsMeasure Feature Coord).real
        {ω | ε ≤ |∑ r : Coord, pairSign (ω r) i j|} ≤
      2 *
        Real.exp
          (-ε ^ 2 /
            (2 * ((∑ _r : Coord,
              ((‖(1 : ℝ) - (-1)‖₊ / 2) ^ 2 : NNReal)) : ℝ))) := by
  classical
  haveI : IsProbabilityMeasure (rowsMeasure Feature Coord) :=
    rowsMeasure_isProbabilityMeasure Feature Coord
  let μM := rowsMeasure Feature Coord
  let posSet : Set (Coord → Feature → Bool) :=
    {ω | ε ≤ ∑ r : Coord, pairSign (ω r) i j}
  let negSet : Set (Coord → Feature → Bool) :=
    {ω | ε ≤ -∑ r : Coord, pairSign (ω r) i j}
  let absSet : Set (Coord → Feature → Bool) :=
    {ω | ε ≤ |∑ r : Coord, pairSign (ω r) i j|}
  have hsubset : absSet ⊆ posSet ∪ negSet := by
    intro ω hω
    dsimp [absSet, posSet, negSet] at hω ⊢
    by_cases hsum : 0 ≤ ∑ r : Coord, pairSign (ω r) i j
    · left
      simpa [abs_of_nonneg hsum] using hω
    · right
      have hsum' : ∑ r : Coord, pairSign (ω r) i j < 0 := lt_of_not_ge hsum
      simpa [abs_of_neg hsum'] using hω
  have hpos := measure_sum_pairSign_ge_le_exp
    (Feature := Feature) (Coord := Coord) hij hε
  have hneg := measure_neg_sum_pairSign_ge_le_exp
    (Feature := Feature) (Coord := Coord) hij hε
  calc
    μM.real absSet ≤ μM.real (posSet ∪ negSet) := by
      exact measureReal_mono (μ := μM) hsubset (measure_ne_top _ _)
    _ ≤ μM.real posSet + μM.real negSet := by
      exact measureReal_union_le (μ := μM) posSet negSet
    _ ≤
        Real.exp
          (-ε ^ 2 /
            (2 * ((∑ _r : Coord,
              ((‖(1 : ℝ) - (-1)‖₊ / 2) ^ 2 : NNReal)) : ℝ))) +
        Real.exp
          (-ε ^ 2 /
            (2 * ((∑ _r : Coord,
              ((‖(1 : ℝ) - (-1)‖₊ / 2) ^ 2 : NNReal)) : ℝ))) := by
      exact add_le_add hpos hneg
    _ = 2 *
        Real.exp
          (-ε ^ 2 /
            (2 * ((∑ _r : Coord,
              ((‖(1 : ℝ) - (-1)‖₊ / 2) ^ 2 : NNReal)) : ℝ))) := by
      ring

/--
Two-sided tail for one fixed off-diagonal inner product of the scaled
Rademacher matrix.
-/
theorem measure_abs_inner_scaledMatrix_ge_le_two_mul_exp
    [Fintype Feature] [Fintype Coord]
    (hd : 0 < Fintype.card Coord) {i j : Feature} (hij : i ≠ j)
    {μ : ℝ} (hμ : 0 ≤ μ) :
    (rowsMeasure Feature Coord).real
        {ω |
          μ ≤
            |inner (scaledMatrix (Feature := Feature) (Coord := Coord) ω i)
              (scaledMatrix (Feature := Feature) (Coord := Coord) ω j)|} ≤
      2 *
        Real.exp
          (-((μ * (Fintype.card Coord : ℝ)) ^ 2) /
            (2 * ((∑ _r : Coord,
              ((‖(1 : ℝ) - (-1)‖₊ / 2) ^ 2 : NNReal)) : ℝ))) := by
  classical
  haveI : IsProbabilityMeasure (rowsMeasure Feature Coord) :=
    rowsMeasure_isProbabilityMeasure Feature Coord
  let dR : ℝ := Fintype.card Coord
  have hdR_pos : 0 < dR := by
    dsimp [dR]
    exact_mod_cast hd
  have hε : 0 ≤ μ * dR := mul_nonneg hμ hdR_pos.le
  have htail :=
    measure_abs_sum_pairSign_ge_le_two_mul_exp
      (Feature := Feature) (Coord := Coord) hij (ε := μ * dR) hε
  refine le_trans ?_ htail
  refine measureReal_mono (μ := rowsMeasure Feature Coord) ?_
    (measure_ne_top _ _)
  intro ω hω
  change μ * dR ≤ |∑ r : Coord, pairSign (ω r) i j|
  change μ ≤
    |inner (scaledMatrix (Feature := Feature) (Coord := Coord) ω i)
      (scaledMatrix (Feature := Feature) (Coord := Coord) ω j)| at hω
  have hinner :
      inner (scaledMatrix (Feature := Feature) (Coord := Coord) ω i)
        (scaledMatrix (Feature := Feature) (Coord := Coord) ω j) =
          dR⁻¹ * ∑ r : Coord, pairSign (ω r) i j := by
    simpa [dR] using
      inner_scaledMatrix_eq_inv_card_mul_sum_pairSign
        (Feature := Feature) (Coord := Coord) hd ω i j
  rw [hinner, abs_mul, abs_of_pos (inv_pos.mpr hdR_pos)] at hω
  have hprod : dR * dR⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hdR_pos)
  have habs_nonneg : 0 ≤ |∑ r : Coord, pairSign (ω r) i j| := abs_nonneg _
  nlinarith

/-- Ordered off-diagonal feature pairs. -/
noncomputable def offdiagPairFinset
    [Fintype Feature] [DecidableEq Feature] : Finset (Feature × Feature) :=
  ((Finset.univ : Finset Feature).product (Finset.univ : Finset Feature)).filter
    fun p => p.1 ≠ p.2

theorem mem_offdiagPairFinset
    [Fintype Feature] [DecidableEq Feature] {p : Feature × Feature} :
    p ∈ offdiagPairFinset (Feature := Feature) ↔ p.1 ≠ p.2 := by
  classical
  simp [offdiagPairFinset]

/-- The ordered off-diagonal pair family is contained in all ordered pairs. -/
theorem card_offdiagPairFinset_le_card_sq
    [Fintype Feature] [DecidableEq Feature] :
    (offdiagPairFinset (Feature := Feature)).card ≤ Fintype.card Feature ^ 2 := by
  classical
  unfold offdiagPairFinset
  calc
    (((Finset.univ : Finset Feature).product Finset.univ).filter
        (fun pair => pair.1 ≠ pair.2)).card ≤
        ((Finset.univ : Finset Feature).product Finset.univ).card :=
      Finset.card_filter_le _ _
    _ = Fintype.card Feature ^ 2 := by simp [pow_two]

/-- Fixed-pair two-sided tail bound, as a reusable expression. -/
noncomputable def fixedPairTailBound (Coord : Type*) [Fintype Coord] (μ : ℝ) : ℝ :=
  2 *
    Real.exp
      (-((μ * (Fintype.card Coord : ℝ)) ^ 2) /
        (2 * ((∑ _r : Coord,
          ((‖(1 : ℝ) - (-1)‖₊ / 2) ^ 2 : NNReal)) : ℝ)))

/-- The fixed-pair tail bound in the simplified `d mu^2 / 2` form. -/
theorem fixedPairTailBound_eq
    (Coord : Type*) [Fintype Coord] (μ : ℝ) :
    fixedPairTailBound Coord μ =
      2 * Real.exp (-((Fintype.card Coord : ℝ) * μ ^ 2) / 2) := by
  classical
  let dR : ℝ := Fintype.card Coord
  have hsum :
      (∑ _r : Coord, (|(1 : ℝ) - (-1)| / 2) ^ 2) = dR := by
    norm_num [dR]
  by_cases hdR : dR = 0
  · simp [fixedPairTailBound, dR, hdR]
  · dsimp [fixedPairTailBound]
    rw [hsum]
    congr 2
    field_simp [hdR]
    ring

/--
Logarithmic dimension form of the ordered-pair Rademacher union bound.  If
`log (2 * pairCount) < d * μ^2 / 2`, then
`pairCount * 2 * exp (-(d * μ^2) / 2) < 1`.
-/
theorem pair_count_mul_fixedPairTailBound_lt_one_of_log_lt
    (Coord : Type*) [Fintype Coord] {pairCount μ : ℝ}
    (hpair_pos : 0 < pairCount)
    (hlog :
      Real.log (2 * pairCount) <
        ((Fintype.card Coord : ℝ) * μ ^ 2) / 2) :
    pairCount * fixedPairTailBound Coord μ < 1 := by
  let x : ℝ := ((Fintype.card Coord : ℝ) * μ ^ 2) / 2
  have hP_pos : 0 < 2 * pairCount := by positivity
  have hP_lt_exp : 2 * pairCount < Real.exp x := by
    exact (Real.log_lt_iff_lt_exp hP_pos).mp (by simpa [x] using hlog)
  have hexp_neg_pos : 0 < Real.exp (-x) := Real.exp_pos _
  have hmul_lt :
      (2 * pairCount) * Real.exp (-x) <
        Real.exp x * Real.exp (-x) :=
    mul_lt_mul_of_pos_right hP_lt_exp hexp_neg_pos
  have hexp_cancel : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    simp
  calc
    pairCount * fixedPairTailBound Coord μ =
        (2 * pairCount) * Real.exp (-x) := by
          rw [fixedPairTailBound_eq]
          have hxarg :
              -((Fintype.card Coord : ℝ) * μ ^ 2) / 2 = -x := by
            dsimp [x]
            ring
          rw [hxarg]
          ring
    _ < Real.exp x * Real.exp (-x) := hmul_lt
    _ = 1 := hexp_cancel

/-- An explicit finite coordinate count for the Rademacher incoherence union
bound.  One more than the natural ceiling of the logarithmic threshold is
strictly sufficient, while remaining within two of that nonnegative
threshold. -/
theorem exists_positive_fin_dimension_pair_count_mul_fixedPairTailBound_lt_one
    {pairCount μ : ℝ} (hpair_pos : 0 < pairCount) (hμ_pos : 0 < μ) :
    ∃ dimension : ℕ, 0 < dimension ∧
      ((dimension : ℝ) ≤
        max 0 (2 * Real.log (2 * pairCount) / μ ^ 2) + 2) ∧
      pairCount * fixedPairTailBound (Fin dimension) μ < 1 := by
  let threshold : ℝ := 2 * Real.log (2 * pairCount) / μ ^ 2
  let scale : ℝ := max 0 threshold
  let dimension : ℕ := Nat.ceil scale + 1
  have hscale_nonnegative : 0 ≤ scale := by
    dsimp [scale]
    exact le_max_left _ _
  have hthreshold_le_scale : threshold ≤ scale := by
    dsimp [scale]
    exact le_max_right _ _
  have hscale_le_ceil : scale ≤ (Nat.ceil scale : ℝ) := Nat.le_ceil scale
  have hceil_lt_dimension : (Nat.ceil scale : ℝ) < (dimension : ℝ) := by
    dsimp [dimension]
    norm_num
  have hthreshold_lt_dimension : threshold < (dimension : ℝ) :=
    lt_of_le_of_lt (le_trans hthreshold_le_scale hscale_le_ceil) hceil_lt_dimension
  have hdimension_pos : 0 < dimension := by
    dsimp [dimension]
    omega
  have hμ_sq_pos : 0 < μ ^ 2 := sq_pos_of_pos hμ_pos
  have hlog :
      Real.log (2 * pairCount) < ((Fintype.card (Fin dimension) : ℝ) * μ ^ 2) / 2 := by
    rw [Fintype.card_fin]
    apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    calc
      Real.log (2 * pairCount) * 2 = threshold * μ ^ 2 := by
        dsimp [threshold]
        field_simp [hμ_sq_pos.ne']
      _ < (dimension : ℝ) * μ ^ 2 :=
        mul_lt_mul_of_pos_right hthreshold_lt_dimension hμ_sq_pos
  have hdimension_upper :
      (dimension : ℝ) ≤ scale + 2 := by
    have hceil_lt : (Nat.ceil scale : ℝ) < scale + 1 :=
      Nat.ceil_lt_add_one hscale_nonnegative
    dsimp [dimension]
    norm_num
    linarith
  refine ⟨dimension, hdimension_pos, ?_, ?_⟩
  · simpa [scale, threshold] using hdimension_upper
  · exact pair_count_mul_fixedPairTailBound_lt_one_of_log_lt
      (Coord := Fin dimension) hpair_pos hlog

/--
Logarithmic dimension form of the ordered-pair Rademacher union bound with an
explicit failure probability. If
`log ((2 * pairCount) / δ) <= d * μ^2 / 2`, then the union-bound tail is at
most `δ`.
-/
theorem pair_count_mul_fixedPairTailBound_le_delta_of_log_div_le
    (Coord : Type*) [Fintype Coord] {pairCount μ δ : ℝ}
    (hpair_pos : 0 < pairCount) (hδ_pos : 0 < δ)
    (hlog :
      Real.log ((2 * pairCount) / δ) ≤
        ((Fintype.card Coord : ℝ) * μ ^ 2) / 2) :
    pairCount * fixedPairTailBound Coord μ ≤ δ := by
  let x : ℝ := ((Fintype.card Coord : ℝ) * μ ^ 2) / 2
  have harg_pos : 0 < (2 * pairCount) / δ := by
    positivity
  have hP_div_le_exp : (2 * pairCount) / δ ≤ Real.exp x := by
    exact (Real.log_le_iff_le_exp harg_pos).mp (by simpa [x] using hlog)
  have hP_le_delta_exp : 2 * pairCount ≤ δ * Real.exp x := by
    have hmul :=
      mul_le_mul_of_nonneg_right hP_div_le_exp hδ_pos.le
    calc
      2 * pairCount = ((2 * pairCount) / δ) * δ := by
        field_simp [ne_of_gt hδ_pos]
      _ ≤ Real.exp x * δ := hmul
      _ = δ * Real.exp x := by ring
  have hexp_neg_nonneg : 0 ≤ Real.exp (-x) := (Real.exp_pos _).le
  have hmul_le :
      (2 * pairCount) * Real.exp (-x) ≤
        (δ * Real.exp x) * Real.exp (-x) :=
    mul_le_mul_of_nonneg_right hP_le_delta_exp hexp_neg_nonneg
  have hexp_cancel : (δ * Real.exp x) * Real.exp (-x) = δ := by
    rw [mul_assoc, ← Real.exp_add]
    ring_nf
    simp
  calc
    pairCount * fixedPairTailBound Coord μ =
        (2 * pairCount) * Real.exp (-x) := by
          rw [fixedPairTailBound_eq]
          have hxarg :
              -((Fintype.card Coord : ℝ) * μ ^ 2) / 2 = -x := by
            dsimp [x]
            ring
          rw [hxarg]
          ring
    _ ≤ (δ * Real.exp x) * Real.exp (-x) := hmul_le
    _ = δ := hexp_cancel

/--
High-probability strict off-diagonal incoherence for a scaled Rademacher
matrix.  This is the reusable finite union-bound form behind the standard
random incoherent-matrix lemma.
-/
theorem measure_forall_offdiag_abs_inner_scaledMatrix_lt_ge_one_sub_union_bound
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    (hd : 0 < Fintype.card Coord) {μ : ℝ} (hμ : 0 ≤ μ) :
    measureProb (rowsMeasure Feature Coord)
        (fun ω =>
          ∀ ⦃i j : Feature⦄, i ≠ j →
            |inner (scaledMatrix (Feature := Feature) (Coord := Coord) ω i)
              (scaledMatrix (Feature := Feature) (Coord := Coord) ω j)| < μ) ≥
      1 - ((offdiagPairFinset (Feature := Feature)).card : ℝ) *
          fixedPairTailBound Coord μ := by
  classical
  let μM := rowsMeasure Feature Coord
  haveI : IsProbabilityMeasure μM := by
    simpa [μM] using rowsMeasure_isProbabilityMeasure Feature Coord
  let pairs := offdiagPairFinset (Feature := Feature)
  let bad : Feature × Feature → (Coord → Feature → Bool) → Prop :=
    fun p ω =>
      μ ≤
        |inner (scaledMatrix (Feature := Feature) (Coord := Coord) ω p.1)
          (scaledMatrix (Feature := Feature) (Coord := Coord) ω p.2)|
  let badUnion : Set (Coord → Feature → Bool) :=
    {ω | ∃ p ∈ pairs, bad p ω}
  let good : Set (Coord → Feature → Bool) :=
    {ω |
      ∀ ⦃i j : Feature⦄, i ≠ j →
        |inner (scaledMatrix (Feature := Feature) (Coord := Coord) ω i)
          (scaledMatrix (Feature := Feature) (Coord := Coord) ω j)| < μ}
  have hpair_le :
      ∀ p ∈ pairs,
        measureProb μM (bad p) ≤ fixedPairTailBound Coord μ := by
    intro p hp
    have hij : p.1 ≠ p.2 := by
      simpa [pairs] using (mem_offdiagPairFinset (Feature := Feature)).mp hp
    simpa [measureProb, μM, bad, fixedPairTailBound] using
      measure_abs_inner_scaledMatrix_ge_le_two_mul_exp
        (Feature := Feature) (Coord := Coord) hd hij hμ
  have hbad_union_le :
      measureProb μM (fun ω => ∃ p ∈ pairs, bad p ω) ≤
        ((pairs.card : ℕ) : ℝ) * fixedPairTailBound Coord μ := by
    have hunion :=
      measureProb_biUnion_finset_le
        (μ := μM) (s := pairs) (p := bad)
    have hsum_le :
        ∑ p ∈ pairs, measureProb μM (bad p) ≤
          ∑ _p ∈ pairs, fixedPairTailBound Coord μ := by
      exact Finset.sum_le_sum fun p hp => hpair_le p hp
    calc
      measureProb μM (fun ω => ∃ p ∈ pairs, bad p ω) ≤
          ∑ p ∈ pairs, measureProb μM (bad p) := hunion
      _ ≤ ∑ _p ∈ pairs, fixedPairTailBound Coord μ := hsum_le
      _ = ((pairs.card : ℕ) : ℝ) * fixedPairTailBound Coord μ := by
        simp
  have hgood_eq : good = badUnionᶜ := by
    ext ω
    constructor
    · intro hgood hbad
      rcases hbad with ⟨p, hp, hpbad⟩
      have hij : p.1 ≠ p.2 := by
        simpa [pairs] using (mem_offdiagPairFinset (Feature := Feature)).mp hp
      exact not_le_of_gt (hgood hij) hpbad
    · intro hnot i j hij
      by_contra hle
      exact hnot ⟨(i, j), by
        simpa [pairs] using
          (mem_offdiagPairFinset (Feature := Feature) (p := (i, j))).mpr hij,
        by simpa [bad] using hle⟩
  have hbad_meas : MeasurableSet badUnion := by
    exact Set.toFinite badUnion |>.measurableSet
  have hgood_prob :
      μM.real good = 1 - μM.real badUnion := by
    rw [hgood_eq, probReal_compl_eq_one_sub (μ := μM) hbad_meas]
  have hbad_bound :
      μM.real badUnion ≤
        ((offdiagPairFinset (Feature := Feature)).card : ℝ) *
          fixedPairTailBound Coord μ := by
    simpa [measureProb, μM, badUnion, pairs] using hbad_union_le
  rw [measureProb]
  change μM.real good ≥
    1 - ((offdiagPairFinset (Feature := Feature)).card : ℝ) *
        fixedPairTailBound Coord μ
  rw [hgood_prob]
  linarith

/--
High-probability strict off-diagonal incoherence in the standard `1 - δ` form:
the logarithmic row-dimension condition makes the union-bound failure
probability at most `δ`.
-/
theorem measure_forall_offdiag_abs_inner_scaledMatrix_lt_ge_one_sub_delta_of_log_div_le
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    (hd : 0 < Fintype.card Coord) {μ δ : ℝ} (hμ : 0 ≤ μ)
    (hpair_pos : 0 < ((offdiagPairFinset (Feature := Feature)).card : ℝ))
    (hδ_pos : 0 < δ)
    (hlog :
      Real.log
          ((2 * ((offdiagPairFinset (Feature := Feature)).card : ℝ)) / δ) ≤
        ((Fintype.card Coord : ℝ) * μ ^ 2) / 2) :
    measureProb (rowsMeasure Feature Coord)
        (fun ω =>
          ∀ ⦃i j : Feature⦄, i ≠ j →
            |inner (scaledMatrix (Feature := Feature) (Coord := Coord) ω i)
              (scaledMatrix (Feature := Feature) (Coord := Coord) ω j)| < μ) ≥
      1 - δ := by
  have hprob :=
    measure_forall_offdiag_abs_inner_scaledMatrix_lt_ge_one_sub_union_bound
      (Feature := Feature) (Coord := Coord) hd hμ
  have htail :
      ((offdiagPairFinset (Feature := Feature)).card : ℝ) *
          fixedPairTailBound Coord μ ≤ δ :=
    pair_count_mul_fixedPairTailBound_le_delta_of_log_div_le
      (Coord := Coord)
      (pairCount := ((offdiagPairFinset (Feature := Feature)).card : ℝ))
      (μ := μ) (δ := δ) hpair_pos hδ_pos hlog
  have hprob' :
      measureProb (rowsMeasure Feature Coord)
          (fun ω =>
            ∀ ⦃i j : Feature⦄, i ≠ j →
              |inner (scaledMatrix (Feature := Feature) (Coord := Coord) ω i)
                (scaledMatrix (Feature := Feature) (Coord := Coord) ω j)| < μ) ≥
        1 - ((offdiagPairFinset (Feature := Feature)).card : ℝ) *
            (2 * Real.exp (-((Fintype.card Coord : ℝ) * μ ^ 2) / 2)) := by
    simpa [fixedPairTailBound_eq] using hprob
  rw [fixedPairTailBound_eq] at htail
  linarith

/--
Existence corollary from the finite union bound: if the ordered-pair failure
bound is below one, some scaled Rademacher matrix is `mu`-incoherent.
-/
theorem exists_scaledMatrix_muIncoherentLE_of_union_bound_lt_one
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    (hd : 0 < Fintype.card Coord) {μ : ℝ} (hμ : 0 ≤ μ)
    (hbad_lt_one :
      ((offdiagPairFinset (Feature := Feature)).card : ℝ) *
          fixedPairTailBound Coord μ < 1) :
    ∃ A : Feature → Coord → ℝ, MuIncoherentLE A μ := by
  classical
  let μM := rowsMeasure Feature Coord
  haveI : IsProbabilityMeasure μM := by
    simpa [μM] using rowsMeasure_isProbabilityMeasure Feature Coord
  let pairs := offdiagPairFinset (Feature := Feature)
  let bad : Feature × Feature → (Coord → Feature → Bool) → Prop :=
    fun p ω =>
      μ ≤
        |inner (scaledMatrix (Feature := Feature) (Coord := Coord) ω p.1)
          (scaledMatrix (Feature := Feature) (Coord := Coord) ω p.2)|
  have hpair_le :
      ∀ p ∈ pairs,
        measureProb μM (bad p) ≤ fixedPairTailBound Coord μ := by
    intro p hp
    have hij : p.1 ≠ p.2 := by
      simpa [pairs] using (mem_offdiagPairFinset (Feature := Feature)).mp hp
    simpa [measureProb, μM, bad, fixedPairTailBound] using
      measure_abs_inner_scaledMatrix_ge_le_two_mul_exp
        (Feature := Feature) (Coord := Coord) hd hij hμ
  have hbad_union_le :
      measureProb μM (fun ω => ∃ p ∈ pairs, bad p ω) ≤
        ((pairs.card : ℕ) : ℝ) * fixedPairTailBound Coord μ := by
    have hunion :=
      measureProb_biUnion_finset_le
        (μ := μM) (s := pairs) (p := bad)
    have hsum_le :
        ∑ p ∈ pairs, measureProb μM (bad p) ≤
          ∑ _p ∈ pairs, fixedPairTailBound Coord μ := by
      exact Finset.sum_le_sum fun p hp => hpair_le p hp
    calc
      measureProb μM (fun ω => ∃ p ∈ pairs, bad p ω) ≤
          ∑ p ∈ pairs, measureProb μM (bad p) := hunion
      _ ≤ ∑ _p ∈ pairs, fixedPairTailBound Coord μ := hsum_le
      _ = ((pairs.card : ℕ) : ℝ) * fixedPairTailBound Coord μ := by
        simp
  by_contra hnone
  have huniv_subset :
      (Set.univ : Set (Coord → Feature → Bool)) ⊆
        {ω | ∃ p ∈ pairs, bad p ω} := by
    intro ω _hω
    by_contra hno_bad
    apply hnone
    refine ⟨scaledMatrix (Feature := Feature) (Coord := Coord) ω, ?_⟩
    refine scaledMatrix_muIncoherentLE_of_offdiag
      (Feature := Feature) (Coord := Coord) (μ := μ) hd ω ?_
    intro i j hij
    have hp : (i, j) ∈ pairs := by
      simpa [pairs] using
        (mem_offdiagPairFinset (Feature := Feature) (p := (i, j))).mpr hij
    have hnot : ¬ bad (i, j) ω := by
      intro hb
      exact hno_bad ⟨(i, j), hp, hb⟩
    exact le_of_lt (lt_of_not_ge hnot)
  have huniv_le :
      μM.real (Set.univ : Set (Coord → Feature → Bool)) ≤
        measureProb μM (fun ω => ∃ p ∈ pairs, bad p ω) := by
    exact measureReal_mono (μ := μM) huniv_subset (measure_ne_top _ _)
  have hbad_lt :
      measureProb μM (fun ω => ∃ p ∈ pairs, bad p ω) < 1 := by
    have hcard_eq :
        ((pairs.card : ℕ) : ℝ) =
          ((offdiagPairFinset (Feature := Feature)).card : ℝ) := by
      simp [pairs]
    rw [hcard_eq] at hbad_union_le
    exact lt_of_le_of_lt hbad_union_le hbad_lt_one
  have huniv_one :
      μM.real (Set.univ : Set (Coord → Feature → Bool)) = 1 := by
    simp [MeasureTheory.probReal_univ]
  linarith

/--
Existence corollary for exact basis-pursuit recovery from the same finite
Rademacher union bound.  This is the standard coherence-scale sufficient
condition; it is weaker than RIP-scale compressed sensing, but the deterministic
optimization step is fully internal.
-/
theorem exists_scaledMatrix_basisPursuitExactRecovery_of_union_bound_lt_one
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    (hd : 0 < Fintype.card Coord) {k : ℕ} {μ : ℝ} (hμ : 0 ≤ μ)
    (hbad_lt_one :
      ((offdiagPairFinset (Feature := Feature)).card : ℝ) *
          fixedPairTailBound Coord μ < 1)
    (hbound : (k : ℝ) * μ < 1 / 2) :
    ∃ A : Feature → Coord → ℝ, BasisPursuitExactRecovery A k := by
  rcases exists_scaledMatrix_muIncoherentLE_of_union_bound_lt_one
    (Feature := Feature) (Coord := Coord) hd hμ hbad_lt_one with
    ⟨A, hA⟩
  exact ⟨A, basisPursuitExactRecovery_of_muIncoherentLE hμ hA hbound⟩

/--
Supportwise union-bound skeleton for random RIP existence.  If the total
failure probability over the finite family of supports of size at most `s` is
below one, then some scaled Rademacher matrix has global RIP at order `s`.
The remaining analytic work in a full RIP proof is to bound each supportwise
failure probability.
-/
theorem exists_scaledMatrix_restrictedIsometryProperty_of_supportwise_failure_sum_lt_one
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {s : ℕ} {δ : ℝ}
    (hbad_lt_one :
      ∑ S ∈ supportFinsetsCardLe (Feature := Feature) s,
        measureProb (rowsMeasure Feature Coord)
          (fun ω =>
            ¬ RestrictedIsometryOnSupport
              (scaledMatrix (Feature := Feature) (Coord := Coord) ω) S δ) <
        1) :
    ∃ A : Feature → Coord → ℝ, RestrictedIsometryProperty A s δ := by
  classical
  let μM := rowsMeasure Feature Coord
  haveI : IsProbabilityMeasure μM := by
    simpa [μM] using rowsMeasure_isProbabilityMeasure Feature Coord
  let supports := supportFinsetsCardLe (Feature := Feature) s
  let bad : Finset Feature → (Coord → Feature → Bool) → Prop :=
    fun S ω =>
      ¬ RestrictedIsometryOnSupport
        (scaledMatrix (Feature := Feature) (Coord := Coord) ω) S δ
  have hbad_union_le :
      measureProb μM (fun ω => ∃ S ∈ supports, bad S ω) ≤
        ∑ S ∈ supports, measureProb μM (bad S) :=
    measureProb_biUnion_finset_le (μ := μM) (s := supports) (p := bad)
  by_contra hnone
  have huniv_subset :
      (Set.univ : Set (Coord → Feature → Bool)) ⊆
        {ω | ∃ S ∈ supports, bad S ω} := by
    intro ω _hω
    by_contra hno_bad
    apply hnone
    refine ⟨scaledMatrix (Feature := Feature) (Coord := Coord) ω, ?_⟩
    refine restrictedIsometryProperty_of_forall_supportFinsetsCardLe ?_
    intro S hS
    by_contra hbad
    exact hno_bad ⟨S, hS, hbad⟩
  have huniv_le :
      μM.real (Set.univ : Set (Coord → Feature → Bool)) ≤
        measureProb μM (fun ω => ∃ S ∈ supports, bad S ω) := by
    exact measureReal_mono (μ := μM) huniv_subset (measure_ne_top _ _)
  have hbad_lt :
      measureProb μM (fun ω => ∃ S ∈ supports, bad S ω) < 1 := by
    exact lt_of_le_of_lt hbad_union_le (by simpa [supports, bad, μM] using hbad_lt_one)
  have huniv_one :
      μM.real (Set.univ : Set (Coord → Feature → Bool)) = 1 := by
    simp [MeasureTheory.probReal_univ]
  linarith

/--
Uniform per-support failure adapter.  A full random RIP proof usually supplies
the same tail bound for each fixed support; this lemma converts that uniform
tail estimate and a cardinality/tail-product inequality into the failure-sum
condition used by
`exists_scaledMatrix_restrictedIsometryProperty_of_supportwise_failure_sum_lt_one`.
-/
theorem supportwise_failure_sum_lt_one_of_forall_le
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {s : ℕ} {δ η : ℝ}
    (hcard_mul :
      ((supportFinsetsCardLe (Feature := Feature) s).card : ℝ) * η < 1)
    (hfail :
      ∀ S ∈ supportFinsetsCardLe (Feature := Feature) s,
        measureProb (rowsMeasure Feature Coord)
          (fun ω =>
            ¬ RestrictedIsometryOnSupport
              (scaledMatrix (Feature := Feature) (Coord := Coord) ω) S δ) ≤
          η) :
    ∑ S ∈ supportFinsetsCardLe (Feature := Feature) s,
      measureProb (rowsMeasure Feature Coord)
        (fun ω =>
          ¬ RestrictedIsometryOnSupport
            (scaledMatrix (Feature := Feature) (Coord := Coord) ω) S δ) <
      1 := by
  classical
  let supports := supportFinsetsCardLe (Feature := Feature) s
  have hsum_le :
      ∑ S ∈ supports,
        measureProb (rowsMeasure Feature Coord)
          (fun ω =>
            ¬ RestrictedIsometryOnSupport
              (scaledMatrix (Feature := Feature) (Coord := Coord) ω) S δ) ≤
        ∑ _S ∈ supports, η := by
    exact Finset.sum_le_sum fun S hS => by
      exact hfail S (by simpa [supports] using hS)
  calc
    ∑ S ∈ supportFinsetsCardLe (Feature := Feature) s,
      measureProb (rowsMeasure Feature Coord)
        (fun ω =>
          ¬ RestrictedIsometryOnSupport
            (scaledMatrix (Feature := Feature) (Coord := Coord) ω) S δ)
        ≤ ∑ _S ∈ supports, η := by
          simpa [supports] using hsum_le
    _ = ((supportFinsetsCardLe (Feature := Feature) s).card : ℝ) * η := by
          simp [supports]
    _ < 1 := hcard_mul

/--
Existence form using a uniform per-support failure bound.  The only remaining
inputs are the fixed-support concentration estimate and the arithmetic showing
that the number of supports times that estimate is below one.
-/
theorem exists_scaledMatrix_restrictedIsometryProperty_of_uniform_supportwise_failure_lt_one
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {s : ℕ} {δ η : ℝ}
    (hcard_mul :
      ((supportFinsetsCardLe (Feature := Feature) s).card : ℝ) * η < 1)
    (hfail :
      ∀ S ∈ supportFinsetsCardLe (Feature := Feature) s,
        measureProb (rowsMeasure Feature Coord)
          (fun ω =>
            ¬ RestrictedIsometryOnSupport
              (scaledMatrix (Feature := Feature) (Coord := Coord) ω) S δ) ≤
          η) :
    ∃ A : Feature → Coord → ℝ, RestrictedIsometryProperty A s δ :=
  exists_scaledMatrix_restrictedIsometryProperty_of_supportwise_failure_sum_lt_one
    (Feature := Feature) (Coord := Coord) (s := s) (δ := δ)
    (supportwise_failure_sum_lt_one_of_forall_le
      (Feature := Feature) (Coord := Coord) (s := s) (δ := δ) (η := η)
      hcard_mul hfail)

/--
Rademacher restricted-isometry existence from the explicit finite-net tail.
The sole remaining premise is the finite support-family arithmetic comparing
the union-bound envelope to one.
-/
theorem exists_scaledMatrix_restrictedIsometryProperty_three_eighths_of_support_card_exp_lt
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    (hd : 0 < Fintype.card Coord) (s : ℕ)
    (hcard_mul : ((supportFinsetsCardLe (Feature := Feature) s).card : ℝ) *
      (2 * ((9 ^ s : ℕ) : ℝ) *
        Real.exp (-(Fintype.card Coord : ℝ) / 524288)) < 1) :
    ∃ A : Feature → Coord → ℝ, RestrictedIsometryProperty A s (3 / 8 : ℝ) := by
  apply exists_scaledMatrix_restrictedIsometryProperty_of_uniform_supportwise_failure_lt_one
    (Feature := Feature) (Coord := Coord) (s := s) (δ := (3 / 8 : ℝ))
    (η := 2 * ((9 ^ s : ℕ) : ℝ) *
      Real.exp (-(Fintype.card Coord : ℝ) / 524288))
  · exact hcard_mul
  · intro S hS
    have hScard : S.card ≤ s := mem_supportFinsetsCardLe.mp hS
    calc
      measureProb (rowsMeasure Feature Coord)
          (fun omega => ¬ RestrictedIsometryOnSupport
            (scaledMatrix (Feature := Feature) (Coord := Coord) omega) S (3 / 8 : ℝ)) ≤
          2 * ((9 ^ S.card : ℕ) : ℝ) *
            Real.exp (-(Fintype.card Coord : ℝ) / 524288) :=
        measure_not_restrictedIsometryOnSupport_scaledMatrix_three_eighths_le hd S
      _ ≤ 2 * ((9 ^ s : ℕ) : ℝ) *
            Real.exp (-(Fintype.card Coord : ℝ) / 524288) := by
              have hpownat : 9 ^ S.card ≤ 9 ^ s :=
                Nat.pow_le_pow_right (by norm_num) hScard
              have hpow : ((9 ^ S.card : ℕ) : ℝ) ≤ ((9 ^ s : ℕ) : ℝ) := by
                exact_mod_cast hpownat
              calc
                2 * ((9 ^ S.card : ℕ) : ℝ) *
                    Real.exp (-(Fintype.card Coord : ℝ) / 524288) =
                    2 * (((9 ^ S.card : ℕ) : ℝ) *
                      Real.exp (-(Fintype.card Coord : ℝ) / 524288)) := by ring
                _ ≤ 2 * (((9 ^ s : ℕ) : ℝ) *
                      Real.exp (-(Fintype.card Coord : ℝ) / 524288)) := by
                      gcongr
                _ = 2 * ((9 ^ s : ℕ) : ℝ) *
                      Real.exp (-(Fintype.card Coord : ℝ) / 524288) := by ring

/--
Exact finite `l1` recovery follows from the same explicit Rademacher
support-count inequality.  This is the standard RIP-to-nullspace-to-basis-
pursuit deterministic chain with the random-matrix part already internal.
-/
theorem exists_scaledMatrix_basisPursuitExactRecovery_of_support_card_exp_lt
    [LinearOrder Feature] [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    (hd : 0 < Fintype.card Coord) (k : ℕ) (hk : 0 < k)
    (hcard_mul : ((supportFinsetsCardLe (Feature := Feature) (3 * k)).card : ℝ) *
      (2 * ((9 ^ (3 * k) : ℕ) : ℝ) *
        Real.exp (-(Fintype.card Coord : ℝ) / 524288)) < 1) :
    ∃ A : Feature → Coord → ℝ, BasisPursuitExactRecovery A k := by
  rcases exists_scaledMatrix_restrictedIsometryProperty_three_eighths_of_support_card_exp_lt
    (Feature := Feature) (Coord := Coord) hd (3 * k) hcard_mul with ⟨A, hrip⟩
  refine ⟨A, ?_⟩
  exact basisPursuitExactRecovery_of_restrictedIsometry_three_mul
    (A := A) (k := k) (δ := (3 / 8 : ℝ)) hk (by norm_num) (by norm_num) hrip

/--
Exponential-tail form of the uniform supportwise failure adapter.  If each
fixed support fails with probability at most `exp (-rate)` and the logarithm
of the support-family size is below `rate`, then the union bound is below one.
-/
theorem exists_scaledMatrix_restrictedIsometryProperty_of_uniform_supportwise_failure_exp_log_card_lt
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {s : ℕ} {δ rate : ℝ}
    (hcard_pos : 0 < ((supportFinsetsCardLe (Feature := Feature) s).card : ℝ))
    (hlog_card_lt :
      Real.log ((supportFinsetsCardLe (Feature := Feature) s).card : ℝ) <
        rate)
    (hfail :
      ∀ S ∈ supportFinsetsCardLe (Feature := Feature) s,
        measureProb (rowsMeasure Feature Coord)
          (fun ω =>
            ¬ RestrictedIsometryOnSupport
              (scaledMatrix (Feature := Feature) (Coord := Coord) ω) S δ) ≤
          Real.exp (-rate)) :
    ∃ A : Feature → Coord → ℝ, RestrictedIsometryProperty A s δ := by
  have hcard_mul :
      ((supportFinsetsCardLe (Feature := Feature) s).card : ℝ) *
          Real.exp (-rate) < 1 :=
    AppliedModelingLib.Math.mul_exp_neg_lt_one_of_log_lt hcard_pos hlog_card_lt
  exact
    exists_scaledMatrix_restrictedIsometryProperty_of_uniform_supportwise_failure_lt_one
      (Feature := Feature) (Coord := Coord) (s := s) (δ := δ)
      (η := Real.exp (-rate)) hcard_mul hfail

/--
Binomial-count version of the uniform supportwise failure adapter.  The
finite support family has cardinality at most
`sum_{r <= s} choose |Feature| r`, so a fixed-support tail bound whose product
with this binomial count is below one yields a sampled RIP matrix.
-/
theorem exists_scaledMatrix_restrictedIsometryProperty_of_uniform_supportwise_failure_sum_choose_lt_one
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {s : ℕ} {δ η : ℝ}
    (hη_nonneg : 0 ≤ η)
    (hcount_mul :
      ((∑ r ∈ Finset.range (s + 1), Nat.choose (Fintype.card Feature) r : ℕ) : ℝ) *
          η < 1)
    (hfail :
      ∀ S ∈ supportFinsetsCardLe (Feature := Feature) s,
        measureProb (rowsMeasure Feature Coord)
          (fun ω =>
            ¬ RestrictedIsometryOnSupport
              (scaledMatrix (Feature := Feature) (Coord := Coord) ω) S δ) ≤
          η) :
    ∃ A : Feature → Coord → ℝ, RestrictedIsometryProperty A s δ := by
  have hcard_nat :
      (supportFinsetsCardLe (Feature := Feature) s).card ≤
        ∑ r ∈ Finset.range (s + 1), Nat.choose (Fintype.card Feature) r :=
    AppliedModelingLib.Math.LinearCompressedSensing.supportFinsetsCardLe_card_le_sum_choose
      (Feature := Feature) s
  have hcard_real :
      ((supportFinsetsCardLe (Feature := Feature) s).card : ℝ) ≤
        ((∑ r ∈ Finset.range (s + 1),
          Nat.choose (Fintype.card Feature) r : ℕ) : ℝ) := by
    exact_mod_cast hcard_nat
  have hcard_mul :
      ((supportFinsetsCardLe (Feature := Feature) s).card : ℝ) * η < 1 := by
    exact (mul_le_mul_of_nonneg_right hcard_real hη_nonneg).trans_lt hcount_mul
  exact
    exists_scaledMatrix_restrictedIsometryProperty_of_uniform_supportwise_failure_lt_one
      (Feature := Feature) (Coord := Coord) (s := s) (δ := δ) (η := η)
      hcard_mul hfail

/--
Small-support binomial-count version.  When `s <= |Feature| / 2`, the number
of supports of size at most `s` is at most `(s+1) * choose |Feature| s`.
-/
theorem exists_scaledMatrix_restrictedIsometryProperty_of_uniform_supportwise_failure_succ_mul_choose_lt_one
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {s : ℕ} {δ η : ℝ}
    (hs_half : s ≤ Fintype.card Feature / 2)
    (hη_nonneg : 0 ≤ η)
    (hcount_mul :
      (((s + 1) * Nat.choose (Fintype.card Feature) s : ℕ) : ℝ) *
          η < 1)
    (hfail :
      ∀ S ∈ supportFinsetsCardLe (Feature := Feature) s,
        measureProb (rowsMeasure Feature Coord)
          (fun ω =>
            ¬ RestrictedIsometryOnSupport
              (scaledMatrix (Feature := Feature) (Coord := Coord) ω) S δ) ≤
          η) :
    ∃ A : Feature → Coord → ℝ, RestrictedIsometryProperty A s δ := by
  have hcard_nat :
      (supportFinsetsCardLe (Feature := Feature) s).card ≤
        (s + 1) * Nat.choose (Fintype.card Feature) s :=
    AppliedModelingLib.Math.LinearCompressedSensing.supportFinsetsCardLe_card_le_succ_mul_choose_of_le_half
      (Feature := Feature) hs_half
  have hcard_real :
      ((supportFinsetsCardLe (Feature := Feature) s).card : ℝ) ≤
        (((s + 1) * Nat.choose (Fintype.card Feature) s : ℕ) : ℝ) := by
    exact_mod_cast hcard_nat
  have hcard_mul :
      ((supportFinsetsCardLe (Feature := Feature) s).card : ℝ) * η < 1 := by
    exact (mul_le_mul_of_nonneg_right hcard_real hη_nonneg).trans_lt hcount_mul
  exact
    exists_scaledMatrix_restrictedIsometryProperty_of_uniform_supportwise_failure_lt_one
      (Feature := Feature) (Coord := Coord) (s := s) (δ := δ) (η := η)
      hcard_mul hfail

/--
Exponential-tail version of the small-support binomial-count adapter.  This is
the usual shape of a random RIP proof after the fixed-support concentration
estimate has been proved: a per-support tail `exp (-rate)` wins once the
logarithm of `(s+1) * choose |Feature| s` is below `rate`.
-/
theorem exists_scaledMatrix_restrictedIsometryProperty_of_uniform_supportwise_failure_succ_mul_choose_exp_log_count_lt
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {s : ℕ} {δ rate : ℝ}
    (hs_half : s ≤ Fintype.card Feature / 2)
    (hcount_pos :
      0 < (((s + 1) * Nat.choose (Fintype.card Feature) s : ℕ) : ℝ))
    (hlog_count_lt :
      Real.log (((s + 1) * Nat.choose (Fintype.card Feature) s : ℕ) : ℝ) <
        rate)
    (hfail :
      ∀ S ∈ supportFinsetsCardLe (Feature := Feature) s,
        measureProb (rowsMeasure Feature Coord)
          (fun ω =>
            ¬ RestrictedIsometryOnSupport
              (scaledMatrix (Feature := Feature) (Coord := Coord) ω) S δ) ≤
          Real.exp (-rate)) :
    ∃ A : Feature → Coord → ℝ, RestrictedIsometryProperty A s δ := by
  have hcount_mul :
      (((s + 1) * Nat.choose (Fintype.card Feature) s : ℕ) : ℝ) *
          Real.exp (-rate) < 1 :=
    AppliedModelingLib.Math.mul_exp_neg_lt_one_of_log_lt hcount_pos hlog_count_lt
  exact
    exists_scaledMatrix_restrictedIsometryProperty_of_uniform_supportwise_failure_succ_mul_choose_lt_one
      (Feature := Feature) (Coord := Coord) (s := s) (δ := δ)
      (η := Real.exp (-rate)) hs_half (Real.exp_pos _).le hcount_mul hfail

end RademacherMatrix
end Probability
end AppliedModelingLib
