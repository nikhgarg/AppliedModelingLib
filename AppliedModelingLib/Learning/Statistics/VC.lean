import Mathlib.Combinatorics.SetFamily.Shatter
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Finite traces and VC dimension

This file gives the combinatorial layer used by finite-sample VC
generalization bounds.  A hypothesis class may be infinite; its restriction to
any finite sample is nevertheless a finite family of binary labelings.  The
definitions below make that finite trace explicit and reuse Mathlib's
Sauer--Shelah theorem for its growth bound.
-/

namespace AppliedModelingLib
namespace Statistics

open scoped BigOperators

/-- A binary classifier is represented by its Boolean positive-label predicate. -/
abbrev BinaryClassifier (X : Type*) := X → Bool

/-- The positive-label trace of one binary classifier on a finite sample. -/
noncomputable def binaryClassifierTrace
    {X : Type*} (classifier : BinaryClassifier X)
    (sample : Finset X) : Finset sample := by
  classical
  exact sample.attach.filter fun point => classifier point.1 = true

/-- Two classifiers agree on a finite feature sample. -/
def BinaryClassifiersAgreeOn
    {X : Type*} (sample : Finset X) (first second : BinaryClassifier X) : Prop :=
  ∀ point ∈ sample, first point = second point

/-- The finite feature support of an indexed family of observations. -/
noncomputable def finiteFeatureSupport
    {X Index : Type*} [Fintype Index] (features : Index → X) : Finset X := by
  classical
  exact Finset.univ.image features

/-- Every indexed feature belongs to its finite support. -/
theorem mem_finiteFeatureSupport
    {X Index : Type*} [Fintype Index] (features : Index → X) (index : Index) :
    features index ∈ finiteFeatureSupport features := by
  classical
  simp [finiteFeatureSupport]

/-- A finite feature support has no more points than its indexing family. -/
theorem card_finiteFeatureSupport_le_fintype_card
    {X Index : Type*} [Fintype Index] (features : Index → X) :
    (finiteFeatureSupport features).card ≤ Fintype.card Index := by
  classical
  unfold finiteFeatureSupport
  simpa using (Finset.card_image_le (s := (Finset.univ : Finset Index)) (f := features))

/-- Agreement on an indexed family's finite support is pointwise agreement. -/
theorem binaryClassifiersAgreeOn_of_agreeOn_finiteFeatureSupport
    {X Index : Type*} [Fintype Index] (features : Index → X)
    {first second : BinaryClassifier X}
    (hagrees : BinaryClassifiersAgreeOn (finiteFeatureSupport features) first second)
    (index : Index) :
    first (features index) = second (features index) :=
  hagrees _ (mem_finiteFeatureSupport features index)

/--
The label traces realized by a possibly infinite binary concept class on a
finite sample.  A trace is stored as its subset of positively labelled sample
positions; the `univ.filter` presentation keeps the result finite without
requiring the source class itself to be finite or enumerable.
-/
noncomputable def binaryTrace
    {X : Type*} (concepts : Set (BinaryClassifier X))
    (sample : Finset X) : Finset (Finset sample) := by
  classical
  exact Finset.univ.filter fun labels =>
    ∃ classifier ∈ concepts, ∀ point : sample,
      (point ∈ labels) ↔ classifier point.1 = true

/-- Every member of a concept class realizes its own finite trace. -/
theorem binaryClassifierTrace_mem_binaryTrace
    {X : Type*} {concepts : Set (BinaryClassifier X)}
    {classifier : BinaryClassifier X} (hclassifier : classifier ∈ concepts)
    (sample : Finset X) :
    binaryClassifierTrace classifier sample ∈ binaryTrace concepts sample := by
  classical
  simp only [binaryTrace, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨classifier, hclassifier, ?_⟩
  intro point
  simp [binaryClassifierTrace]

/-- Equal positive-label traces imply agreement on every sampled feature. -/
theorem binaryClassifiersAgreeOn_of_trace_eq
    {X : Type*} {first second : BinaryClassifier X}
    {sample : Finset X}
    (htrace : binaryClassifierTrace first sample = binaryClassifierTrace second sample) :
    BinaryClassifiersAgreeOn sample first second := by
  intro point hpoint
  have hmembership :
      ((⟨point, hpoint⟩ : sample) ∈ binaryClassifierTrace first sample) ↔
        ((⟨point, hpoint⟩ : sample) ∈ binaryClassifierTrace second sample) := by
    rw [htrace]
  cases hfirst : first point <;> cases hsecond : second point <;>
    simp [binaryClassifierTrace, hfirst, hsecond] at hmembership ⊢

/--
A canonical representative for a possible finite trace.  Outside the realized
trace family it returns the all-negative classifier; on a realized trace the
definition chooses a classifier that realizes it.
-/
noncomputable def classifierOfBinaryTrace
    {X : Type*} (concepts : Set (BinaryClassifier X))
    (sample : Finset X) (labels : Finset sample) : BinaryClassifier X := by
  classical
  exact if h : ∃ classifier ∈ concepts, ∀ point : sample,
      (point ∈ labels) ↔ classifier point.1 = true then
    Classical.choose h
  else fun _ => false

/-- A realized trace is realized by its selected representative. -/
theorem classifierOfBinaryTrace_realizes
    {X : Type*} {concepts : Set (BinaryClassifier X)}
    {sample : Finset X} {labels : Finset sample}
    (hlabels : labels ∈ binaryTrace concepts sample) :
    ∀ point : sample,
      (point ∈ labels) ↔ classifierOfBinaryTrace concepts sample labels point.1 = true := by
  classical
  have hexists : ∃ classifier ∈ concepts, ∀ point : sample,
      (point ∈ labels) ↔ classifier point.1 = true := by
    exact (Finset.mem_filter.mp hlabels).2
  simp only [classifierOfBinaryTrace, dif_pos hexists]
  exact Classical.choose_spec hexists |>.2

/-- The selected representative of a realized trace belongs to the source class. -/
theorem classifierOfBinaryTrace_mem
    {X : Type*} {concepts : Set (BinaryClassifier X)}
    {sample : Finset X} {labels : Finset sample}
    (hlabels : labels ∈ binaryTrace concepts sample) :
    classifierOfBinaryTrace concepts sample labels ∈ concepts := by
  classical
  have hexists : ∃ classifier ∈ concepts, ∀ point : sample,
      (point ∈ labels) ↔ classifier point.1 = true := by
    exact (Finset.mem_filter.mp hlabels).2
  simp only [classifierOfBinaryTrace, dif_pos hexists]
  exact Classical.choose_spec hexists |>.1

/-- The finite index type of realized traces on a fixed sample. -/
abbrev BinaryTraceRepresentativeIndex
    {X : Type*} (concepts : Set (BinaryClassifier X))
    (sample : Finset X) :=
  {labels : Finset sample // labels ∈ binaryTrace concepts sample}

/--
Every classifier in the source class agrees with a selected finite
representative on the given sample.  This is the exact finite reduction used
before a trace-based union bound.
-/
theorem exists_binaryTraceRepresentative_agreesOn
    {X : Type*} {concepts : Set (BinaryClassifier X)}
    {classifier : BinaryClassifier X} (hclassifier : classifier ∈ concepts)
    (sample : Finset X) :
    ∃ labels : BinaryTraceRepresentativeIndex concepts sample,
      BinaryClassifiersAgreeOn sample classifier
        (classifierOfBinaryTrace concepts sample labels.1) := by
  classical
  let labels := binaryClassifierTrace classifier sample
  have hlabels : labels ∈ binaryTrace concepts sample := by
    simpa [labels] using binaryClassifierTrace_mem_binaryTrace hclassifier sample
  refine ⟨⟨labels, hlabels⟩, ?_⟩
  apply binaryClassifiersAgreeOn_of_trace_eq
  apply Finset.ext
  intro point
  have hrealizes := classifierOfBinaryTrace_realizes hlabels point
  simp only [labels, binaryClassifierTrace, Finset.mem_filter, Finset.mem_attach,
    true_and] at hrealizes ⊢
  exact hrealizes

/--
Every classifier in a concept class has a trace representative agreeing on an
arbitrary finite indexed feature family.  The indexing type may contain
repeated observations; `finiteFeatureSupport` deliberately removes repeats,
which cannot create new label traces.
-/
theorem exists_binaryTraceRepresentative_agreesOn_finiteFeatureSupport
    {X Index : Type*} [Fintype Index] {concepts : Set (BinaryClassifier X)}
    {classifier : BinaryClassifier X} (hclassifier : classifier ∈ concepts)
    (features : Index → X) :
    ∃ labels : BinaryTraceRepresentativeIndex concepts (finiteFeatureSupport features),
      ∀ index,
        classifier (features index) =
          classifierOfBinaryTrace concepts (finiteFeatureSupport features) labels.1
            (features index) := by
  rcases exists_binaryTraceRepresentative_agreesOn hclassifier
    (finiteFeatureSupport features) with ⟨labels, hagrees⟩
  refine ⟨labels, ?_⟩
  intro index
  exact binaryClassifiersAgreeOn_of_agreeOn_finiteFeatureSupport features hagrees index

/-- The combinatorial VC dimension of the class's trace on a finite sample. -/
noncomputable def binaryTraceVCDimension
    {X : Type*} (concepts : Set (BinaryClassifier X))
    (sample : Finset X) : ℕ := by
  classical
  exact (binaryTrace concepts sample).vcDim

/--
`d` is a VC-dimension upper bound for a binary concept class when every finite
trace has combinatorial VC dimension at most `d`.  This is equivalent to the
usual shattering formulation and is the finite object consumed by
Sauer--Shelah and sampling arguments.
-/
def VCDimensionAtMost
    {X : Type*} (concepts : Set (BinaryClassifier X)) (d : ℕ) : Prop := by
  classical
  exact ∀ sample : Finset X, binaryTraceVCDimension concepts sample ≤ d

/-- The trace growth function on a concrete finite sample. -/
noncomputable def binaryGrowth
    {X : Type*} (concepts : Set (BinaryClassifier X))
    (sample : Finset X) : ℕ := by
  classical
  exact (binaryTrace concepts sample).card

/-- The number of subsets of a trace that the trace family shatters. -/
noncomputable def binaryTraceShattererCard
    {X : Type*} (concepts : Set (BinaryClassifier X))
    (sample : Finset X) : ℕ := by
  classical
  exact (binaryTrace concepts sample).shatterer.card

/-- The finite representative index has exactly the trace-growth cardinality. -/
theorem card_binaryTraceRepresentativeIndex_eq_growth
    {X : Type*} (concepts : Set (BinaryClassifier X))
    (sample : Finset X) :
    Fintype.card (BinaryTraceRepresentativeIndex concepts sample) =
      binaryGrowth concepts sample := by
  classical
  exact Fintype.card_coe (binaryTrace concepts sample)

/-- A trace family is no larger than the family of sets it shatters. -/
theorem binaryGrowth_le_trace_shatterer_card
    {X : Type*} (concepts : Set (BinaryClassifier X))
    (sample : Finset X) :
    binaryGrowth concepts sample ≤ binaryTraceShattererCard concepts sample := by
  classical
  unfold binaryGrowth binaryTraceShattererCard
  exact Finset.card_le_card_shatterer _

/--
Sauer--Shelah for a concrete trace: its growth is bounded by the binomial sum
through the trace's VC dimension.
-/
theorem binaryGrowth_le_sum_choose_traceVC
    {X : Type*} (concepts : Set (BinaryClassifier X))
    (sample : Finset X) :
    binaryGrowth concepts sample ≤
      ∑ k ∈ Finset.Iic (binaryTraceVCDimension concepts sample), sample.card.choose k := by
  classical
  unfold binaryGrowth binaryTraceVCDimension
  exact (Finset.card_le_card_shatterer _).trans
    (by simpa using
      (Finset.card_shatterer_le_sum_vcDim (𝒜 := binaryTrace concepts sample)))

/-- A VC-dimension upper bound controls the VC dimension of every finite trace. -/
theorem binaryTrace_vcDim_le_of_vcDimensionAtMost
    {X : Type*} {concepts : Set (BinaryClassifier X)} {d : ℕ}
    (hvc : VCDimensionAtMost concepts d) (sample : Finset X) :
    binaryTraceVCDimension concepts sample ≤ d := by
  classical
  exact hvc sample

/--
The source VC-dimension hypothesis converts Sauer--Shelah's local trace bound
to the usual binomial growth bound with parameter `d`.
-/
theorem binaryGrowth_le_sum_choose_of_vcDimensionAtMost
    {X : Type*} {concepts : Set (BinaryClassifier X)} {d : ℕ}
    (hvc : VCDimensionAtMost concepts d) (sample : Finset X) :
    binaryGrowth concepts sample ≤
      ∑ k ∈ Finset.Iic d, sample.card.choose k := by
  classical
  calc
    binaryGrowth concepts sample ≤
        ∑ k ∈ Finset.Iic (binaryTraceVCDimension concepts sample), sample.card.choose k :=
      binaryGrowth_le_sum_choose_traceVC concepts sample
    _ ≤ ∑ k ∈ Finset.Iic d, sample.card.choose k := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.Iic_subset_Iic.mpr (hvc sample)
      · intro k _ _
        exact Nat.zero_le _

/--
Sauer--Shelah's growth bound is monotone in the available feature count. This
form is used when a trace support was formed from an indexed sample with
possible repeated features.
-/
theorem binaryGrowth_le_sum_choose_of_vcDimensionAtMost_le_card
    {X : Type*} {concepts : Set (BinaryClassifier X)} {d bound : ℕ}
    (hvc : VCDimensionAtMost concepts d) (sample : Finset X)
    (hsample_card : sample.card ≤ bound) :
    binaryGrowth concepts sample ≤
      ∑ k ∈ Finset.Iic d, bound.choose k := by
  calc
    binaryGrowth concepts sample ≤
        ∑ k ∈ Finset.Iic d, sample.card.choose k :=
      binaryGrowth_le_sum_choose_of_vcDimensionAtMost hvc sample
    _ ≤ ∑ k ∈ Finset.Iic d, bound.choose k := by
      apply Finset.sum_le_sum
      intro k _
      exact Nat.choose_le_choose k hsample_card

/--
An arbitrary finite indexed feature family has a VC trace-growth bound using
its index cardinality rather than its (possibly smaller) distinct support.
-/
theorem binaryGrowth_finiteFeatureSupport_le_sum_choose_of_vcDimensionAtMost
    {X Index : Type*} [Fintype Index] {concepts : Set (BinaryClassifier X)} {d : ℕ}
    (hvc : VCDimensionAtMost concepts d) (features : Index → X) :
    binaryGrowth concepts (finiteFeatureSupport features) ≤
      ∑ k ∈ Finset.Iic d, (Fintype.card Index).choose k :=
  binaryGrowth_le_sum_choose_of_vcDimensionAtMost_le_card hvc
    (finiteFeatureSupport features)
    (card_finiteFeatureSupport_le_fintype_card features)

/--
The standard binomial growth envelope.  Weight the binomial expansion of
`(1 + d / n)^n` by `(d / n)^k`: on the range `k ≤ d`, its smallest weight is
`(d / n)^d`.  This gives the sharp VC form without inserting an avoidable
factor of `d + 1`.
-/
theorem sum_choose_le_exp_one_mul_div_pow
    {n d : ℕ} (hd : 0 < d) (hdn : d ≤ n) :
    (∑ k ∈ Finset.Iic d, (n.choose k : ℝ)) ≤
      (Real.exp 1 * (n : ℝ) / (d : ℝ)) ^ d := by
  let x : ℝ := (d : ℝ) / (n : ℝ)
  have hn : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le hd hdn)
  have hdReal : 0 < (d : ℝ) := by
    exact_mod_cast hd
  have hx_nonneg : 0 ≤ x := by
    dsimp [x]
    positivity
  have hx_le_one : x ≤ 1 := by
    dsimp [x]
    exact div_le_one_of_le₀ (by exact_mod_cast hdn) hn.le
  have hsub : Finset.Iic d ⊆ Finset.range (n + 1) := by
    intro k hk
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le ((Finset.mem_Iic.mp hk).trans hdn)
  have hpow : ∀ k ∈ Finset.Iic d, x ^ d ≤ x ^ k := by
    intro k hk
    have hkd : k ≤ d := Finset.mem_Iic.mp hk
    rw [← Nat.add_sub_of_le hkd, pow_add]
    have hrest : x ^ (d - k) ≤ 1 := pow_le_one₀ hx_nonneg hx_le_one
    have hleft : 0 ≤ x ^ k := pow_nonneg hx_nonneg _
    simpa using mul_le_mul_of_nonneg_left hrest hleft
  have hweighted :
      (∑ k ∈ Finset.Iic d, (n.choose k : ℝ)) * x ^ d ≤
        ∑ k ∈ Finset.Iic d, x ^ k * (n.choose k : ℝ) := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum ?_
    intro k hk
    have hchoose : 0 ≤ (n.choose k : ℝ) := by
      positivity
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_of_nonneg_left (hpow k hk) hchoose
  have hpartial :
      (∑ k ∈ Finset.Iic d, x ^ k * (n.choose k : ℝ)) ≤
        ∑ k ∈ Finset.range (n + 1), x ^ k * (n.choose k : ℝ) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (by
      intro k _ _
      positivity)
  have hbinomial :
      (∑ k ∈ Finset.range (n + 1), x ^ k * (n.choose k : ℝ)) = (x + 1) ^ n := by
    rw [add_pow]
    refine (Finset.sum_congr rfl ?_).symm
    intro k hk
    simp
  have hNx : (n : ℝ) * x = (d : ℝ) := by
    dsimp [x]
    field_simp [hn.ne']
  have hexp : (x + 1) ^ n ≤ (Real.exp 1) ^ d := by
    calc
      (x + 1) ^ n ≤ (Real.exp x) ^ n := by
        apply pow_le_pow_left₀
        · positivity
        · simpa [add_comm] using Real.add_one_le_exp x
      _ = Real.exp ((n : ℝ) * x) := (Real.exp_nat_mul x n).symm
      _ = Real.exp (d : ℝ) := by rw [hNx]
      _ = (Real.exp 1) ^ d := by simpa using Real.exp_nat_mul 1 d
  have hsum :
      (∑ k ∈ Finset.Iic d, (n.choose k : ℝ)) * x ^ d ≤ (Real.exp 1) ^ d :=
    hweighted.trans (hpartial.trans (by rw [hbinomial]; exact hexp))
  have hxpos : 0 < x := by
    dsimp [x]
    positivity
  have hdiv :
      (∑ k ∈ Finset.Iic d, (n.choose k : ℝ)) ≤ (Real.exp 1) ^ d / x ^ d :=
    (le_div_iff₀ (pow_pos hxpos _)).mpr hsum
  have hratio : (Real.exp 1) ^ d / x ^ d =
      (Real.exp 1 * (n : ℝ) / (d : ℝ)) ^ d := by
    dsimp [x]
    rw [div_pow, div_pow]
    field_simp [hn.ne', hdReal.ne']
    ring
  rwa [hratio] at hdiv

/--
Logarithmic form of `sum_choose_le_exp_one_mul_div_pow`, matching the
`d (log (n / d) + 1)` entropy term used in VC confidence radii.
-/
theorem sum_choose_le_exp_mul_log_div_add_one
    {n d : ℕ} (hd : 0 < d) (hdn : d ≤ n) :
    (∑ k ∈ Finset.Iic d, (n.choose k : ℝ)) ≤
      Real.exp ((d : ℝ) * (Real.log ((n : ℝ) / (d : ℝ)) + 1)) := by
  calc
    (∑ k ∈ Finset.Iic d, (n.choose k : ℝ)) ≤
        (Real.exp 1 * (n : ℝ) / (d : ℝ)) ^ d :=
      sum_choose_le_exp_one_mul_div_pow hd hdn
    _ = Real.exp ((d : ℝ) * (Real.log ((n : ℝ) / (d : ℝ)) + 1)) := by
      have hn : 0 < (n : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le hd hdn)
      have hdReal : 0 < (d : ℝ) := by
        exact_mod_cast hd
      have hratio : 0 < (n : ℝ) / (d : ℝ) := by
        positivity
      have hbase : 0 < Real.exp 1 * (n : ℝ) / (d : ℝ) := by
        positivity
      have hbaseEq : Real.exp 1 * (n : ℝ) / (d : ℝ) =
          Real.exp 1 * ((n : ℝ) / (d : ℝ)) := by
        ring
      calc
        (Real.exp 1 * (n : ℝ) / (d : ℝ)) ^ d =
            Real.exp ((d : ℝ) * Real.log (Real.exp 1 * (n : ℝ) / (d : ℝ))) := by
          symm
          rw [Real.exp_nat_mul, Real.exp_log hbase]
        _ = Real.exp ((d : ℝ) * (Real.log ((n : ℝ) / (d : ℝ)) + 1)) := by
          rw [hbaseEq, Real.log_mul (Real.exp_pos _).ne' hratio.ne', Real.log_exp]
          ring_nf

end Statistics
end AppliedModelingLib
