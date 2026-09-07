import AppliedModelingLib.Foundations.Probability.FiniteIID
import AppliedModelingLib.Foundations.Probability.RademacherMatrix
import AppliedModelingLib.Foundations.Probability.UniformHoeffding
import AppliedModelingLib.Learning.Statistics.VC

/-!
# Binary-classification generalization foundations

This module connects iid binary examples to the reusable finite-family
Hoeffding bound.  It proves the finite-class generalization result that is the
concentration base of VC generalization; the later VC argument replaces the
finite class cardinality with a random trace growth bound.
-/

namespace AppliedModelingLib
namespace Statistics

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- The zero-one loss of a binary classifier on one labelled example. -/
noncomputable def binaryClassificationLoss
    {X : Type*} (classifier : BinaryClassifier X) (datum : X × Bool) : ℝ :=
  if classifier datum.1 = datum.2 then 0 else 1

/-- Pointwise Boolean complement of a binary classifier. -/
def binaryComplementClassifier {X : Type*}
    (classifier : BinaryClassifier X) : BinaryClassifier X :=
  fun feature => !classifier feature

/-- Complementing a classifier complements its zero-one loss. -/
theorem binaryClassificationLoss_complement
    {X : Type*} (classifier : BinaryClassifier X) (datum : X × Bool) :
    binaryClassificationLoss (binaryComplementClassifier classifier) datum =
      1 - binaryClassificationLoss classifier datum := by
  unfold binaryClassificationLoss binaryComplementClassifier
  split <;> split <;> simp_all

/-- Binary classification loss always lies in `[0,1]`. -/
theorem binaryClassificationLoss_mem_Icc
    {X : Type*} (classifier : BinaryClassifier X) (datum : X × Bool) :
    binaryClassificationLoss classifier datum ∈ Set.Icc (0 : ℝ) 1 := by
  unfold binaryClassificationLoss
  split <;> norm_num

/-- A measurable binary classifier induces a measurable zero-one loss. -/
theorem measurable_binaryClassificationLoss
    {X : Type*} [MeasurableSpace X] (classifier : BinaryClassifier X)
    (hclassifier : Measurable classifier) :
    Measurable (binaryClassificationLoss classifier) := by
  let truthTable : Bool × Bool → ℝ := fun labels =>
    if labels.1 = labels.2 then 0 else 1
  have htruthTable : Measurable truthTable := measurable_of_finite _
  have hpairs : Measurable (fun datum : X × Bool =>
      (classifier datum.1, datum.2)) :=
    Measurable.prodMk (hclassifier.comp measurable_fst) measurable_snd
  exact htruthTable.comp hpairs

/-- The empirical zero-one error of an arbitrary finite indexed sample. -/
noncomputable def finiteBinaryEmpiricalError
    {X Index : Type*} [Fintype Index] (sample : Index → X × Bool)
    (classifier : BinaryClassifier X) : ℝ :=
  (∑ index, binaryClassificationLoss classifier (sample index)) / (Fintype.card Index : ℝ)

/-- Empirical zero-one error of the complemented classifier. -/
theorem finiteBinaryEmpiricalError_complement
    {X : Type*} (count : ℕ) (hcount : 0 < count)
    (sample : Fin count → X × Bool) (classifier : BinaryClassifier X) :
    finiteBinaryEmpiricalError sample (binaryComplementClassifier classifier) =
      1 - finiteBinaryEmpiricalError sample classifier := by
  unfold finiteBinaryEmpiricalError
  simp_rw [binaryClassificationLoss_complement]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fin]
  have hcountReal : (count : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hcount
  field_simp [hcountReal]

/-- A Boolean-controlled swap chooses the training member of each paired sample. -/
def binarySwappedFirstSample
    {X Index : Type*} (firstSample secondSample : Index → X × Bool) (swap : Index → Bool) :
    Index → X × Bool :=
  fun index => if swap index then firstSample index else secondSample index

/-- The complementary member of each Boolean-controlled paired-sample swap. -/
def binarySwappedSecondSample
    {X Index : Type*} (firstSample secondSample : Index → X × Bool) (swap : Index → Bool) :
    Index → X × Bool :=
  fun index => if swap index then secondSample index else firstSample index

/-- The involutive coordinate permutation that swaps exactly the selected pairs. -/
def binaryPairSwapEquiv {Index : Type*} (swap : Index → Bool) :
    Index ⊕ Index ≃ Index ⊕ Index where
  toFun
    | Sum.inl index => if swap index then Sum.inl index else Sum.inr index
    | Sum.inr index => if swap index then Sum.inr index else Sum.inl index
  invFun
    | Sum.inl index => if swap index then Sum.inl index else Sum.inr index
    | Sum.inr index => if swap index then Sum.inr index else Sum.inl index
  left_inv side := by
    rcases side with index | index <;> cases hswap : swap index <;> simp [hswap]
  right_inv side := by
    rcases side with index | index <;> cases hswap : swap index <;> simp [hswap]

/-- The selected-pair swap as a permutation of a `2 * count` iid sample vector. -/
def binaryPairSwapFinEquiv (count : ℕ) (swap : Fin count → Bool) :
    Fin (count + count) ≃ Fin (count + count) :=
  finSumFinEquiv.symm.trans ((binaryPairSwapEquiv swap).trans finSumFinEquiv)

/-- A Boolean-controlled pair swap preserves the canonical iid double-sample law. -/
theorem measurePreserving_finiteIIDBinaryPairSwap
    {Y : Type*} [MeasurableSpace Y] (law : Measure Y)
    [IsProbabilityMeasure law] (count : ℕ) (swap : Fin count → Bool) :
    MeasurePreserving
      (MeasurableEquiv.piCongrLeft (fun _ : Fin (count + count) => Y)
        (binaryPairSwapFinEquiv count swap))
      (Probability.finiteIIDSampleLaw law (count + count))
      (Probability.finiteIIDSampleLaw law (count + count)) := by
  exact Probability.measurePreserving_finiteIIDSampleReindex law (count + count)
    (binaryPairSwapFinEquiv count swap)

/-- Reindexing a double sample by a selected-pair swap gives its swapped training half. -/
theorem finiteIIDTrainSample_pairSwapReindex_eq_binarySwappedFirst
    {X : Type*} [MeasurableSpace X] (count : ℕ) (swap : Fin count → Bool)
    (sample : Fin (count + count) → X × Bool) :
    Probability.finiteIIDTrainSample count
      (MeasurableEquiv.piCongrLeft (fun _ : Fin (count + count) => X × Bool)
        (binaryPairSwapFinEquiv count swap) sample) =
      binarySwappedFirstSample (Probability.finiteIIDTrainSample count sample)
        (Probability.finiteIIDGhostSample count sample) swap := by
  funext index
  cases hswap : swap index
  · have hpermutation : binaryPairSwapFinEquiv count swap (Fin.natAdd count index) =
        Fin.castAdd count index := by
      simp only [binaryPairSwapFinEquiv, Equiv.trans_apply]
      rw [finSumFinEquiv_symm_apply_natAdd]
      simp [binaryPairSwapEquiv, hswap]
    have happly := MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ : Fin (count + count) => X × Bool) (binaryPairSwapFinEquiv count swap) sample
      (Fin.natAdd count index)
    rw [hpermutation] at happly
    simpa [Probability.finiteIIDTrainSample, Probability.finiteIIDGhostSample,
      binarySwappedFirstSample, hswap] using happly
  · have hpermutation : binaryPairSwapFinEquiv count swap (Fin.castAdd count index) =
        Fin.castAdd count index := by
      simp only [binaryPairSwapFinEquiv, Equiv.trans_apply]
      rw [finSumFinEquiv_symm_apply_castAdd]
      simp [binaryPairSwapEquiv, hswap]
    have happly := MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ : Fin (count + count) => X × Bool) (binaryPairSwapFinEquiv count swap) sample
      (Fin.castAdd count index)
    rw [hpermutation] at happly
    simpa [Probability.finiteIIDTrainSample, Probability.finiteIIDGhostSample,
      binarySwappedFirstSample, hswap] using happly

/-- Reindexing a double sample by a selected-pair swap gives its swapped ghost half. -/
theorem finiteIIDGhostSample_pairSwapReindex_eq_binarySwappedSecond
    {X : Type*} [MeasurableSpace X] (count : ℕ) (swap : Fin count → Bool)
    (sample : Fin (count + count) → X × Bool) :
    Probability.finiteIIDGhostSample count
      (MeasurableEquiv.piCongrLeft (fun _ : Fin (count + count) => X × Bool)
        (binaryPairSwapFinEquiv count swap) sample) =
      binarySwappedSecondSample (Probability.finiteIIDTrainSample count sample)
        (Probability.finiteIIDGhostSample count sample) swap := by
  funext index
  cases hswap : swap index
  · have hpermutation : binaryPairSwapFinEquiv count swap (Fin.castAdd count index) =
        Fin.natAdd count index := by
      simp only [binaryPairSwapFinEquiv, Equiv.trans_apply]
      rw [finSumFinEquiv_symm_apply_castAdd]
      simp [binaryPairSwapEquiv, hswap]
    have happly := MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ : Fin (count + count) => X × Bool) (binaryPairSwapFinEquiv count swap) sample
      (Fin.castAdd count index)
    rw [hpermutation] at happly
    simpa [Probability.finiteIIDTrainSample, Probability.finiteIIDGhostSample,
      binarySwappedSecondSample, hswap] using happly
  · have hpermutation : binaryPairSwapFinEquiv count swap (Fin.natAdd count index) =
        Fin.natAdd count index := by
      simp only [binaryPairSwapFinEquiv, Equiv.trans_apply]
      rw [finSumFinEquiv_symm_apply_natAdd]
      simp [binaryPairSwapEquiv, hswap]
    have happly := MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ : Fin (count + count) => X × Bool) (binaryPairSwapFinEquiv count swap) sample
      (Fin.natAdd count index)
    rw [hpermutation] at happly
    simpa [Probability.finiteIIDTrainSample, Probability.finiteIIDGhostSample,
      binarySwappedSecondSample, hswap] using happly

/-- Apply an auxiliary Boolean pair swap to a canonical iid double sample. -/
noncomputable def finiteIIDPairSwapSample
    {X : Type*} [MeasurableSpace X] (count : ℕ) :
    (Fin (count + count) → X) × (Fin count → Bool) → Fin (count + count) → X :=
  fun pair => MeasurableEquiv.piCongrLeft (fun _ : Fin (count + count) => X)
    (binaryPairSwapFinEquiv count pair.2) pair.1

/--
An iid double sample remains identically distributed after a pair swap chosen
independently from the fair-Boolean product law.  The event's preimage
measurability is explicit, so this result also applies to non-finite classes
once their bad event has a permissible measurability witness.
-/
theorem measureReal_finiteIIDPairSwap_preimage_eq
    {X : Type*} [MeasurableSpace X] (law : Measure X) [IsProbabilityMeasure law]
    (count : ℕ) (event : Set (Fin (count + count) → X))
    (hevent : MeasurableSet event)
    (hpreimage : MeasurableSet {pair | finiteIIDPairSwapSample count pair ∈ event}) :
    ((Probability.finiteIIDSampleLaw law (count + count)).prod
      (FairCoin.productMeasure (Fin count))).real
        {pair | finiteIIDPairSwapSample count pair ∈ event} =
      (Probability.finiteIIDSampleLaw law (count + count)).real event := by
  letI : IsProbabilityMeasure (Probability.finiteIIDSampleLaw law (count + count)) := by
    dsimp [Probability.finiteIIDSampleLaw]
    infer_instance
  letI : IsProbabilityMeasure (FairCoin.productMeasure (Fin count)) :=
    FairCoin.productMeasure_isProbabilityMeasure (Fin count)
  have hsection : ∀ swap : Fin count → Bool,
      (Probability.finiteIIDSampleLaw law (count + count))
        {sample | finiteIIDPairSwapSample count (sample, swap) ∈ event} =
      (Probability.finiteIIDSampleLaw law (count + count)) event := by
    intro swap
    simpa only [finiteIIDPairSwapSample] using
      (measurePreserving_finiteIIDBinaryPairSwap law count swap).measure_preimage
        hevent.nullMeasurableSet
  have hmeasure : (Probability.finiteIIDSampleLaw law (count + count)).prod
      (FairCoin.productMeasure (Fin count))
      {pair | finiteIIDPairSwapSample count pair ∈ event} =
      Probability.finiteIIDSampleLaw law (count + count) event := by
    rw [Measure.prod_apply_symm hpreimage]
    calc
      ∫⁻ swap, (Probability.finiteIIDSampleLaw law (count + count))
          ((fun sample => (sample, swap)) ⁻¹'
            {pair | finiteIIDPairSwapSample count pair ∈ event}) ∂
          FairCoin.productMeasure (Fin count) =
          ∫⁻ _ : Fin count → Bool,
            (Probability.finiteIIDSampleLaw law (count + count)) event ∂
              FairCoin.productMeasure (Fin count) := by
        apply lintegral_congr
        intro swap
        simpa only [Set.preimage] using hsection swap
      _ = Probability.finiteIIDSampleLaw law (count + count) event := by
        simp [lintegral_const]
  simpa only [Measure.real] using congrArg ENNReal.toReal hmeasure

/-- The loss difference of the two members of one paired labelled sample. -/
noncomputable def binaryTwoSampleLossDifference
    {X Index : Type*} (classifier : BinaryClassifier X)
    (firstSample secondSample : Index → X × Bool) (index : Index) : ℝ :=
  binaryClassificationLoss classifier (firstSample index) -
    binaryClassificationLoss classifier (secondSample index)

/-- A binary paired-sample loss difference has absolute value at most one. -/
theorem abs_binaryTwoSampleLossDifference_le_one
    {X Index : Type*} (classifier : BinaryClassifier X)
    (firstSample secondSample : Index → X × Bool) (index : Index) :
    |binaryTwoSampleLossDifference classifier firstSample secondSample index| ≤ 1 := by
  have hfirst := binaryClassificationLoss_mem_Icc classifier (firstSample index)
  have hsecond := binaryClassificationLoss_mem_Icc classifier (secondSample index)
  apply abs_le.2
  constructor <;> unfold binaryTwoSampleLossDifference <;> linarith [hfirst.1, hfirst.2,
    hsecond.1, hsecond.2]

/--
The signed empirical-error gap induced by a Boolean pairwise swap is its
Rademacher sum divided by the number of pairs.
-/
theorem finiteBinaryEmpiricalError_swapGap_eq_rademacher_sum_div
    {X : Type*} (count : ℕ) (hcount : 0 < count) (classifier : BinaryClassifier X)
    (firstSample secondSample : Fin count → X × Bool) (swap : Fin count → Bool) :
    finiteBinaryEmpiricalError (binarySwappedFirstSample firstSample secondSample swap) classifier -
      finiteBinaryEmpiricalError (binarySwappedSecondSample firstSample secondSample swap) classifier =
      (∑ index : Fin count,
        AppliedModelingLib.Probability.RademacherMatrix.rademacherSign (swap index) *
          binaryTwoSampleLossDifference classifier firstSample secondSample index) / (count : ℝ) := by
  have hsum :
      (∑ index : Fin count,
        binaryClassificationLoss classifier
          (binarySwappedFirstSample firstSample secondSample swap index)) -
      ∑ index : Fin count,
        binaryClassificationLoss classifier
          (binarySwappedSecondSample firstSample secondSample swap index) =
      ∑ index : Fin count,
        AppliedModelingLib.Probability.RademacherMatrix.rademacherSign (swap index) *
          binaryTwoSampleLossDifference classifier firstSample secondSample index := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro index _
    cases hswap : swap index <;>
      simp [binarySwappedFirstSample, binarySwappedSecondSample,
        binaryTwoSampleLossDifference, AppliedModelingLib.Probability.RademacherMatrix.rademacherSign, hswap]
  unfold finiteBinaryEmpiricalError
  simp only [Fintype.card_fin]
  rw [← sub_div, hsum]

/--
For a finite classifier family and a fixed pair of labelled samples, a fair
independent swap of each pair obeys the uniform Rademacher empirical-gap tail.
This is a conditional finite-sample statement; it makes no distributional
claim about the paired values themselves.
-/
theorem finite_uniform_binaryTwoSample_swapGap_upperTail
    {X Hypothesis : Type*} [Fintype Hypothesis]
    (count : ℕ) (hcount : 0 < count)
    (classifier : Hypothesis → BinaryClassifier X)
    (firstSample secondSample : Fin count → X × Bool)
    (error : ℝ) (herror : 0 ≤ error) :
    (FairCoin.productMeasure (Fin count)).real {swap | ∃ hypothesis,
      error ≤ finiteBinaryEmpiricalError
        (binarySwappedFirstSample firstSample secondSample swap) (classifier hypothesis) -
        finiteBinaryEmpiricalError
          (binarySwappedSecondSample firstSample secondSample swap) (classifier hypothesis)} ≤
      (Fintype.card Hypothesis : ℝ) *
        Real.exp (-((count : ℝ) * error) ^ 2 / (2 * (count : ℝ))) := by
  let coefficient : Hypothesis → Fin count → ℝ := fun hypothesis index =>
    binaryTwoSampleLossDifference (classifier hypothesis) firstSample secondSample index
  have hcoefficient : ∀ hypothesis index, |coefficient hypothesis index| ≤ 1 := by
    intro hypothesis index
    exact abs_binaryTwoSampleLossDifference_le_one (classifier hypothesis)
      firstSample secondSample index
  have hcount_real_pos : 0 < (count : ℝ) := by
    exact_mod_cast hcount
  have htail :=
    AppliedModelingLib.Probability.RademacherMatrix.measure_exists_sum_weightedSign_ge_le_card_mul_exp_card_of_forall_abs_le_one
      coefficient hcoefficient (ε := (count : ℝ) * error)
      (mul_nonneg hcount_real_pos.le herror)
  have hevent : {swap : Fin count → Bool | ∃ hypothesis,
      error ≤ finiteBinaryEmpiricalError
        (binarySwappedFirstSample firstSample secondSample swap) (classifier hypothesis) -
        finiteBinaryEmpiricalError
          (binarySwappedSecondSample firstSample secondSample swap) (classifier hypothesis)} =
      {swap | ∃ hypothesis, (count : ℝ) * error ≤
        ∑ index : Fin count,
          AppliedModelingLib.Probability.RademacherMatrix.rademacherSign (swap index) *
            coefficient hypothesis index} := by
    ext swap
    constructor
    · rintro ⟨hypothesis, hgap⟩
      refine ⟨hypothesis, ?_⟩
      rw [finiteBinaryEmpiricalError_swapGap_eq_rademacher_sum_div count hcount]
        at hgap
      have hmult := (le_div_iff₀ hcount_real_pos).mp hgap
      simpa [coefficient, mul_comm] using hmult
    · rintro ⟨hypothesis, hsum⟩
      refine ⟨hypothesis, ?_⟩
      rw [finiteBinaryEmpiricalError_swapGap_eq_rademacher_sum_div count hcount]
      apply (le_div_iff₀ hcount_real_pos).mpr
      simpa [coefficient, mul_comm] using hsum
  rw [hevent]
  simpa only [Fintype.card_fin] using htail

/--
The loss transform used for a training/ghost pair: keep a training loss and
complement a ghost loss.  Centering the resulting independent `2N` variables
is the standard fixed-classifier two-sample comparison.
-/
noncomputable def binaryTrainGhostLossTransform
    {X Index : Type*} (classifier : BinaryClassifier X) (side : Index ⊕ Index) :
    X × Bool → ℝ :=
  match side with
  | Sum.inl _ => binaryClassificationLoss classifier
  | Sum.inr _ => fun datum => 1 - binaryClassificationLoss classifier datum

/-- The train/ghost loss transform is measurable for a measurable classifier. -/
theorem measurable_binaryTrainGhostLossTransform
    {X Index : Type*} [MeasurableSpace X] (classifier : BinaryClassifier X)
    (hclassifier : Measurable classifier) (side : Index ⊕ Index) :
    Measurable (binaryTrainGhostLossTransform classifier side) := by
  rcases side with index | index
  · exact measurable_binaryClassificationLoss classifier hclassifier
  · exact measurable_const.sub (measurable_binaryClassificationLoss classifier hclassifier)

/-- The train/ghost loss transform remains `[0,1]`-valued. -/
theorem binaryTrainGhostLossTransform_mem_Icc
    {X Index : Type*} (classifier : BinaryClassifier X) (side : Index ⊕ Index)
    (datum : X × Bool) :
    binaryTrainGhostLossTransform classifier side datum ∈ Set.Icc (0 : ℝ) 1 := by
  rcases side with index | index
  · exact binaryClassificationLoss_mem_Icc classifier datum
  · have hloss := binaryClassificationLoss_mem_Icc classifier datum
    change 1 - binaryClassificationLoss classifier datum ∈ Set.Icc (0 : ℝ) 1
    constructor <;> linarith [hloss.1, hloss.2]

/-- The transformed loss of a side of a canonical train/ghost product sample. -/
noncomputable def finiteIIDTrainGhostLoss
    {X : Type*} (classifier : BinaryClassifier X) (count : ℕ) (side : Fin count ⊕ Fin count) :
    (Fin (count + count) → X × Bool) → ℝ :=
  fun sample => binaryTrainGhostLossTransform classifier side
    (Probability.finiteIIDTrainGhostCoordinate count side sample)

/--
For one fixed measurable classifier, the independent training/ghost losses
obey the finite-index Hoeffding upper tail on the canonical product sample.
This is only the fixed-classifier concentration ingredient; no random-trace
or class-level symmetrization is assumed here.
-/
theorem finiteIIDTrainGhostLoss_centeredSum_upperTail
    {X : Type*} [MeasurableSpace X] (law : Measure (X × Bool))
    [IsProbabilityMeasure law] (count : ℕ) (classifier : BinaryClassifier X)
    (hclassifier : Measurable classifier) (error : ℝ) (herror : 0 ≤ error) :
    (Probability.finiteIIDSampleLaw law (count + count)).real {sample | error ≤
      ∑ side, (finiteIIDTrainGhostLoss classifier count side sample -
        (Probability.finiteIIDSampleLaw law (count + count))[
          finiteIIDTrainGhostLoss classifier count side])} ≤
      Real.exp (-error ^ 2 /
        (2 * (Fintype.card (Fin count ⊕ Fin count) : ℝ) * (1 / 4 : ℝ))) := by
  letI : IsProbabilityMeasure (Probability.finiteIIDSampleLaw law (count + count)) := by
    unfold Probability.finiteIIDSampleLaw
    infer_instance
  let coordinate := Probability.finiteIIDTrainGhostCoordinate (X := X × Bool) count
  let transform : (Fin count ⊕ Fin count) → (X × Bool) → ℝ :=
    binaryTrainGhostLossTransform classifier
  have hindependent : iIndepFun (finiteIIDTrainGhostLoss classifier count)
      (Probability.finiteIIDSampleLaw law (count + count)) := by
    change iIndepFun (fun side => transform side ∘ coordinate side)
      (Probability.finiteIIDSampleLaw law (count + count))
    exact (Probability.iIndepFun_finiteIIDTrainGhostCoordinates law count).comp transform
      (fun side => measurable_binaryTrainGhostLossTransform classifier hclassifier side)
  have hmeasurable : ∀ side, Measurable (finiteIIDTrainGhostLoss classifier count side) := by
    intro side
    change Measurable (transform side ∘ coordinate side)
    exact (measurable_binaryTrainGhostLossTransform classifier hclassifier side).comp
      (Probability.measurable_finiteIIDTrainGhostCoordinate count side)
  have hbounded : ∀ side, ∀ᵐ sample ∂(Probability.finiteIIDSampleLaw law (count + count)),
      finiteIIDTrainGhostLoss classifier count side sample ∈ Set.Icc (0 : ℝ) 1 := by
    intro side
    filter_upwards [] with sample
    exact binaryTrainGhostLossTransform_mem_Icc classifier side (coordinate side sample)
  exact Probability.boundedIIndep_centeredSum_upperTail_finset
    (Probability.finiteIIDSampleLaw law (count + count))
    (finiteIIDTrainGhostLoss classifier count) hindependent hmeasurable hbounded error herror

/-- The product expectation of a transformed split coordinate is its marginal expectation. -/
theorem integral_finiteIIDTrainGhostLoss
    {X : Type*} [MeasurableSpace X] (law : Measure (X × Bool))
    [IsProbabilityMeasure law] (count : ℕ) (classifier : BinaryClassifier X)
    (hclassifier : Measurable classifier) (side : Fin count ⊕ Fin count) :
    (Probability.finiteIIDSampleLaw law (count + count))[
      finiteIIDTrainGhostLoss classifier count side] =
      law[binaryTrainGhostLossTransform classifier side] := by
  letI : IsProbabilityMeasure (Probability.finiteIIDSampleLaw law (count + count)) := by
    unfold Probability.finiteIIDSampleLaw
    infer_instance
  calc
    (Probability.finiteIIDSampleLaw law (count + count))[
        finiteIIDTrainGhostLoss classifier count side] =
        ∫ sample, binaryTrainGhostLossTransform classifier side
          (Probability.finiteIIDTrainGhostCoordinate count side sample)
          ∂(Probability.finiteIIDSampleLaw law (count + count)) := rfl
    _ = (Measure.map (Probability.finiteIIDTrainGhostCoordinate count side)
        (Probability.finiteIIDSampleLaw law (count + count)))[
          binaryTrainGhostLossTransform classifier side] :=
      (integral_map
        (Probability.measurable_finiteIIDTrainGhostCoordinate count side).aemeasurable
        (measurable_binaryTrainGhostLossTransform classifier hclassifier side).aestronglyMeasurable).symm
    _ = law[binaryTrainGhostLossTransform classifier side] := by
      rw [Probability.map_finiteIIDTrainGhostCoordinate law count side]

/-- The left half of a train/ghost loss has the usual loss expectation. -/
theorem integral_finiteIIDTrainGhostLoss_left
    {X : Type*} [MeasurableSpace X] (law : Measure (X × Bool))
    [IsProbabilityMeasure law] (count : ℕ) (classifier : BinaryClassifier X)
    (hclassifier : Measurable classifier) (index : Fin count) :
    (Probability.finiteIIDSampleLaw law (count + count))[
      finiteIIDTrainGhostLoss classifier count (Sum.inl index)] =
      law[binaryClassificationLoss classifier] := by
  rw [integral_finiteIIDTrainGhostLoss law count classifier hclassifier]
  rfl

/-- The right half of a train/ghost loss has the complemented loss expectation. -/
theorem integral_finiteIIDTrainGhostLoss_right
    {X : Type*} [MeasurableSpace X] (law : Measure (X × Bool))
    [IsProbabilityMeasure law] (count : ℕ) (classifier : BinaryClassifier X)
    (hclassifier : Measurable classifier) (index : Fin count) :
    (Probability.finiteIIDSampleLaw law (count + count))[
      finiteIIDTrainGhostLoss classifier count (Sum.inr index)] =
      1 - law[binaryClassificationLoss classifier] := by
  rw [integral_finiteIIDTrainGhostLoss law count classifier hclassifier]
  unfold binaryTrainGhostLossTransform
  have hintegrable : Integrable (binaryClassificationLoss classifier) law :=
    Integrable.of_mem_Icc 0 1
      (measurable_binaryClassificationLoss classifier hclassifier).aemeasurable
      (Filter.Eventually.of_forall fun datum =>
        binaryClassificationLoss_mem_Icc classifier datum)
  rw [integral_sub (integrable_const _) hintegrable]
  simp

/--
The centered train/ghost transformed-loss sum is exactly `count` times the
signed difference between the two empirical errors.
-/
theorem centeredSum_finiteIIDTrainGhostLoss_eq_count_mul_empiricalGap
    {X : Type*} [MeasurableSpace X] (law : Measure (X × Bool))
    [IsProbabilityMeasure law] (count : ℕ) (hcount : 0 < count)
    (classifier : BinaryClassifier X) (hclassifier : Measurable classifier)
    (sample : Fin (count + count) → X × Bool) :
    (∑ side, (finiteIIDTrainGhostLoss classifier count side sample -
      (Probability.finiteIIDSampleLaw law (count + count))[
        finiteIIDTrainGhostLoss classifier count side])) =
      (count : ℝ) *
        (finiteBinaryEmpiricalError (Probability.finiteIIDTrainSample count sample) classifier -
          finiteBinaryEmpiricalError (Probability.finiteIIDGhostSample count sample) classifier) := by
  have hleft : ∀ index : Fin count,
      (Probability.finiteIIDSampleLaw law (count + count))[
        finiteIIDTrainGhostLoss classifier count (Sum.inl index)] =
        law[binaryClassificationLoss classifier] :=
    integral_finiteIIDTrainGhostLoss_left law count classifier hclassifier
  have hright : ∀ index : Fin count,
      (Probability.finiteIIDSampleLaw law (count + count))[
        finiteIIDTrainGhostLoss classifier count (Sum.inr index)] =
        1 - law[binaryClassificationLoss classifier] :=
    integral_finiteIIDTrainGhostLoss_right law count classifier hclassifier
  rw [Fintype.sum_sum_type]
  simp_rw [hleft, hright]
  simp only [finiteIIDTrainGhostLoss, binaryTrainGhostLossTransform,
    Probability.finiteIIDTrainGhostCoordinate, Probability.finiteIIDTrainSample,
    Probability.finiteIIDGhostSample]
  unfold finiteBinaryEmpiricalError
  simp only [Fintype.card_fin, Probability.finiteIIDTrainSample,
    Probability.finiteIIDGhostSample]
  simp_rw [Finset.sum_sub_distrib]
  have hcount_ne : (count : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hcount
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp [hcount_ne]
  ring

/--
For a fixed measurable classifier, two independent iid samples have a
one-sided empirical-error-gap tail of `exp (-N ε²)`.  This is the concentration
step later combined with the finite trace reduction; it does not assert the
class-level ghost-sample symmetrization.
-/
theorem finiteIID_empiricalErrorGap_upperTail
    {X : Type*} [MeasurableSpace X] (law : Measure (X × Bool))
    [IsProbabilityMeasure law] (count : ℕ) (hcount : 0 < count)
    (classifier : BinaryClassifier X) (hclassifier : Measurable classifier)
    (error : ℝ) (herror : 0 ≤ error) :
    (Probability.finiteIIDSampleLaw law (count + count)).real {sample |
      error ≤
        finiteBinaryEmpiricalError (Probability.finiteIIDTrainSample count sample) classifier -
          finiteBinaryEmpiricalError (Probability.finiteIIDGhostSample count sample) classifier} ≤
      Real.exp (-((count : ℝ) * error ^ 2)) := by
  letI : IsProbabilityMeasure (Probability.finiteIIDSampleLaw law (count + count)) := by
    unfold Probability.finiteIIDSampleLaw
    infer_instance
  have hcount_real_pos : 0 < (count : ℝ) := by
    exact_mod_cast hcount
  have htail := finiteIIDTrainGhostLoss_centeredSum_upperTail law count classifier hclassifier
    ((count : ℝ) * error) (mul_nonneg hcount_real_pos.le herror)
  have hevent : {sample : Fin (count + count) → X × Bool |
      error ≤
        finiteBinaryEmpiricalError (Probability.finiteIIDTrainSample count sample) classifier -
          finiteBinaryEmpiricalError (Probability.finiteIIDGhostSample count sample) classifier} =
      {sample | (count : ℝ) * error ≤
        ∑ side, (finiteIIDTrainGhostLoss classifier count side sample -
          (Probability.finiteIIDSampleLaw law (count + count))[
            finiteIIDTrainGhostLoss classifier count side])} := by
    ext sample
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq,
      centeredSum_finiteIIDTrainGhostLoss_eq_count_mul_empiricalGap law count hcount
        classifier hclassifier sample]
    exact (mul_le_mul_iff_of_pos_left hcount_real_pos).symm
  rw [← hevent] at htail
  calc
    (Probability.finiteIIDSampleLaw law (count + count)).real {sample |
        error ≤
          finiteBinaryEmpiricalError (Probability.finiteIIDTrainSample count sample) classifier -
            finiteBinaryEmpiricalError (Probability.finiteIIDGhostSample count sample) classifier} ≤
        Real.exp (-((count : ℝ) * error) ^ 2 /
          (2 * (Fintype.card (Fin count ⊕ Fin count) : ℝ) * (1 / 4 : ℝ))) := htail
    _ = Real.exp (-((count : ℝ) * error ^ 2)) := by
      congr 1
      have hcount_ne : (count : ℝ) ≠ 0 := ne_of_gt hcount_real_pos
      simp only [Fintype.card_sum, Fintype.card_fin]
      norm_num [Nat.cast_mul]
      field_simp [hcount_ne]
      ring

/-- The population zero-one error of a measurable binary classifier. -/
noncomputable def binaryPopulationError
    {X : Type*} [MeasurableSpace X] (law : Measure (X × Bool))
    (classifier : BinaryClassifier X) : ℝ :=
  law[binaryClassificationLoss classifier]

/-- A measurable classifier has a measurable Boolean complement. -/
theorem measurable_binaryComplementClassifier
    {X : Type*} [MeasurableSpace X] (classifier : BinaryClassifier X)
    (hclassifier : Measurable classifier) :
    Measurable (binaryComplementClassifier classifier) := by
  exact (measurable_of_finite Bool.not).comp hclassifier

/-- Population zero-one error of the complemented classifier. -/
theorem binaryPopulationError_complement
    {X : Type*} [MeasurableSpace X] (law : Measure (X × Bool))
    [IsProbabilityMeasure law] (classifier : BinaryClassifier X)
    (hclassifier : Measurable classifier) :
    binaryPopulationError law (binaryComplementClassifier classifier) =
      1 - binaryPopulationError law classifier := by
  unfold binaryPopulationError
  rw [show binaryClassificationLoss (binaryComplementClassifier classifier) =
      fun datum => 1 - binaryClassificationLoss classifier datum by
        funext datum
        exact binaryClassificationLoss_complement classifier datum]
  have hintegrable : Integrable (binaryClassificationLoss classifier) law :=
    Integrable.of_mem_Icc 0 1
      (measurable_binaryClassificationLoss classifier hclassifier).aemeasurable
      (Filter.Eventually.of_forall fun datum =>
        binaryClassificationLoss_mem_Icc classifier datum)
  rw [integral_sub (integrable_const _) hintegrable]
  simp

/--
The ghost half of a canonical iid double sample has the usual one-sided
Hoeffding lower tail about a fixed classifier's population error.
-/
theorem finiteIIDGhost_empiricalError_population_lowerTail
    {X : Type*} [MeasurableSpace X] (law : Measure (X × Bool))
    [IsProbabilityMeasure law] (count : ℕ) (hcount : 0 < count)
    (classifier : BinaryClassifier X) (hclassifier : Measurable classifier)
    (error : ℝ) (herror : 0 ≤ error) :
    (Probability.finiteIIDSampleLaw law (count + count)).real {sample |
      finiteBinaryEmpiricalError (Probability.finiteIIDGhostSample count sample) classifier ≤
        binaryPopulationError law classifier - error} ≤
      Real.exp (-((count : ℝ) * error) ^ 2 /
        (2 * (count : ℝ) * (1 / 4 : ℝ))) := by
  letI : IsProbabilityMeasure (Probability.finiteIIDSampleLaw law (count + count)) := by
    dsimp [Probability.finiteIIDSampleLaw]
    infer_instance
  let observation : Fin count → (Fin (count + count) → X × Bool) → ℝ :=
    fun index sample => binaryClassificationLoss classifier
      (Probability.finiteIIDGhostSample count sample index)
  have hcoordinate_independent : iIndepFun
      (fun index : Fin count =>
        Probability.finiteIIDTrainGhostCoordinate (X := X × Bool) count (Sum.inr index))
      (Probability.finiteIIDSampleLaw law (count + count)) :=
    (Probability.iIndepFun_finiteIIDTrainGhostCoordinates law count).precomp
      Sum.inr_injective
  have hindependent : iIndepFun observation
      (Probability.finiteIIDSampleLaw law (count + count)) := by
    simpa only [observation, Probability.finiteIIDTrainGhostCoordinate] using
      hcoordinate_independent.comp
        (fun _ datum => binaryClassificationLoss classifier datum)
        (fun _ => measurable_binaryClassificationLoss classifier hclassifier)
  have hmeasurable : ∀ index, Measurable (observation index) := by
    intro index
    exact (measurable_binaryClassificationLoss classifier hclassifier).comp
      (measurable_pi_apply _)
  have hbounded : ∀ index, ∀ᵐ sample ∂(Probability.finiteIIDSampleLaw law (count + count)),
      observation index sample ∈ Set.Icc (0 : ℝ) 1 := by
    intro index
    filter_upwards [] with sample
    exact binaryClassificationLoss_mem_Icc classifier
      (Probability.finiteIIDGhostSample count sample index)
  have hmean : ∀ index,
      (Probability.finiteIIDSampleLaw law (count + count))[observation index] =
        binaryPopulationError law classifier := by
    intro index
    calc
      (Probability.finiteIIDSampleLaw law (count + count))[observation index] =
          ∫ sample,
            binaryClassificationLoss classifier
              (Probability.finiteIIDGhostSample count sample index) ∂
              (Probability.finiteIIDSampleLaw law (count + count)) := rfl
      _ = (Measure.map (fun sample => Probability.finiteIIDGhostSample count sample index)
            (Probability.finiteIIDSampleLaw law (count + count)))[
              binaryClassificationLoss classifier] := by
          symm
          apply integral_map
          · exact (measurable_pi_apply (Fin.natAdd count index)).aemeasurable
          · exact (measurable_binaryClassificationLoss classifier hclassifier).aestronglyMeasurable
      _ = binaryPopulationError law classifier := by
          rw [Probability.map_finiteIIDGhostSampleCoordinate law count index]
          rfl
  have hcount_real_pos : 0 < (count : ℝ) := by exact_mod_cast hcount
  have hcentered : ∀ sample,
      (∑ index, (observation index sample -
        (Probability.finiteIIDSampleLaw law (count + count))[observation index])) =
        (∑ index, observation index sample) -
          (count : ℝ) * binaryPopulationError law classifier := by
    intro sample
    rw [Finset.sum_sub_distrib]
    simp_rw [hmean]
    simp
  have hevent : {sample |
      finiteBinaryEmpiricalError (Probability.finiteIIDGhostSample count sample) classifier ≤
        binaryPopulationError law classifier - error} =
      {sample | ∑ index, (observation index sample -
        (Probability.finiteIIDSampleLaw law (count + count))[observation index]) ≤
          -((count : ℝ) * error)} := by
    ext sample
    change (finiteBinaryEmpiricalError
      (Probability.finiteIIDGhostSample count sample) classifier ≤
        binaryPopulationError law classifier - error) ↔
      (∑ index, (observation index sample -
        (Probability.finiteIIDSampleLaw law (count + count))[observation index])) ≤
        -((count : ℝ) * error)
    rw [hcentered sample]
    unfold finiteBinaryEmpiricalError
    simp only [Fintype.card_fin]
    change (∑ index, observation index sample) / (count : ℝ) ≤
        binaryPopulationError law classifier - error ↔
      (∑ index, observation index sample) -
          (count : ℝ) * binaryPopulationError law classifier ≤
        -((count : ℝ) * error)
    constructor
    · intro h
      have hmult := (div_le_iff₀ hcount_real_pos).mp h
      nlinarith
    · intro h
      apply (div_le_iff₀ hcount_real_pos).mpr
      nlinarith
  rw [hevent]
  simpa only [Fintype.card_fin] using
    Probability.boundedIIndep_centeredSum_lowerTail_finset
    (Probability.finiteIIDSampleLaw law (count + count)) observation hindependent
    hmeasurable hbounded ((count : ℝ) * error) (mul_nonneg hcount_real_pos.le herror)

/--
For a fixed classifier, the ghost empirical error exceeds the population
error minus `error` except on its checked lower-tail event.
-/
theorem finiteIIDGhost_population_sub_lt_empiricalError_probability_lower
    {X : Type*} [MeasurableSpace X] (law : Measure (X × Bool))
    [IsProbabilityMeasure law] (count : ℕ) (hcount : 0 < count)
    (classifier : BinaryClassifier X) (hclassifier : Measurable classifier)
    (error : ℝ) (herror : 0 ≤ error) :
    1 - Real.exp (-((count : ℝ) * error) ^ 2 /
        (2 * (count : ℝ) * (1 / 4 : ℝ))) ≤
      (Probability.finiteIIDSampleLaw law (count + count)).real {sample |
        binaryPopulationError law classifier - error <
          finiteBinaryEmpiricalError (Probability.finiteIIDGhostSample count sample) classifier} := by
  letI : IsProbabilityMeasure (Probability.finiteIIDSampleLaw law (count + count)) := by
    dsimp [Probability.finiteIIDSampleLaw]
    infer_instance
  let bad : Set (Fin (count + count) → X × Bool) := {sample |
    finiteBinaryEmpiricalError (Probability.finiteIIDGhostSample count sample) classifier ≤
      binaryPopulationError law classifier - error}
  let good : Set (Fin (count + count) → X × Bool) := {sample |
    binaryPopulationError law classifier - error <
      finiteBinaryEmpiricalError (Probability.finiteIIDGhostSample count sample) classifier}
  have hbad := finiteIIDGhost_empiricalError_population_lowerTail law count hcount
    classifier hclassifier error herror
  have hunion : bad ∪ good = Set.univ := by
    ext sample
    change
      (finiteBinaryEmpiricalError (Probability.finiteIIDGhostSample count sample) classifier ≤
        binaryPopulationError law classifier - error) ∨
      (binaryPopulationError law classifier - error <
        finiteBinaryEmpiricalError (Probability.finiteIIDGhostSample count sample) classifier) ↔ True
    constructor
    · intro _
      trivial
    · intro _
      exact le_or_gt _ _
  have hcover := measureReal_union_le (μ := Probability.finiteIIDSampleLaw law (count + count))
    bad good
  rw [hunion, MeasureTheory.probReal_univ] at hcover
  change 1 - Real.exp (-((count : ℝ) * error) ^ 2 /
      (2 * (count : ℝ) * (1 / 4 : ℝ))) ≤
    (Probability.finiteIIDSampleLaw law (count + count)).real good
  change (Probability.finiteIIDSampleLaw law (count + count)).real bad ≤
    Real.exp (-((count : ℝ) * error) ^ 2 /
      (2 * (count : ℝ) * (1 / 4 : ℝ))) at hbad
  nlinarith

/-- A single canonical iid sample has the fixed-classifier lower Hoeffding tail. -/
theorem finiteIID_empiricalError_population_lowerTail
    {X : Type*} [MeasurableSpace X] (law : Measure (X × Bool))
    [IsProbabilityMeasure law] (count : ℕ) (hcount : 0 < count)
    (classifier : BinaryClassifier X) (hclassifier : Measurable classifier)
    (error : ℝ) (herror : 0 ≤ error) :
    (Probability.finiteIIDSampleLaw law count).real {sample |
      finiteBinaryEmpiricalError sample classifier ≤ binaryPopulationError law classifier - error} ≤
      Real.exp (-((count : ℝ) * error) ^ 2 /
        (2 * (count : ℝ) * (1 / 4 : ℝ))) := by
  letI : IsProbabilityMeasure (Probability.finiteIIDSampleLaw law count) := by
    dsimp [Probability.finiteIIDSampleLaw]
    infer_instance
  let observation : Fin count → (Fin count → X × Bool) → ℝ := fun index sample =>
    binaryClassificationLoss classifier (sample index)
  have hindependent : iIndepFun observation (Probability.finiteIIDSampleLaw law count) := by
    simpa only [observation, Probability.finiteIIDSampleCoordinate] using
      (Probability.iIndepFun_finiteIIDSampleCoordinate law count).comp
        (fun _ datum => binaryClassificationLoss classifier datum)
        (fun _ => measurable_binaryClassificationLoss classifier hclassifier)
  have hmeasurable : ∀ index, Measurable (observation index) := by
    intro index
    exact (measurable_binaryClassificationLoss classifier hclassifier).comp (measurable_pi_apply _)
  have hbounded : ∀ index, ∀ᵐ sample ∂(Probability.finiteIIDSampleLaw law count),
      observation index sample ∈ Set.Icc (0 : ℝ) 1 := by
    intro index
    filter_upwards [] with sample
    exact binaryClassificationLoss_mem_Icc classifier (sample index)
  have hmean : ∀ index, (Probability.finiteIIDSampleLaw law count)[observation index] =
      binaryPopulationError law classifier := by
    intro index
    calc
      (Probability.finiteIIDSampleLaw law count)[observation index] =
          (Measure.map (fun sample => sample index) (Probability.finiteIIDSampleLaw law count))[
            binaryClassificationLoss classifier] := by
          symm
          apply integral_map
          · exact (measurable_pi_apply index).aemeasurable
          · exact (measurable_binaryClassificationLoss classifier hclassifier).aestronglyMeasurable
      _ = binaryPopulationError law classifier := by
          change ∫ x, binaryClassificationLoss classifier x ∂
            Measure.map (Probability.finiteIIDSampleCoordinate index)
              (Probability.finiteIIDSampleLaw law count) = binaryPopulationError law classifier
          rw [Probability.map_finiteIIDSampleCoordinate law count index]
          rfl
  have hcount_real_pos : 0 < (count : ℝ) := by exact_mod_cast hcount
  have hcentered : ∀ sample,
      (∑ index, (observation index sample -
        (Probability.finiteIIDSampleLaw law count)[observation index])) =
      (∑ index, observation index sample) - (count : ℝ) * binaryPopulationError law classifier := by
    intro sample
    rw [Finset.sum_sub_distrib]
    simp_rw [hmean]
    simp
  have hevent : {sample |
      finiteBinaryEmpiricalError sample classifier ≤ binaryPopulationError law classifier - error} =
      {sample | ∑ index, (observation index sample -
        (Probability.finiteIIDSampleLaw law count)[observation index]) ≤ -((count : ℝ) * error)} := by
    ext sample
    change (finiteBinaryEmpiricalError sample classifier ≤
      binaryPopulationError law classifier - error) ↔
      (∑ index, (observation index sample -
        (Probability.finiteIIDSampleLaw law count)[observation index]) ≤ -((count : ℝ) * error))
    rw [hcentered sample]
    unfold finiteBinaryEmpiricalError
    simp only [Fintype.card_fin]
    change (∑ index, observation index sample) / (count : ℝ) ≤
      binaryPopulationError law classifier - error ↔
      (∑ index, observation index sample) -
        (count : ℝ) * binaryPopulationError law classifier ≤ -((count : ℝ) * error)
    constructor
    · intro h
      have hmult := (div_le_iff₀ hcount_real_pos).mp h
      nlinarith
    · intro h
      apply (div_le_iff₀ hcount_real_pos).mpr
      nlinarith
  rw [hevent]
  simpa only [Fintype.card_fin] using
    Probability.boundedIIndep_centeredSum_lowerTail_finset
      (Probability.finiteIIDSampleLaw law count) observation hindependent
      hmeasurable hbounded ((count : ℝ) * error) (mul_nonneg hcount_real_pos.le herror)

/-- A single canonical iid sample has the fixed-classifier upper Hoeffding tail. -/
theorem finiteIID_empiricalError_population_upperTail
    {X : Type*} [MeasurableSpace X] (law : Measure (X × Bool))
    [IsProbabilityMeasure law] (count : ℕ) (hcount : 0 < count)
    (classifier : BinaryClassifier X) (hclassifier : Measurable classifier)
    (error : ℝ) (herror : 0 ≤ error) :
    (Probability.finiteIIDSampleLaw law count).real {sample |
      binaryPopulationError law classifier + error ≤
        finiteBinaryEmpiricalError sample classifier} ≤
      Real.exp (-((count : ℝ) * error) ^ 2 /
        (2 * (count : ℝ) * (1 / 4 : ℝ))) := by
  letI : IsProbabilityMeasure (Probability.finiteIIDSampleLaw law count) := by
    dsimp [Probability.finiteIIDSampleLaw]
    infer_instance
  have hcomplementMeasurable :=
    measurable_binaryComplementClassifier classifier hclassifier
  have htail := finiteIID_empiricalError_population_lowerTail law count hcount
    (binaryComplementClassifier classifier) hcomplementMeasurable error herror
  have hevent : ({sample : Fin count → X × Bool |
      binaryPopulationError law classifier + error ≤
        finiteBinaryEmpiricalError sample classifier} : Set (Fin count → X × Bool)) =
      {sample | finiteBinaryEmpiricalError sample (binaryComplementClassifier classifier) ≤
        binaryPopulationError law (binaryComplementClassifier classifier) - error} := by
    ext sample
    change binaryPopulationError law classifier + error ≤
        finiteBinaryEmpiricalError sample classifier ↔
      finiteBinaryEmpiricalError sample (binaryComplementClassifier classifier) ≤
        binaryPopulationError law (binaryComplementClassifier classifier) - error
    rw [finiteBinaryEmpiricalError_complement count hcount sample classifier,
      binaryPopulationError_complement law classifier hclassifier]
    constructor <;> intro h <;> linarith
  rw [hevent]
  exact htail

/-- The favorable lower-side population-to-empirical section for one iid sample. -/
theorem finiteIID_population_sub_lt_empiricalError_probability_lower
    {X : Type*} [MeasurableSpace X] (law : Measure (X × Bool))
    [IsProbabilityMeasure law] (count : ℕ) (hcount : 0 < count)
    (classifier : BinaryClassifier X) (hclassifier : Measurable classifier)
    (error : ℝ) (herror : 0 ≤ error) :
    1 - Real.exp (-((count : ℝ) * error) ^ 2 /
        (2 * (count : ℝ) * (1 / 4 : ℝ))) ≤
      (Probability.finiteIIDSampleLaw law count).real {sample |
        binaryPopulationError law classifier - error < finiteBinaryEmpiricalError sample classifier} := by
  letI : IsProbabilityMeasure (Probability.finiteIIDSampleLaw law count) := by
    dsimp [Probability.finiteIIDSampleLaw]
    infer_instance
  let bad : Set (Fin count → X × Bool) := {sample |
    finiteBinaryEmpiricalError sample classifier ≤ binaryPopulationError law classifier - error}
  let good : Set (Fin count → X × Bool) := {sample |
    binaryPopulationError law classifier - error < finiteBinaryEmpiricalError sample classifier}
  have hbad := finiteIID_empiricalError_population_lowerTail law count hcount
    classifier hclassifier error herror
  have hunion : bad ∪ good = Set.univ := by
    ext sample
    change (finiteBinaryEmpiricalError sample classifier ≤
      binaryPopulationError law classifier - error) ∨
      (binaryPopulationError law classifier - error < finiteBinaryEmpiricalError sample classifier) ↔ True
    constructor
    · intro _
      trivial
    · intro _
      exact le_or_gt _ _
  have hcover := measureReal_union_le (μ := Probability.finiteIIDSampleLaw law count) bad good
  rw [hunion, MeasureTheory.probReal_univ] at hcover
  change 1 - Real.exp (-((count : ℝ) * error) ^ 2 /
      (2 * (count : ℝ) * (1 / 4 : ℝ))) ≤
    (Probability.finiteIIDSampleLaw law count).real good
  change (Probability.finiteIIDSampleLaw law count).real bad ≤
    Real.exp (-((count : ℝ) * error) ^ 2 /
      (2 * (count : ℝ) * (1 / 4 : ℝ))) at hbad
  nlinarith

/-- The favorable upper-side empirical-to-population section for one iid sample. -/
theorem finiteIID_empiricalError_lt_population_add_probability_lower
    {X : Type*} [MeasurableSpace X] (law : Measure (X × Bool))
    [IsProbabilityMeasure law] (count : ℕ) (hcount : 0 < count)
    (classifier : BinaryClassifier X) (hclassifier : Measurable classifier)
    (error : ℝ) (herror : 0 ≤ error) :
    1 - Real.exp (-((count : ℝ) * error) ^ 2 /
        (2 * (count : ℝ) * (1 / 4 : ℝ))) ≤
      (Probability.finiteIIDSampleLaw law count).real {sample |
        finiteBinaryEmpiricalError sample classifier <
          binaryPopulationError law classifier + error} := by
  letI : IsProbabilityMeasure (Probability.finiteIIDSampleLaw law count) := by
    dsimp [Probability.finiteIIDSampleLaw]
    infer_instance
  let bad : Set (Fin count → X × Bool) := {sample |
    binaryPopulationError law classifier + error ≤
      finiteBinaryEmpiricalError sample classifier}
  let good : Set (Fin count → X × Bool) := {sample |
    finiteBinaryEmpiricalError sample classifier <
      binaryPopulationError law classifier + error}
  have hbad := finiteIID_empiricalError_population_upperTail law count hcount
    classifier hclassifier error herror
  have hunion : bad ∪ good = Set.univ := by
    ext sample
    change
      (binaryPopulationError law classifier + error ≤
        finiteBinaryEmpiricalError sample classifier) ∨
      (finiteBinaryEmpiricalError sample classifier <
        binaryPopulationError law classifier + error) ↔ True
    constructor
    · intro _
      trivial
    · intro _
      exact le_or_gt _ _
  have hcover := measureReal_union_le (μ := Probability.finiteIIDSampleLaw law count) bad good
  rw [hunion, MeasureTheory.probReal_univ] at hcover
  change 1 - Real.exp (-((count : ℝ) * error) ^ 2 /
      (2 * (count : ℝ) * (1 / 4 : ℝ))) ≤
    (Probability.finiteIIDSampleLaw law count).real good
  change (Probability.finiteIIDSampleLaw law count).real bad ≤
    Real.exp (-((count : ℝ) * error) ^ 2 /
      (2 * (count : ℝ) * (1 / 4 : ℝ))) at hbad
  nlinarith

/--
Agreement of two classifiers on a finite feature sample gives identical
zero-one losses on every labelled observation from that sample.
-/
theorem binaryClassificationLoss_eq_of_agreeOn
    {X : Type*} {sample : Finset X} {first second : BinaryClassifier X}
    (hagrees : BinaryClassifiersAgreeOn sample first second)
    (datum : X × Bool) (hdatum : datum.1 ∈ sample) :
    binaryClassificationLoss first datum = binaryClassificationLoss second datum := by
  unfold binaryClassificationLoss
  rw [hagrees datum.1 hdatum]

/--
Agreement on a support containing every feature of a finite labelled sample
preserves its empirical error.
-/
theorem finiteBinaryEmpiricalError_eq_of_agreeOn
    {X Index : Type*} [Fintype Index] (sample : Index → X × Bool)
    (support : Finset X) {first second : BinaryClassifier X}
    (hagrees : BinaryClassifiersAgreeOn support first second)
    (hsupport : ∀ index, (sample index).1 ∈ support) :
    finiteBinaryEmpiricalError sample first = finiteBinaryEmpiricalError sample second := by
  unfold finiteBinaryEmpiricalError
  congr 1
  apply Finset.sum_congr rfl
  intro index _
  exact binaryClassificationLoss_eq_of_agreeOn hagrees (sample index) (hsupport index)

/-- The support of the features appearing in either of two indexed labelled samples. -/
noncomputable def binaryTwoSampleFeatureSupport
    {X Index : Type*} [Fintype Index]
    (firstSample secondSample : Index → X × Bool) : Finset X :=
  finiteFeatureSupport (fun side : Sum Index Index =>
    match side with
    | Sum.inl index => (firstSample index).1
    | Sum.inr index => (secondSample index).1)

/-- Expand the two-sample support as the support of its summed index family. -/
theorem binaryTwoSampleFeatureSupport_eq_finiteFeatureSupport
    {X Index : Type*} [Fintype Index]
    (firstSample secondSample : Index → X × Bool) :
    binaryTwoSampleFeatureSupport firstSample secondSample =
      finiteFeatureSupport (fun side : Sum Index Index =>
        match side with
        | Sum.inl index => (firstSample index).1
        | Sum.inr index => (secondSample index).1) := by
  unfold binaryTwoSampleFeatureSupport
  rfl

/-- Every feature in the left sample belongs to the two-sample support. -/
theorem mem_binaryTwoSampleFeatureSupport_left
    {X Index : Type*} [Fintype Index]
    (firstSample secondSample : Index → X × Bool) (index : Index) :
    (firstSample index).1 ∈ binaryTwoSampleFeatureSupport firstSample secondSample := by
  simpa [binaryTwoSampleFeatureSupport] using
    (mem_finiteFeatureSupport
      (fun side : Sum Index Index =>
        match side with
        | Sum.inl index => (firstSample index).1
        | Sum.inr index => (secondSample index).1)
      (Sum.inl index))

/-- Every feature in the right sample belongs to the two-sample support. -/
theorem mem_binaryTwoSampleFeatureSupport_right
    {X Index : Type*} [Fintype Index]
    (firstSample secondSample : Index → X × Bool) (index : Index) :
    (secondSample index).1 ∈ binaryTwoSampleFeatureSupport firstSample secondSample := by
  simpa [binaryTwoSampleFeatureSupport] using
    (mem_finiteFeatureSupport
      (fun side : Sum Index Index =>
        match side with
        | Sum.inl index => (firstSample index).1
        | Sum.inr index => (secondSample index).1)
      (Sum.inr index))

/--
On a fixed pair of finite labelled samples, every classifier in an arbitrary
concept class has a trace representative with exactly the same two empirical
errors.
-/
theorem exists_binaryTraceRepresentative_twoSample_empiricalErrors
    {X Index : Type*} [Fintype Index] {concepts : Set (BinaryClassifier X)}
    {classifier : BinaryClassifier X} (hclassifier : classifier ∈ concepts)
    (firstSample secondSample : Index → X × Bool) :
    ∃ labels : BinaryTraceRepresentativeIndex concepts
        (binaryTwoSampleFeatureSupport firstSample secondSample),
      finiteBinaryEmpiricalError firstSample classifier =
          finiteBinaryEmpiricalError firstSample
            (classifierOfBinaryTrace concepts
              (binaryTwoSampleFeatureSupport firstSample secondSample) labels.1) ∧
        finiteBinaryEmpiricalError secondSample classifier =
          finiteBinaryEmpiricalError secondSample
            (classifierOfBinaryTrace concepts
              (binaryTwoSampleFeatureSupport firstSample secondSample) labels.1) := by
  rcases exists_binaryTraceRepresentative_agreesOn hclassifier
    (binaryTwoSampleFeatureSupport firstSample secondSample) with ⟨labels, hagrees⟩
  refine ⟨labels, ?_, ?_⟩
  · exact finiteBinaryEmpiricalError_eq_of_agreeOn firstSample
      (binaryTwoSampleFeatureSupport firstSample secondSample) hagrees
      (mem_binaryTwoSampleFeatureSupport_left firstSample secondSample)
  · exact finiteBinaryEmpiricalError_eq_of_agreeOn secondSample
      (binaryTwoSampleFeatureSupport firstSample secondSample) hagrees
      (mem_binaryTwoSampleFeatureSupport_right firstSample secondSample)

/--
The two-sample empirical-gap event for an arbitrary class is witnessed by a
finite trace representative on the combined feature support.
-/
theorem exists_binaryTraceRepresentative_twoSample_empiricalGap
    {X Index : Type*} [Fintype Index] {concepts : Set (BinaryClassifier X)}
    {classifier : BinaryClassifier X} (hclassifier : classifier ∈ concepts)
    (firstSample secondSample : Index → X × Bool) (error : ℝ)
    (hgap : error < |finiteBinaryEmpiricalError firstSample classifier -
      finiteBinaryEmpiricalError secondSample classifier|) :
    ∃ labels : BinaryTraceRepresentativeIndex concepts
        (binaryTwoSampleFeatureSupport firstSample secondSample),
      error < |finiteBinaryEmpiricalError firstSample
          (classifierOfBinaryTrace concepts
            (binaryTwoSampleFeatureSupport firstSample secondSample) labels.1) -
        finiteBinaryEmpiricalError secondSample
          (classifierOfBinaryTrace concepts
            (binaryTwoSampleFeatureSupport firstSample secondSample) labels.1)| := by
  rcases exists_binaryTraceRepresentative_twoSample_empiricalErrors hclassifier
    firstSample secondSample with ⟨labels, hfirst, hsecond⟩
  refine ⟨labels, ?_⟩
  rw [← hfirst, ← hsecond]
  exact hgap

/--
The finite representative family on a pair of `count`-point samples has the
Sauer--Shelah cardinality bound for a VC-dimension-`d` concept class.  The
combined support has at most `2 * count` distinct feature values, even if the
two samples contain repeats.
-/
theorem card_binaryTraceRepresentative_twoSample_le_vcGrowth
    {X : Type*} {concepts : Set (BinaryClassifier X)} {d count : ℕ}
    (hvc : VCDimensionAtMost concepts d)
    (firstSample secondSample : Fin count → X × Bool) :
    Fintype.card (BinaryTraceRepresentativeIndex concepts
      (binaryTwoSampleFeatureSupport firstSample secondSample)) ≤
      ∑ k ∈ Finset.Iic d, (count + count).choose k := by
  calc
    Fintype.card (BinaryTraceRepresentativeIndex concepts
        (binaryTwoSampleFeatureSupport firstSample secondSample)) =
        binaryGrowth concepts (binaryTwoSampleFeatureSupport firstSample secondSample) :=
      card_binaryTraceRepresentativeIndex_eq_growth concepts _
    _ ≤ ∑ k ∈ Finset.Iic d, (Fintype.card (Fin count ⊕ Fin count)).choose k := by
      rw [binaryTwoSampleFeatureSupport_eq_finiteFeatureSupport]
      apply binaryGrowth_finiteFeatureSupport_le_sum_choose_of_vcDimensionAtMost hvc
    _ = ∑ k ∈ Finset.Iic d, (count + count).choose k := by simp

/--
For a fixed pair of `count`-point samples, the Boolean pair-swap tail extends
from a finite classifier family to an arbitrary VC class by replacing it with
its finite trace family on the combined sample support.
-/
theorem finite_uniform_binaryTwoSample_swapGap_upperTail_vc
    {X : Type*} [MeasurableSpace X] {concepts : Set (BinaryClassifier X)}
    {d count : ℕ} (hvc : VCDimensionAtMost concepts d) (hcount : 0 < count)
    (firstSample secondSample : Fin count → X × Bool)
    (error : ℝ) (herror : 0 ≤ error) :
    (FairCoin.productMeasure (Fin count)).real {swap | ∃ classifier,
      classifier ∈ concepts ∧
      error ≤ finiteBinaryEmpiricalError
        (binarySwappedFirstSample firstSample secondSample swap) classifier -
        finiteBinaryEmpiricalError
          (binarySwappedSecondSample firstSample secondSample swap) classifier} ≤
      (∑ k ∈ Finset.Iic d, (count + count).choose k : ℝ) *
        Real.exp (-((count : ℝ) * error) ^ 2 / (2 * (count : ℝ))) := by
  let support := binaryTwoSampleFeatureSupport firstSample secondSample
  let representativeClassifier : BinaryTraceRepresentativeIndex concepts support →
      BinaryClassifier X := fun labels => classifierOfBinaryTrace concepts support labels.1
  letI : IsProbabilityMeasure (FairCoin.productMeasure (Fin count)) :=
    FairCoin.productMeasure_isProbabilityMeasure (Fin count)
  have hsubset : {swap | ∃ classifier,
      classifier ∈ concepts ∧
      error ≤ finiteBinaryEmpiricalError
        (binarySwappedFirstSample firstSample secondSample swap) classifier -
        finiteBinaryEmpiricalError
          (binarySwappedSecondSample firstSample secondSample swap) classifier} ⊆
      {swap | ∃ labels : BinaryTraceRepresentativeIndex concepts support,
        error ≤ finiteBinaryEmpiricalError
          (binarySwappedFirstSample firstSample secondSample swap)
            (representativeClassifier labels) -
          finiteBinaryEmpiricalError
            (binarySwappedSecondSample firstSample secondSample swap)
              (representativeClassifier labels)} := by
    intro swap hswap
    rcases hswap with ⟨classifier, hclassifier, hgap⟩
    rcases exists_binaryTraceRepresentative_agreesOn hclassifier support with ⟨labels, hagrees⟩
    have hfirst : finiteBinaryEmpiricalError
        (binarySwappedFirstSample firstSample secondSample swap) classifier =
        finiteBinaryEmpiricalError
          (binarySwappedFirstSample firstSample secondSample swap)
            (representativeClassifier labels) := by
      apply finiteBinaryEmpiricalError_eq_of_agreeOn
        (binarySwappedFirstSample firstSample secondSample swap) support hagrees
      intro index
      cases hswap : swap index
      · simpa [binarySwappedFirstSample, hswap, support] using
          mem_binaryTwoSampleFeatureSupport_right firstSample secondSample index
      · simpa [binarySwappedFirstSample, hswap, support] using
          mem_binaryTwoSampleFeatureSupport_left firstSample secondSample index
    have hsecond : finiteBinaryEmpiricalError
        (binarySwappedSecondSample firstSample secondSample swap) classifier =
        finiteBinaryEmpiricalError
          (binarySwappedSecondSample firstSample secondSample swap)
            (representativeClassifier labels) := by
      apply finiteBinaryEmpiricalError_eq_of_agreeOn
        (binarySwappedSecondSample firstSample secondSample swap) support hagrees
      intro index
      cases hswap : swap index
      · simpa [binarySwappedSecondSample, hswap, support] using
          mem_binaryTwoSampleFeatureSupport_left firstSample secondSample index
      · simpa [binarySwappedSecondSample, hswap, support] using
          mem_binaryTwoSampleFeatureSupport_right firstSample secondSample index
    refine ⟨labels, ?_⟩
    simpa only [hfirst, hsecond] using hgap
  have htail := finite_uniform_binaryTwoSample_swapGap_upperTail count hcount
    representativeClassifier firstSample secondSample error herror
  have hcard := card_binaryTraceRepresentative_twoSample_le_vcGrowth hvc
    firstSample secondSample
  calc
    (FairCoin.productMeasure (Fin count)).real {swap | ∃ classifier,
        classifier ∈ concepts ∧
        error ≤ finiteBinaryEmpiricalError
          (binarySwappedFirstSample firstSample secondSample swap) classifier -
          finiteBinaryEmpiricalError
            (binarySwappedSecondSample firstSample secondSample swap) classifier} ≤
        (FairCoin.productMeasure (Fin count)).real
          {swap | ∃ labels : BinaryTraceRepresentativeIndex concepts support,
            error ≤ finiteBinaryEmpiricalError
              (binarySwappedFirstSample firstSample secondSample swap)
                (representativeClassifier labels) -
              finiteBinaryEmpiricalError
                (binarySwappedSecondSample firstSample secondSample swap)
                  (representativeClassifier labels)} :=
      measureReal_mono hsubset (measure_ne_top _ _)
    _ ≤ (Fintype.card (BinaryTraceRepresentativeIndex concepts support) : ℝ) *
        Real.exp (-((count : ℝ) * error) ^ 2 / (2 * (count : ℝ))) := by
      simpa only [support, representativeClassifier] using htail
    _ ≤ (∑ k ∈ Finset.Iic d, (count + count).choose k : ℝ) *
        Real.exp (-((count : ℝ) * error) ^ 2 / (2 * (count : ℝ))) := by
      gcongr
      exact_mod_cast hcard

/--
The joint bad event for an iid double sample and an auxiliary independent
Boolean pair swap.  Its measurability is a separate permissible-class
condition when `concepts` itself is not finite.
-/
noncomputable def finiteIIDVCPairSwapBadEvent
    {X : Type*} (concepts : Set (BinaryClassifier X)) (count : ℕ) (error : ℝ) :
    Set ((Fin (count + count) → X × Bool) × (Fin count → Bool)) :=
  {pair | ∃ classifier, classifier ∈ concepts ∧
    error ≤ finiteBinaryEmpiricalError
      (binarySwappedFirstSample
        (Probability.finiteIIDTrainSample count pair.1)
        (Probability.finiteIIDGhostSample count pair.1) pair.2) classifier -
      finiteBinaryEmpiricalError
        (binarySwappedSecondSample
          (Probability.finiteIIDTrainSample count pair.1)
          (Probability.finiteIIDGhostSample count pair.1) pair.2) classifier}

/-- The corresponding one-sided bad event for the unswapped iid double sample. -/
noncomputable def finiteIIDVCTwoSampleBadEvent
    {X : Type*} (concepts : Set (BinaryClassifier X)) (count : ℕ) (error : ℝ) :
    Set (Fin (count + count) → X × Bool) :=
  {sample | ∃ classifier, classifier ∈ concepts ∧
    error ≤ finiteBinaryEmpiricalError
      (Probability.finiteIIDTrainSample count sample) classifier -
      finiteBinaryEmpiricalError
        (Probability.finiteIIDGhostSample count sample) classifier}

/-- The same one-sided two-sample bad event on an explicit train/ghost product. -/
noncomputable def finiteIIDVCTwoSampleProductBadEvent
    {X : Type*} (concepts : Set (BinaryClassifier X)) (count : ℕ) (error : ℝ) :
    Set ((Fin count → X × Bool) × (Fin count → X × Bool)) :=
  {samples | ∃ classifier, classifier ∈ concepts ∧
    error ≤ finiteBinaryEmpiricalError samples.1 classifier -
      finiteBinaryEmpiricalError samples.2 classifier}

/-- The canonical two-sample event is the split-product event's preimage. -/
theorem finiteIIDVCTwoSampleBadEvent_eq_preimage_productBadEvent
    {X : Type*} [MeasurableSpace X] (concepts : Set (BinaryClassifier X))
    (count : ℕ) (error : ℝ) :
    finiteIIDVCTwoSampleBadEvent concepts count error =
      Probability.finiteIIDTrainGhostSplitEquiv count ⁻¹'
        finiteIIDVCTwoSampleProductBadEvent concepts count error := by
  ext sample
  change
    (∃ classifier, classifier ∈ concepts ∧
      error ≤ finiteBinaryEmpiricalError
        (Probability.finiteIIDTrainSample count sample) classifier -
        finiteBinaryEmpiricalError
          (Probability.finiteIIDGhostSample count sample) classifier) ↔
    (∃ classifier, classifier ∈ concepts ∧
      error ≤ finiteBinaryEmpiricalError
        (Probability.finiteIIDTrainGhostSplitEquiv count sample).1 classifier -
        finiteBinaryEmpiricalError
          (Probability.finiteIIDTrainGhostSplitEquiv count sample).2 classifier)
  rw [Probability.finiteIIDTrainGhostSplitEquiv_fst,
    Probability.finiteIIDTrainGhostSplitEquiv_snd]

/--
The auxiliary pair-swap bad event is exactly the preimage of the ordinary
two-sample bad event under `finiteIIDPairSwapSample`.
-/
theorem finiteIIDVCPairSwapBadEvent_eq_preimage_twoSampleBadEvent
    {X : Type*} [MeasurableSpace X] (concepts : Set (BinaryClassifier X))
    (count : ℕ) (error : ℝ) :
    finiteIIDVCPairSwapBadEvent concepts count error =
      finiteIIDPairSwapSample count ⁻¹'
        finiteIIDVCTwoSampleBadEvent concepts count error := by
  ext pair
  rcases pair with ⟨sample, swap⟩
  change
    (∃ classifier, classifier ∈ concepts ∧
      error ≤ finiteBinaryEmpiricalError
        (binarySwappedFirstSample (Probability.finiteIIDTrainSample count sample)
          (Probability.finiteIIDGhostSample count sample) swap) classifier -
        finiteBinaryEmpiricalError
          (binarySwappedSecondSample (Probability.finiteIIDTrainSample count sample)
            (Probability.finiteIIDGhostSample count sample) swap) classifier) ↔
    (∃ classifier, classifier ∈ concepts ∧
      error ≤ finiteBinaryEmpiricalError
        (Probability.finiteIIDTrainSample count
          (finiteIIDPairSwapSample count (sample, swap))) classifier -
        finiteBinaryEmpiricalError
          (Probability.finiteIIDGhostSample count
            (finiteIIDPairSwapSample count (sample, swap))) classifier)
  have htrain : Probability.finiteIIDTrainSample count
      (finiteIIDPairSwapSample count (sample, swap)) =
      binarySwappedFirstSample (Probability.finiteIIDTrainSample count sample)
        (Probability.finiteIIDGhostSample count sample) swap := by
    simpa only [finiteIIDPairSwapSample] using
      finiteIIDTrainSample_pairSwapReindex_eq_binarySwappedFirst count swap sample
  have hghost : Probability.finiteIIDGhostSample count
      (finiteIIDPairSwapSample count (sample, swap)) =
      binarySwappedSecondSample (Probability.finiteIIDTrainSample count sample)
        (Probability.finiteIIDGhostSample count sample) swap := by
    simpa only [finiteIIDPairSwapSample] using
      finiteIIDGhostSample_pairSwapReindex_eq_binarySwappedSecond count swap sample
  rw [htrain, hghost]

/--
Integrating the fixed-two-sample VC swap tail gives the same bound on the
joint iid-double-sample/fair-swap event.  The explicit `hmeasurable`
assumption is the source's permissible-class measurability requirement.
-/
theorem finiteIID_vc_pairSwap_jointGap_upperTail
    {X : Type*} [MeasurableSpace X] (law : Measure (X × Bool))
    [IsProbabilityMeasure law] {concepts : Set (BinaryClassifier X)}
    {d count : ℕ} (hvc : VCDimensionAtMost concepts d) (hcount : 0 < count)
    (error : ℝ) (herror : 0 ≤ error)
    (hmeasurable : MeasurableSet (finiteIIDVCPairSwapBadEvent concepts count error)) :
    ((Probability.finiteIIDSampleLaw law (count + count)).prod
      (FairCoin.productMeasure (Fin count))).real
        (finiteIIDVCPairSwapBadEvent concepts count error) ≤
      (∑ k ∈ Finset.Iic d, (count + count).choose k : ℝ) *
        Real.exp (-((count : ℝ) * error) ^ 2 / (2 * (count : ℝ))) := by
  letI : IsProbabilityMeasure (Probability.finiteIIDSampleLaw law (count + count)) := by
    dsimp [Probability.finiteIIDSampleLaw]
    infer_instance
  letI : IsProbabilityMeasure (FairCoin.productMeasure (Fin count)) :=
    FairCoin.productMeasure_isProbabilityMeasure (Fin count)
  apply Probability.measureReal_prod_event_le_of_forall_section_le
    (Probability.finiteIIDSampleLaw law (count + count))
    (FairCoin.productMeasure (Fin count))
    (finiteIIDVCPairSwapBadEvent concepts count error) hmeasurable
  · positivity
  · intro sample
    simpa only [finiteIIDVCPairSwapBadEvent] using
      finite_uniform_binaryTwoSample_swapGap_upperTail_vc hvc hcount
        (Probability.finiteIIDTrainSample count sample)
        (Probability.finiteIIDGhostSample count sample) error herror

/--
The one-sided iid two-sample VC tail obtained from finite trace reduction,
fair-swap concentration, and random-swap invariance.  The two explicit
measurability hypotheses are the permissible-class interface needed for an
arbitrary (possibly infinite) concept class.
-/
theorem finiteIID_vc_twoSampleGap_upperTail
    {X : Type*} [MeasurableSpace X] (law : Measure (X × Bool))
    [IsProbabilityMeasure law] {concepts : Set (BinaryClassifier X)}
    {d count : ℕ} (hvc : VCDimensionAtMost concepts d) (hcount : 0 < count)
    (error : ℝ) (herror : 0 ≤ error)
    (htwoSampleMeasurable : MeasurableSet (finiteIIDVCTwoSampleBadEvent concepts count error))
    (hpairSwapMeasurable : MeasurableSet (finiteIIDVCPairSwapBadEvent concepts count error)) :
    (Probability.finiteIIDSampleLaw law (count + count)).real
      (finiteIIDVCTwoSampleBadEvent concepts count error) ≤
      (∑ k ∈ Finset.Iic d, (count + count).choose k : ℝ) *
        Real.exp (-((count : ℝ) * error) ^ 2 / (2 * (count : ℝ))) := by
  have heventEq := finiteIIDVCPairSwapBadEvent_eq_preimage_twoSampleBadEvent
    concepts count error
  have hpreimage : MeasurableSet (finiteIIDPairSwapSample count ⁻¹'
      finiteIIDVCTwoSampleBadEvent concepts count error) := by
    rw [← heventEq]
    exact hpairSwapMeasurable
  have hinvariance := measureReal_finiteIIDPairSwap_preimage_eq law count
    (finiteIIDVCTwoSampleBadEvent concepts count error)
    htwoSampleMeasurable hpreimage
  have hinvariance' :
      ((Probability.finiteIIDSampleLaw law (count + count)).prod
        (FairCoin.productMeasure (Fin count))).real
        (finiteIIDVCPairSwapBadEvent concepts count error) =
      (Probability.finiteIIDSampleLaw law (count + count)).real
        (finiteIIDVCTwoSampleBadEvent concepts count error) := by
    rw [heventEq]
    simpa only [Set.preimage] using hinvariance
  calc
    (Probability.finiteIIDSampleLaw law (count + count)).real
        (finiteIIDVCTwoSampleBadEvent concepts count error) =
        ((Probability.finiteIIDSampleLaw law (count + count)).prod
          (FairCoin.productMeasure (Fin count))).real
          (finiteIIDVCPairSwapBadEvent concepts count error) := by
      exact hinvariance'.symm
    _ ≤ (∑ k ∈ Finset.Iic d, (count + count).choose k : ℝ) *
        Real.exp (-((count : ℝ) * error) ^ 2 / (2 * (count : ℝ))) :=
      finiteIID_vc_pairSwap_jointGap_upperTail law hvc hcount error herror
        hpairSwapMeasurable

/--
The checked one-sided VC two-sample tail stated directly on independent
training and ghost product samples.
-/
theorem finiteIID_vc_twoSampleProductGap_upperTail
    {X : Type*} [MeasurableSpace X] (law : Measure (X × Bool))
    [IsProbabilityMeasure law] {concepts : Set (BinaryClassifier X)}
    {d count : ℕ} (hvc : VCDimensionAtMost concepts d) (hcount : 0 < count)
    (error : ℝ) (herror : 0 ≤ error)
    (htwoSampleMeasurable : MeasurableSet (finiteIIDVCTwoSampleBadEvent concepts count error))
    (hpairSwapMeasurable : MeasurableSet (finiteIIDVCPairSwapBadEvent concepts count error))
    (hproductMeasurable : MeasurableSet
      (finiteIIDVCTwoSampleProductBadEvent concepts count error)) :
    ((Probability.finiteIIDSampleLaw law count).prod
      (Probability.finiteIIDSampleLaw law count)).real
        (finiteIIDVCTwoSampleProductBadEvent concepts count error) ≤
      (∑ k ∈ Finset.Iic d, (count + count).choose k : ℝ) *
        Real.exp (-((count : ℝ) * error) ^ 2 / (2 * (count : ℝ))) := by
  letI : IsProbabilityMeasure (Probability.finiteIIDSampleLaw law count) := by
    dsimp [Probability.finiteIIDSampleLaw]
    infer_instance
  have heventEq := finiteIIDVCTwoSampleBadEvent_eq_preimage_productBadEvent
    concepts count error
  have hsplit := Probability.measurePreserving_finiteIIDTrainGhostSplit law count
  have hmeasure := hsplit.measure_preimage hproductMeasurable.nullMeasurableSet
  have hmeasure' :
      (Probability.finiteIIDSampleLaw law (count + count))
        (finiteIIDVCTwoSampleBadEvent concepts count error) =
      ((Probability.finiteIIDSampleLaw law count).prod
        (Probability.finiteIIDSampleLaw law count))
        (finiteIIDVCTwoSampleProductBadEvent concepts count error) := by
    rw [heventEq]
    exact hmeasure
  calc
    ((Probability.finiteIIDSampleLaw law count).prod
        (Probability.finiteIIDSampleLaw law count)).real
        (finiteIIDVCTwoSampleProductBadEvent concepts count error) =
        (Probability.finiteIIDSampleLaw law (count + count)).real
          (finiteIIDVCTwoSampleBadEvent concepts count error) := by
      simpa only [Measure.real] using congrArg ENNReal.toReal hmeasure'.symm
    _ ≤ (∑ k ∈ Finset.Iic d, (count + count).choose k : ℝ) *
        Real.exp (-((count : ℝ) * error) ^ 2 / (2 * (count : ℝ))) :=
      finiteIID_vc_twoSampleGap_upperTail law hvc hcount error herror
        htwoSampleMeasurable hpairSwapMeasurable

/-- The same two-sample bad event with the ghost sample minus the training sample. -/
noncomputable def finiteIIDVCTwoSampleReverseProductBadEvent
    {X : Type*} (concepts : Set (BinaryClassifier X)) (count : ℕ) (error : ℝ) :
    Set ((Fin count → X × Bool) × (Fin count → X × Bool)) :=
  {samples | ∃ classifier, classifier ∈ concepts ∧
    error ≤ finiteBinaryEmpiricalError samples.2 classifier -
      finiteBinaryEmpiricalError samples.1 classifier}

/-- Reversing the product pair identifies the reverse and ordinary gap events. -/
theorem finiteIIDVCTwoSampleReverseProductBadEvent_eq_preimage
    {X : Type*} (concepts : Set (BinaryClassifier X)) (count : ℕ) (error : ℝ) :
    finiteIIDVCTwoSampleReverseProductBadEvent concepts count error =
      Prod.swap ⁻¹' finiteIIDVCTwoSampleProductBadEvent concepts count error := by
  rfl

/-- The reverse product bad event is measurable whenever its ordinary orientation is. -/
theorem measurableSet_finiteIIDVCTwoSampleReverseProductBadEvent
    {X : Type*} [MeasurableSpace X] (concepts : Set (BinaryClassifier X))
    (count : ℕ) (error : ℝ)
    (hproductMeasurable : MeasurableSet
      (finiteIIDVCTwoSampleProductBadEvent concepts count error)) :
    MeasurableSet (finiteIIDVCTwoSampleReverseProductBadEvent concepts count error) := by
  rw [finiteIIDVCTwoSampleReverseProductBadEvent_eq_preimage]
  exact hproductMeasurable.preimage measurable_swap

/-- The VC two-sample tail is invariant under reversing training and ghost halves. -/
theorem finiteIID_vc_twoSampleReverseProductGap_upperTail
    {X : Type*} [MeasurableSpace X] (law : Measure (X × Bool))
    [IsProbabilityMeasure law] {concepts : Set (BinaryClassifier X)}
    {d count : ℕ} (hvc : VCDimensionAtMost concepts d) (hcount : 0 < count)
    (error : ℝ) (herror : 0 ≤ error)
    (htwoSampleMeasurable : MeasurableSet (finiteIIDVCTwoSampleBadEvent concepts count error))
    (hpairSwapMeasurable : MeasurableSet (finiteIIDVCPairSwapBadEvent concepts count error))
    (hproductMeasurable : MeasurableSet
      (finiteIIDVCTwoSampleProductBadEvent concepts count error)) :
    ((Probability.finiteIIDSampleLaw law count).prod
      (Probability.finiteIIDSampleLaw law count)).real
        (finiteIIDVCTwoSampleReverseProductBadEvent concepts count error) ≤
      (∑ k ∈ Finset.Iic d, (count + count).choose k : ℝ) *
        Real.exp (-((count : ℝ) * error) ^ 2 / (2 * (count : ℝ))) := by
  letI : IsProbabilityMeasure (Probability.finiteIIDSampleLaw law count) := by
    dsimp [Probability.finiteIIDSampleLaw]
    infer_instance
  have heventEq := finiteIIDVCTwoSampleReverseProductBadEvent_eq_preimage
    concepts count error
  have hswap := (Measure.measurePreserving_swap
    (μ := Probability.finiteIIDSampleLaw law count)
    (ν := Probability.finiteIIDSampleLaw law count)).measure_preimage
      hproductMeasurable.nullMeasurableSet
  have hmeasure :
      ((Probability.finiteIIDSampleLaw law count).prod
        (Probability.finiteIIDSampleLaw law count))
        (finiteIIDVCTwoSampleReverseProductBadEvent concepts count error) =
      ((Probability.finiteIIDSampleLaw law count).prod
        (Probability.finiteIIDSampleLaw law count))
        (finiteIIDVCTwoSampleProductBadEvent concepts count error) := by
    rw [heventEq]
    exact hswap
  calc
    ((Probability.finiteIIDSampleLaw law count).prod
        (Probability.finiteIIDSampleLaw law count)).real
        (finiteIIDVCTwoSampleReverseProductBadEvent concepts count error) =
        ((Probability.finiteIIDSampleLaw law count).prod
          (Probability.finiteIIDSampleLaw law count)).real
          (finiteIIDVCTwoSampleProductBadEvent concepts count error) := by
      simpa only [Measure.real] using congrArg ENNReal.toReal hmeasure
    _ ≤ (∑ k ∈ Finset.Iic d, (count + count).choose k : ℝ) *
        Real.exp (-((count : ℝ) * error) ^ 2 / (2 * (count : ℝ))) :=
      finiteIID_vc_twoSampleProductGap_upperTail law hvc hcount error herror
        htwoSampleMeasurable hpairSwapMeasurable hproductMeasurable

/--
A population-underestimation witness on a fixed training sample supplies a
large favorable ghost section of the reverse two-sample VC event.
-/
theorem finiteIID_populationUnderestimate_witness_reverseGap_section
    {X : Type*} [MeasurableSpace X] (law : Measure (X × Bool))
    [IsProbabilityMeasure law] {concepts : Set (BinaryClassifier X)}
    (count : ℕ) (hcount : 0 < count)
    (trainingSample : Fin count → X × Bool) (classifier : BinaryClassifier X)
    (hclassifier : classifier ∈ concepts) (hclassifier_measurable : Measurable classifier)
    (error : ℝ) (herror : 0 ≤ error)
    (hunderestimate : error ≤ binaryPopulationError law classifier -
      finiteBinaryEmpiricalError trainingSample classifier) :
    1 - Real.exp (-((count : ℝ) * (error / 2)) ^ 2 /
        (2 * (count : ℝ) * (1 / 4 : ℝ))) ≤
      (Probability.finiteIIDSampleLaw law count).real {ghostSample |
        (trainingSample, ghostSample) ∈
          finiteIIDVCTwoSampleReverseProductBadEvent concepts count (error / 2)} := by
  letI : IsProbabilityMeasure (Probability.finiteIIDSampleLaw law count) := by
    dsimp [Probability.finiteIIDSampleLaw]
    infer_instance
  have hgood := finiteIID_population_sub_lt_empiricalError_probability_lower
    law count hcount classifier hclassifier_measurable (error / 2) (by linarith)
  have hsubset : {ghostSample |
      binaryPopulationError law classifier - error / 2 <
        finiteBinaryEmpiricalError ghostSample classifier} ⊆
      {ghostSample | (trainingSample, ghostSample) ∈
          finiteIIDVCTwoSampleReverseProductBadEvent concepts count (error / 2)} := by
    intro ghostSample hghost
    change binaryPopulationError law classifier - error / 2 <
      finiteBinaryEmpiricalError ghostSample classifier at hghost
    refine ⟨classifier, hclassifier, ?_⟩
    change error / 2 ≤ finiteBinaryEmpiricalError ghostSample classifier -
      finiteBinaryEmpiricalError trainingSample classifier
    linarith
  exact hgood.trans (measureReal_mono hsubset (measure_ne_top _ _))

/--
The training-sample event that some classifier underestimates its population
error by at least `error`.

For arbitrary (possibly infinite) concept classes, measurability of this
existential event is intentionally supplied where it is integrated; this is
the standard permissible-class boundary in VC symmetrization.
-/
noncomputable def finiteIIDVCPopulationUnderestimateBadEvent
    {X : Type*} [MeasurableSpace X] (law : Measure (X × Bool))
    (concepts : Set (BinaryClassifier X)) (count : ℕ) (error : ℝ) :
    Set (Fin count → X × Bool) :=
  {trainingSample | ∃ classifier, classifier ∈ concepts ∧
    error ≤ binaryPopulationError law classifier -
      finiteBinaryEmpiricalError trainingSample classifier}

/--
Every population-underestimation training sample has a uniformly favorable
ghost-sample section inside the reverse two-sample VC event.
-/
theorem finiteIID_populationUnderestimate_reverseGap_section
    {X : Type*} [MeasurableSpace X] (law : Measure (X × Bool))
    [IsProbabilityMeasure law] {concepts : Set (BinaryClassifier X)}
    (count : ℕ) (hcount : 0 < count)
    (hclassifier_measurable : ∀ classifier, classifier ∈ concepts → Measurable classifier)
    (error : ℝ) (herror : 0 ≤ error)
    (trainingSample : Fin count → X × Bool)
    (htraining : trainingSample ∈
      finiteIIDVCPopulationUnderestimateBadEvent law concepts count error) :
    1 - Real.exp (-((count : ℝ) * (error / 2)) ^ 2 /
        (2 * (count : ℝ) * (1 / 4 : ℝ))) ≤
      (Probability.finiteIIDSampleLaw law count).real {ghostSample |
        (trainingSample, ghostSample) ∈
          finiteIIDVCTwoSampleReverseProductBadEvent concepts count (error / 2)} := by
  rcases htraining with ⟨classifier, hclassifier, hunderestimate⟩
  exact finiteIID_populationUnderestimate_witness_reverseGap_section
    law count hcount trainingSample classifier hclassifier
      (hclassifier_measurable classifier hclassifier) error herror hunderestimate

/--
Class-level population-to-ghost symmetrization for a VC class.  The theorem
integrates the favorable ghost section over the measurable population-error
bad event, without selecting a classifier measurably from each training
sample.
-/
theorem finiteIID_populationUnderestimate_symmetrization_lower
    {X : Type*} [MeasurableSpace X] (law : Measure (X × Bool))
    [IsProbabilityMeasure law] {concepts : Set (BinaryClassifier X)}
    (count : ℕ) (hcount : 0 < count)
    (hclassifier_measurable : ∀ classifier, classifier ∈ concepts → Measurable classifier)
    (error : ℝ) (herror : 0 ≤ error)
    (hpopulationBadMeasurable : MeasurableSet
      (finiteIIDVCPopulationUnderestimateBadEvent law concepts count error))
    (hreverseProductMeasurable : MeasurableSet
      (finiteIIDVCTwoSampleReverseProductBadEvent concepts count (error / 2))) :
    (1 - Real.exp (-((count : ℝ) * (error / 2)) ^ 2 /
        (2 * (count : ℝ) * (1 / 4 : ℝ)))) *
        (Probability.finiteIIDSampleLaw law count).real
          (finiteIIDVCPopulationUnderestimateBadEvent law concepts count error) ≤
      ((Probability.finiteIIDSampleLaw law count).prod
        (Probability.finiteIIDSampleLaw law count)).real
          (finiteIIDVCTwoSampleReverseProductBadEvent concepts count (error / 2)) := by
  letI : IsProbabilityMeasure (Probability.finiteIIDSampleLaw law count) := by
    dsimp [Probability.finiteIIDSampleLaw]
    infer_instance
  have hcountReal : 0 < (count : ℝ) := by
    exact_mod_cast hcount
  have hfactorNonneg : 0 ≤ 1 - Real.exp (-((count : ℝ) * (error / 2)) ^ 2 /
      (2 * (count : ℝ) * (1 / 4 : ℝ))) := by
    apply sub_nonneg.mpr
    rw [Real.exp_le_one_iff]
    apply div_nonpos_of_nonpos_of_nonneg
    · exact neg_nonpos.mpr (sq_nonneg _)
    · positivity
  apply Probability.mul_measureReal_le_measureReal_prod_event_of_forall_section_le
    (Probability.finiteIIDSampleLaw law count)
    (Probability.finiteIIDSampleLaw law count)
    (finiteIIDVCTwoSampleReverseProductBadEvent concepts count (error / 2))
    hreverseProductMeasurable
    (finiteIIDVCPopulationUnderestimateBadEvent law concepts count error)
    hpopulationBadMeasurable
    (1 - Real.exp (-((count : ℝ) * (error / 2)) ^ 2 /
      (2 * (count : ℝ) * (1 / 4 : ℝ)))) hfactorNonneg
  intro trainingSample htrainingSample
  exact finiteIID_populationUnderestimate_reverseGap_section law count hcount
    hclassifier_measurable error herror trainingSample htrainingSample

/--
The class-level symmetrization lower bound combined with the checked
two-sample VC tail.  This is the analytic pre-division form of Vapnik's
generalization argument; deriving the printed source constant remains a
separate arithmetic endpoint.
-/
theorem finiteIID_populationUnderestimate_symmetrization_vc_upper
    {X : Type*} [MeasurableSpace X] (law : Measure (X × Bool))
    [IsProbabilityMeasure law] {concepts : Set (BinaryClassifier X)}
    {d count : ℕ} (hvc : VCDimensionAtMost concepts d) (hcount : 0 < count)
    (hclassifier_measurable : ∀ classifier, classifier ∈ concepts → Measurable classifier)
    (error : ℝ) (herror : 0 ≤ error)
    (hpopulationBadMeasurable : MeasurableSet
      (finiteIIDVCPopulationUnderestimateBadEvent law concepts count error))
    (htwoSampleMeasurable : MeasurableSet
      (finiteIIDVCTwoSampleBadEvent concepts count (error / 2)))
    (hpairSwapMeasurable : MeasurableSet
      (finiteIIDVCPairSwapBadEvent concepts count (error / 2)))
    (hproductMeasurable : MeasurableSet
      (finiteIIDVCTwoSampleProductBadEvent concepts count (error / 2))) :
    (1 - Real.exp (-((count : ℝ) * (error / 2)) ^ 2 /
        (2 * (count : ℝ) * (1 / 4 : ℝ)))) *
        (Probability.finiteIIDSampleLaw law count).real
          (finiteIIDVCPopulationUnderestimateBadEvent law concepts count error) ≤
      (∑ k ∈ Finset.Iic d, (count + count).choose k : ℝ) *
        Real.exp (-((count : ℝ) * (error / 2)) ^ 2 / (2 * (count : ℝ))) := by
  have hreverseProductMeasurable : MeasurableSet
      (finiteIIDVCTwoSampleReverseProductBadEvent concepts count (error / 2)) :=
    measurableSet_finiteIIDVCTwoSampleReverseProductBadEvent concepts count (error / 2)
      hproductMeasurable
  exact (finiteIID_populationUnderestimate_symmetrization_lower law count hcount
    hclassifier_measurable error herror hpopulationBadMeasurable
    hreverseProductMeasurable).trans
      (finiteIID_vc_twoSampleReverseProductGap_upperTail law hvc hcount (error / 2)
        (by linarith) htwoSampleMeasurable hpairSwapMeasurable hproductMeasurable)

/--
Parameterized lower-side ghost section.  Retaining the ghost tolerance as an
argument permits the sharper `error / 4` split used in the Vapnik-constant
calculation, while the earlier half-split theorem remains a convenient
special case.
-/
theorem finiteIID_populationUnderestimate_witness_reverseGap_section_of_ghostSlack
    {X : Type*} [MeasurableSpace X] (law : Measure (X × Bool))
    [IsProbabilityMeasure law] {concepts : Set (BinaryClassifier X)}
    (count : ℕ) (hcount : 0 < count)
    (trainingSample : Fin count → X × Bool) (classifier : BinaryClassifier X)
    (hclassifier : classifier ∈ concepts) (hclassifier_measurable : Measurable classifier)
    (error ghostSlack : ℝ) (hghostSlack : 0 ≤ ghostSlack)
    (hunderestimate : error ≤ binaryPopulationError law classifier -
      finiteBinaryEmpiricalError trainingSample classifier) :
    1 - Real.exp (-((count : ℝ) * ghostSlack) ^ 2 /
        (2 * (count : ℝ) * (1 / 4 : ℝ))) ≤
      (Probability.finiteIIDSampleLaw law count).real {ghostSample |
        (trainingSample, ghostSample) ∈
          finiteIIDVCTwoSampleReverseProductBadEvent concepts count (error - ghostSlack)} := by
  letI : IsProbabilityMeasure (Probability.finiteIIDSampleLaw law count) := by
    dsimp [Probability.finiteIIDSampleLaw]
    infer_instance
  have hgood := finiteIID_population_sub_lt_empiricalError_probability_lower
    law count hcount classifier hclassifier_measurable ghostSlack hghostSlack
  have hsubset : {ghostSample |
      binaryPopulationError law classifier - ghostSlack <
        finiteBinaryEmpiricalError ghostSample classifier} ⊆
      {ghostSample | (trainingSample, ghostSample) ∈
        finiteIIDVCTwoSampleReverseProductBadEvent concepts count (error - ghostSlack)} := by
    intro ghostSample hghost
    change binaryPopulationError law classifier - ghostSlack <
      finiteBinaryEmpiricalError ghostSample classifier at hghost
    refine ⟨classifier, hclassifier, ?_⟩
    change error - ghostSlack ≤ finiteBinaryEmpiricalError ghostSample classifier -
      finiteBinaryEmpiricalError trainingSample classifier
    linarith
  exact hgood.trans (measureReal_mono hsubset (measure_ne_top _ _))

/-- Parameterized class-level lower-side ghost symmetrization. -/
theorem finiteIID_populationUnderestimate_symmetrization_lower_of_ghostSlack
    {X : Type*} [MeasurableSpace X] (law : Measure (X × Bool))
    [IsProbabilityMeasure law] {concepts : Set (BinaryClassifier X)}
    (count : ℕ) (hcount : 0 < count)
    (hclassifier_measurable : ∀ classifier, classifier ∈ concepts → Measurable classifier)
    (error ghostSlack : ℝ) (hghostSlack : 0 ≤ ghostSlack)
    (hpopulationBadMeasurable : MeasurableSet
      (finiteIIDVCPopulationUnderestimateBadEvent law concepts count error))
    (hreverseProductMeasurable : MeasurableSet
      (finiteIIDVCTwoSampleReverseProductBadEvent concepts count (error - ghostSlack))) :
    (1 - Real.exp (-((count : ℝ) * ghostSlack) ^ 2 /
        (2 * (count : ℝ) * (1 / 4 : ℝ)))) *
        (Probability.finiteIIDSampleLaw law count).real
          (finiteIIDVCPopulationUnderestimateBadEvent law concepts count error) ≤
      ((Probability.finiteIIDSampleLaw law count).prod
        (Probability.finiteIIDSampleLaw law count)).real
          (finiteIIDVCTwoSampleReverseProductBadEvent concepts count (error - ghostSlack)) := by
  letI : IsProbabilityMeasure (Probability.finiteIIDSampleLaw law count) := by
    dsimp [Probability.finiteIIDSampleLaw]
    infer_instance
  have hcountReal : 0 < (count : ℝ) := by exact_mod_cast hcount
  have hfactorNonneg : 0 ≤ 1 - Real.exp (-((count : ℝ) * ghostSlack) ^ 2 /
      (2 * (count : ℝ) * (1 / 4 : ℝ))) := by
    apply sub_nonneg.mpr
    rw [Real.exp_le_one_iff]
    apply div_nonpos_of_nonpos_of_nonneg
    · exact neg_nonpos.mpr (sq_nonneg _)
    · positivity
  apply Probability.mul_measureReal_le_measureReal_prod_event_of_forall_section_le
    (Probability.finiteIIDSampleLaw law count)
    (Probability.finiteIIDSampleLaw law count)
    (finiteIIDVCTwoSampleReverseProductBadEvent concepts count (error - ghostSlack))
    hreverseProductMeasurable
    (finiteIIDVCPopulationUnderestimateBadEvent law concepts count error)
    hpopulationBadMeasurable
    (1 - Real.exp (-((count : ℝ) * ghostSlack) ^ 2 /
      (2 * (count : ℝ) * (1 / 4 : ℝ)))) hfactorNonneg
  intro trainingSample htrainingSample
  rcases htrainingSample with ⟨classifier, hclassifier, hunderestimate⟩
  exact finiteIID_populationUnderestimate_witness_reverseGap_section_of_ghostSlack
    law count hcount trainingSample classifier hclassifier
      (hclassifier_measurable classifier hclassifier) error ghostSlack hghostSlack hunderestimate

/-- Parameterized lower-side symmetrization combined with the VC two-sample tail. -/
theorem finiteIID_populationUnderestimate_symmetrization_vc_upper_of_ghostSlack
    {X : Type*} [MeasurableSpace X] (law : Measure (X × Bool))
    [IsProbabilityMeasure law] {concepts : Set (BinaryClassifier X)}
    {d count : ℕ} (hvc : VCDimensionAtMost concepts d) (hcount : 0 < count)
    (hclassifier_measurable : ∀ classifier, classifier ∈ concepts → Measurable classifier)
    (error ghostSlack : ℝ) (hghostSlack : 0 ≤ ghostSlack)
    (hgap : 0 ≤ error - ghostSlack)
    (hpopulationBadMeasurable : MeasurableSet
      (finiteIIDVCPopulationUnderestimateBadEvent law concepts count error))
    (htwoSampleMeasurable : MeasurableSet
      (finiteIIDVCTwoSampleBadEvent concepts count (error - ghostSlack)))
    (hpairSwapMeasurable : MeasurableSet
      (finiteIIDVCPairSwapBadEvent concepts count (error - ghostSlack)))
    (hproductMeasurable : MeasurableSet
      (finiteIIDVCTwoSampleProductBadEvent concepts count (error - ghostSlack))) :
    (1 - Real.exp (-((count : ℝ) * ghostSlack) ^ 2 /
        (2 * (count : ℝ) * (1 / 4 : ℝ)))) *
        (Probability.finiteIIDSampleLaw law count).real
          (finiteIIDVCPopulationUnderestimateBadEvent law concepts count error) ≤
      (∑ k ∈ Finset.Iic d, (count + count).choose k : ℝ) *
        Real.exp (-((count : ℝ) * (error - ghostSlack)) ^ 2 /
          (2 * (count : ℝ))) := by
  have hreverseProductMeasurable : MeasurableSet
      (finiteIIDVCTwoSampleReverseProductBadEvent concepts count (error - ghostSlack)) :=
    measurableSet_finiteIIDVCTwoSampleReverseProductBadEvent concepts count (error - ghostSlack)
      hproductMeasurable
  exact (finiteIID_populationUnderestimate_symmetrization_lower_of_ghostSlack
    law count hcount hclassifier_measurable error ghostSlack hghostSlack
    hpopulationBadMeasurable hreverseProductMeasurable).trans
      (finiteIID_vc_twoSampleReverseProductGap_upperTail law hvc hcount
        (error - ghostSlack) hgap htwoSampleMeasurable hpairSwapMeasurable hproductMeasurable)

/-- The training-sample event that some classifier overestimates its population error. -/
noncomputable def finiteIIDVCPopulationOverestimateBadEvent
    {X : Type*} [MeasurableSpace X] (law : Measure (X × Bool))
    (concepts : Set (BinaryClassifier X)) (count : ℕ) (error : ℝ) :
    Set (Fin count → X × Bool) :=
  {trainingSample | ∃ classifier, classifier ∈ concepts ∧
    error ≤ finiteBinaryEmpiricalError trainingSample classifier -
      binaryPopulationError law classifier}

/--
An empirical-overestimation witness on a fixed training sample supplies a
large favorable ghost section of the ordinary two-sample VC event.
-/
theorem finiteIID_populationOverestimate_witness_gap_section
    {X : Type*} [MeasurableSpace X] (law : Measure (X × Bool))
    [IsProbabilityMeasure law] {concepts : Set (BinaryClassifier X)}
    (count : ℕ) (hcount : 0 < count)
    (trainingSample : Fin count → X × Bool) (classifier : BinaryClassifier X)
    (hclassifier : classifier ∈ concepts) (hclassifier_measurable : Measurable classifier)
    (error : ℝ) (herror : 0 ≤ error)
    (hoverestimate : error ≤ finiteBinaryEmpiricalError trainingSample classifier -
      binaryPopulationError law classifier) :
    1 - Real.exp (-((count : ℝ) * (error / 2)) ^ 2 /
        (2 * (count : ℝ) * (1 / 4 : ℝ))) ≤
      (Probability.finiteIIDSampleLaw law count).real {ghostSample |
        (trainingSample, ghostSample) ∈
          finiteIIDVCTwoSampleProductBadEvent concepts count (error / 2)} := by
  letI : IsProbabilityMeasure (Probability.finiteIIDSampleLaw law count) := by
    dsimp [Probability.finiteIIDSampleLaw]
    infer_instance
  have hgood := finiteIID_empiricalError_lt_population_add_probability_lower
    law count hcount classifier hclassifier_measurable (error / 2) (by linarith)
  have hsubset : {ghostSample |
      finiteBinaryEmpiricalError ghostSample classifier <
        binaryPopulationError law classifier + error / 2} ⊆
      {ghostSample | (trainingSample, ghostSample) ∈
        finiteIIDVCTwoSampleProductBadEvent concepts count (error / 2)} := by
    intro ghostSample hghost
    change finiteBinaryEmpiricalError ghostSample classifier <
      binaryPopulationError law classifier + error / 2 at hghost
    refine ⟨classifier, hclassifier, ?_⟩
    change error / 2 ≤ finiteBinaryEmpiricalError trainingSample classifier -
      finiteBinaryEmpiricalError ghostSample classifier
    linarith
  exact hgood.trans (measureReal_mono hsubset (measure_ne_top _ _))

/-- Every empirical-overestimation training sample has a favorable ghost section. -/
theorem finiteIID_populationOverestimate_gap_section
    {X : Type*} [MeasurableSpace X] (law : Measure (X × Bool))
    [IsProbabilityMeasure law] {concepts : Set (BinaryClassifier X)}
    (count : ℕ) (hcount : 0 < count)
    (hclassifier_measurable : ∀ classifier, classifier ∈ concepts → Measurable classifier)
    (error : ℝ) (herror : 0 ≤ error)
    (trainingSample : Fin count → X × Bool)
    (htraining : trainingSample ∈
      finiteIIDVCPopulationOverestimateBadEvent law concepts count error) :
    1 - Real.exp (-((count : ℝ) * (error / 2)) ^ 2 /
        (2 * (count : ℝ) * (1 / 4 : ℝ))) ≤
      (Probability.finiteIIDSampleLaw law count).real {ghostSample |
        (trainingSample, ghostSample) ∈
          finiteIIDVCTwoSampleProductBadEvent concepts count (error / 2)} := by
  rcases htraining with ⟨classifier, hclassifier, hoverestimate⟩
  exact finiteIID_populationOverestimate_witness_gap_section law count hcount
    trainingSample classifier hclassifier
      (hclassifier_measurable classifier hclassifier) error herror hoverestimate

/-- Class-level ghost-sample symmetrization for empirical overestimation. -/
theorem finiteIID_populationOverestimate_symmetrization_lower
    {X : Type*} [MeasurableSpace X] (law : Measure (X × Bool))
    [IsProbabilityMeasure law] {concepts : Set (BinaryClassifier X)}
    (count : ℕ) (hcount : 0 < count)
    (hclassifier_measurable : ∀ classifier, classifier ∈ concepts → Measurable classifier)
    (error : ℝ) (herror : 0 ≤ error)
    (hpopulationBadMeasurable : MeasurableSet
      (finiteIIDVCPopulationOverestimateBadEvent law concepts count error))
    (hproductMeasurable : MeasurableSet
      (finiteIIDVCTwoSampleProductBadEvent concepts count (error / 2))) :
    (1 - Real.exp (-((count : ℝ) * (error / 2)) ^ 2 /
        (2 * (count : ℝ) * (1 / 4 : ℝ)))) *
        (Probability.finiteIIDSampleLaw law count).real
          (finiteIIDVCPopulationOverestimateBadEvent law concepts count error) ≤
      ((Probability.finiteIIDSampleLaw law count).prod
        (Probability.finiteIIDSampleLaw law count)).real
          (finiteIIDVCTwoSampleProductBadEvent concepts count (error / 2)) := by
  letI : IsProbabilityMeasure (Probability.finiteIIDSampleLaw law count) := by
    dsimp [Probability.finiteIIDSampleLaw]
    infer_instance
  have hcountReal : 0 < (count : ℝ) := by
    exact_mod_cast hcount
  have hfactorNonneg : 0 ≤ 1 - Real.exp (-((count : ℝ) * (error / 2)) ^ 2 /
      (2 * (count : ℝ) * (1 / 4 : ℝ))) := by
    apply sub_nonneg.mpr
    rw [Real.exp_le_one_iff]
    apply div_nonpos_of_nonpos_of_nonneg
    · exact neg_nonpos.mpr (sq_nonneg _)
    · positivity
  apply Probability.mul_measureReal_le_measureReal_prod_event_of_forall_section_le
    (Probability.finiteIIDSampleLaw law count)
    (Probability.finiteIIDSampleLaw law count)
    (finiteIIDVCTwoSampleProductBadEvent concepts count (error / 2))
    hproductMeasurable
    (finiteIIDVCPopulationOverestimateBadEvent law concepts count error)
    hpopulationBadMeasurable
    (1 - Real.exp (-((count : ℝ) * (error / 2)) ^ 2 /
      (2 * (count : ℝ) * (1 / 4 : ℝ)))) hfactorNonneg
  intro trainingSample htrainingSample
  exact finiteIID_populationOverestimate_gap_section law count hcount
    hclassifier_measurable error herror trainingSample htrainingSample

/-- The overestimation symmetrization bound combined with the VC two-sample tail. -/
theorem finiteIID_populationOverestimate_symmetrization_vc_upper
    {X : Type*} [MeasurableSpace X] (law : Measure (X × Bool))
    [IsProbabilityMeasure law] {concepts : Set (BinaryClassifier X)}
    {d count : ℕ} (hvc : VCDimensionAtMost concepts d) (hcount : 0 < count)
    (hclassifier_measurable : ∀ classifier, classifier ∈ concepts → Measurable classifier)
    (error : ℝ) (herror : 0 ≤ error)
    (hpopulationBadMeasurable : MeasurableSet
      (finiteIIDVCPopulationOverestimateBadEvent law concepts count error))
    (htwoSampleMeasurable : MeasurableSet
      (finiteIIDVCTwoSampleBadEvent concepts count (error / 2)))
    (hpairSwapMeasurable : MeasurableSet
      (finiteIIDVCPairSwapBadEvent concepts count (error / 2)))
    (hproductMeasurable : MeasurableSet
      (finiteIIDVCTwoSampleProductBadEvent concepts count (error / 2))) :
    (1 - Real.exp (-((count : ℝ) * (error / 2)) ^ 2 /
        (2 * (count : ℝ) * (1 / 4 : ℝ)))) *
        (Probability.finiteIIDSampleLaw law count).real
          (finiteIIDVCPopulationOverestimateBadEvent law concepts count error) ≤
      (∑ k ∈ Finset.Iic d, (count + count).choose k : ℝ) *
        Real.exp (-((count : ℝ) * (error / 2)) ^ 2 / (2 * (count : ℝ))) := by
  exact (finiteIID_populationOverestimate_symmetrization_lower law count hcount
    hclassifier_measurable error herror hpopulationBadMeasurable
    hproductMeasurable).trans
      (finiteIID_vc_twoSampleProductGap_upperTail law hvc hcount (error / 2)
        (by linarith) htwoSampleMeasurable hpairSwapMeasurable hproductMeasurable)

/-- Parameterized upper-side ghost section for a fixed empirical-overestimate witness. -/
theorem finiteIID_populationOverestimate_witness_gap_section_of_ghostSlack
    {X : Type*} [MeasurableSpace X] (law : Measure (X × Bool))
    [IsProbabilityMeasure law] {concepts : Set (BinaryClassifier X)}
    (count : ℕ) (hcount : 0 < count)
    (trainingSample : Fin count → X × Bool) (classifier : BinaryClassifier X)
    (hclassifier : classifier ∈ concepts) (hclassifier_measurable : Measurable classifier)
    (error ghostSlack : ℝ) (hghostSlack : 0 ≤ ghostSlack)
    (hoverestimate : error ≤ finiteBinaryEmpiricalError trainingSample classifier -
      binaryPopulationError law classifier) :
    1 - Real.exp (-((count : ℝ) * ghostSlack) ^ 2 /
        (2 * (count : ℝ) * (1 / 4 : ℝ))) ≤
      (Probability.finiteIIDSampleLaw law count).real {ghostSample |
        (trainingSample, ghostSample) ∈
          finiteIIDVCTwoSampleProductBadEvent concepts count (error - ghostSlack)} := by
  letI : IsProbabilityMeasure (Probability.finiteIIDSampleLaw law count) := by
    dsimp [Probability.finiteIIDSampleLaw]
    infer_instance
  have hgood := finiteIID_empiricalError_lt_population_add_probability_lower
    law count hcount classifier hclassifier_measurable ghostSlack hghostSlack
  have hsubset : {ghostSample |
      finiteBinaryEmpiricalError ghostSample classifier <
        binaryPopulationError law classifier + ghostSlack} ⊆
      {ghostSample | (trainingSample, ghostSample) ∈
        finiteIIDVCTwoSampleProductBadEvent concepts count (error - ghostSlack)} := by
    intro ghostSample hghost
    change finiteBinaryEmpiricalError ghostSample classifier <
      binaryPopulationError law classifier + ghostSlack at hghost
    refine ⟨classifier, hclassifier, ?_⟩
    change error - ghostSlack ≤ finiteBinaryEmpiricalError trainingSample classifier -
      finiteBinaryEmpiricalError ghostSample classifier
    linarith
  exact hgood.trans (measureReal_mono hsubset (measure_ne_top _ _))

/-- Parameterized class-level upper-side ghost symmetrization. -/
theorem finiteIID_populationOverestimate_symmetrization_lower_of_ghostSlack
    {X : Type*} [MeasurableSpace X] (law : Measure (X × Bool))
    [IsProbabilityMeasure law] {concepts : Set (BinaryClassifier X)}
    (count : ℕ) (hcount : 0 < count)
    (hclassifier_measurable : ∀ classifier, classifier ∈ concepts → Measurable classifier)
    (error ghostSlack : ℝ) (hghostSlack : 0 ≤ ghostSlack)
    (hpopulationBadMeasurable : MeasurableSet
      (finiteIIDVCPopulationOverestimateBadEvent law concepts count error))
    (hproductMeasurable : MeasurableSet
      (finiteIIDVCTwoSampleProductBadEvent concepts count (error - ghostSlack))) :
    (1 - Real.exp (-((count : ℝ) * ghostSlack) ^ 2 /
        (2 * (count : ℝ) * (1 / 4 : ℝ)))) *
        (Probability.finiteIIDSampleLaw law count).real
          (finiteIIDVCPopulationOverestimateBadEvent law concepts count error) ≤
      ((Probability.finiteIIDSampleLaw law count).prod
        (Probability.finiteIIDSampleLaw law count)).real
          (finiteIIDVCTwoSampleProductBadEvent concepts count (error - ghostSlack)) := by
  letI : IsProbabilityMeasure (Probability.finiteIIDSampleLaw law count) := by
    dsimp [Probability.finiteIIDSampleLaw]
    infer_instance
  have hcountReal : 0 < (count : ℝ) := by exact_mod_cast hcount
  have hfactorNonneg : 0 ≤ 1 - Real.exp (-((count : ℝ) * ghostSlack) ^ 2 /
      (2 * (count : ℝ) * (1 / 4 : ℝ))) := by
    apply sub_nonneg.mpr
    rw [Real.exp_le_one_iff]
    apply div_nonpos_of_nonpos_of_nonneg
    · exact neg_nonpos.mpr (sq_nonneg _)
    · positivity
  apply Probability.mul_measureReal_le_measureReal_prod_event_of_forall_section_le
    (Probability.finiteIIDSampleLaw law count)
    (Probability.finiteIIDSampleLaw law count)
    (finiteIIDVCTwoSampleProductBadEvent concepts count (error - ghostSlack))
    hproductMeasurable
    (finiteIIDVCPopulationOverestimateBadEvent law concepts count error)
    hpopulationBadMeasurable
    (1 - Real.exp (-((count : ℝ) * ghostSlack) ^ 2 /
      (2 * (count : ℝ) * (1 / 4 : ℝ)))) hfactorNonneg
  intro trainingSample htrainingSample
  rcases htrainingSample with ⟨classifier, hclassifier, hoverestimate⟩
  exact finiteIID_populationOverestimate_witness_gap_section_of_ghostSlack
    law count hcount trainingSample classifier hclassifier
      (hclassifier_measurable classifier hclassifier) error ghostSlack hghostSlack hoverestimate

/-- Parameterized upper-side symmetrization combined with the VC two-sample tail. -/
theorem finiteIID_populationOverestimate_symmetrization_vc_upper_of_ghostSlack
    {X : Type*} [MeasurableSpace X] (law : Measure (X × Bool))
    [IsProbabilityMeasure law] {concepts : Set (BinaryClassifier X)}
    {d count : ℕ} (hvc : VCDimensionAtMost concepts d) (hcount : 0 < count)
    (hclassifier_measurable : ∀ classifier, classifier ∈ concepts → Measurable classifier)
    (error ghostSlack : ℝ) (hghostSlack : 0 ≤ ghostSlack)
    (hgap : 0 ≤ error - ghostSlack)
    (hpopulationBadMeasurable : MeasurableSet
      (finiteIIDVCPopulationOverestimateBadEvent law concepts count error))
    (htwoSampleMeasurable : MeasurableSet
      (finiteIIDVCTwoSampleBadEvent concepts count (error - ghostSlack)))
    (hpairSwapMeasurable : MeasurableSet
      (finiteIIDVCPairSwapBadEvent concepts count (error - ghostSlack)))
    (hproductMeasurable : MeasurableSet
      (finiteIIDVCTwoSampleProductBadEvent concepts count (error - ghostSlack))) :
    (1 - Real.exp (-((count : ℝ) * ghostSlack) ^ 2 /
        (2 * (count : ℝ) * (1 / 4 : ℝ)))) *
        (Probability.finiteIIDSampleLaw law count).real
          (finiteIIDVCPopulationOverestimateBadEvent law concepts count error) ≤
      (∑ k ∈ Finset.Iic d, (count + count).choose k : ℝ) *
        Real.exp (-((count : ℝ) * (error - ghostSlack)) ^ 2 /
          (2 * (count : ℝ))) := by
  exact (finiteIID_populationOverestimate_symmetrization_lower_of_ghostSlack
    law count hcount hclassifier_measurable error ghostSlack hghostSlack
    hpopulationBadMeasurable hproductMeasurable).trans
      (finiteIID_vc_twoSampleProductGap_upperTail law hvc hcount
        (error - ghostSlack) hgap htwoSampleMeasurable hpairSwapMeasurable hproductMeasurable)

/-- The two-sided population-versus-empirical error event for a VC class. -/
noncomputable def finiteIIDVCPopulationAbsoluteBadEvent
    {X : Type*} [MeasurableSpace X] (law : Measure (X × Bool))
    (concepts : Set (BinaryClassifier X)) (count : ℕ) (error : ℝ) :
    Set (Fin count → X × Bool) :=
  finiteIIDVCPopulationUnderestimateBadEvent law concepts count error ∪
    finiteIIDVCPopulationOverestimateBadEvent law concepts count error

/-- The two-sided event has exactly the source's absolute-error witness form. -/
theorem mem_finiteIIDVCPopulationAbsoluteBadEvent_iff
    {X : Type*} [MeasurableSpace X] (law : Measure (X × Bool))
    (concepts : Set (BinaryClassifier X)) (count : ℕ) (error : ℝ)
    (trainingSample : Fin count → X × Bool) :
    trainingSample ∈ finiteIIDVCPopulationAbsoluteBadEvent law concepts count error ↔
      ∃ classifier, classifier ∈ concepts ∧ error ≤
        |finiteBinaryEmpiricalError trainingSample classifier -
          binaryPopulationError law classifier| := by
  constructor
  · rintro (⟨classifier, hclassifier, hunderestimate⟩ | ⟨classifier, hclassifier,
      hoverestimate⟩)
    · refine ⟨classifier, hclassifier, (le_abs.mpr (Or.inr ?_))⟩
      simpa only [neg_sub] using hunderestimate
    · exact ⟨classifier, hclassifier, le_abs.mpr (Or.inl hoverestimate)⟩
  · rintro ⟨classifier, hclassifier, habs⟩
    rcases le_abs.mp habs with hoverestimate | hunderestimate
    · exact Or.inr ⟨classifier, hclassifier, hoverestimate⟩
    · exact Or.inl ⟨classifier, hclassifier, by
        simpa only [neg_sub] using hunderestimate⟩

/--
Fully checked two-sided VC uniform-convergence bound obtained from the
train/ghost symmetrization route in this file.  Its finite-sample constants
are intentionally retained exactly rather than being silently identified with
the stronger printed Vapnik constant.
-/
theorem finiteIID_vc_absolutePopulationError_symmetrization_bound
    {X : Type*} [MeasurableSpace X] (law : Measure (X × Bool))
    [IsProbabilityMeasure law] {concepts : Set (BinaryClassifier X)}
    {d count : ℕ} (hvc : VCDimensionAtMost concepts d) (hcount : 0 < count)
    (hclassifier_measurable : ∀ classifier, classifier ∈ concepts → Measurable classifier)
    (error : ℝ) (herror : 0 < error)
    (hunderestimateMeasurable : MeasurableSet
      (finiteIIDVCPopulationUnderestimateBadEvent law concepts count error))
    (hoverestimateMeasurable : MeasurableSet
      (finiteIIDVCPopulationOverestimateBadEvent law concepts count error))
    (htwoSampleMeasurable : MeasurableSet
      (finiteIIDVCTwoSampleBadEvent concepts count (error / 2)))
    (hpairSwapMeasurable : MeasurableSet
      (finiteIIDVCPairSwapBadEvent concepts count (error / 2)))
    (hproductMeasurable : MeasurableSet
      (finiteIIDVCTwoSampleProductBadEvent concepts count (error / 2))) :
    (Probability.finiteIIDSampleLaw law count).real
        (finiteIIDVCPopulationAbsoluteBadEvent law concepts count error) ≤
      2 * ((∑ k ∈ Finset.Iic d, (count + count).choose k : ℝ) *
        Real.exp (-((count : ℝ) * (error / 2)) ^ 2 / (2 * (count : ℝ)))) /
        (1 - Real.exp (-((count : ℝ) * (error / 2)) ^ 2 /
          (2 * (count : ℝ) * (1 / 4 : ℝ)))) := by
  letI : IsProbabilityMeasure (Probability.finiteIIDSampleLaw law count) := by
    dsimp [Probability.finiteIIDSampleLaw]
    infer_instance
  have hcountReal : 0 < (count : ℝ) := by
    exact_mod_cast hcount
  have hdenominatorPos : 0 < 1 - Real.exp (-((count : ℝ) * (error / 2)) ^ 2 /
      (2 * (count : ℝ) * (1 / 4 : ℝ))) := by
    have hbasePos : 0 < (count : ℝ) * (error / 2) := by positivity
    have hexponentNeg : -((count : ℝ) * (error / 2)) ^ 2 /
        (2 * (count : ℝ) * (1 / 4 : ℝ)) < 0 := by
      apply div_neg_of_neg_of_pos
      · exact neg_lt_zero.mpr (sq_pos_of_pos hbasePos)
      · positivity
    have hexpLtOne : Real.exp (-((count : ℝ) * (error / 2)) ^ 2 /
        (2 * (count : ℝ) * (1 / 4 : ℝ))) < 1 :=
      Real.exp_lt_one_iff.mpr hexponentNeg
    linarith
  have hunder := finiteIID_populationUnderestimate_symmetrization_vc_upper
    law hvc hcount hclassifier_measurable error herror.le hunderestimateMeasurable
      htwoSampleMeasurable hpairSwapMeasurable hproductMeasurable
  have hover := finiteIID_populationOverestimate_symmetrization_vc_upper
    law hvc hcount hclassifier_measurable error herror.le hoverestimateMeasurable
      htwoSampleMeasurable hpairSwapMeasurable hproductMeasurable
  have hunderDiv : (Probability.finiteIIDSampleLaw law count).real
      (finiteIIDVCPopulationUnderestimateBadEvent law concepts count error) ≤
      ((∑ k ∈ Finset.Iic d, (count + count).choose k : ℝ) *
        Real.exp (-((count : ℝ) * (error / 2)) ^ 2 / (2 * (count : ℝ)))) /
        (1 - Real.exp (-((count : ℝ) * (error / 2)) ^ 2 /
          (2 * (count : ℝ) * (1 / 4 : ℝ)))) :=
    (le_div_iff₀ hdenominatorPos).mpr (by simpa only [mul_comm] using hunder)
  have hoverDiv : (Probability.finiteIIDSampleLaw law count).real
      (finiteIIDVCPopulationOverestimateBadEvent law concepts count error) ≤
      ((∑ k ∈ Finset.Iic d, (count + count).choose k : ℝ) *
          Real.exp (-((count : ℝ) * (error / 2)) ^ 2 / (2 * (count : ℝ)))) /
          (1 - Real.exp (-((count : ℝ) * (error / 2)) ^ 2 /
            (2 * (count : ℝ) * (1 / 4 : ℝ)))) :=
    (le_div_iff₀ hdenominatorPos).mpr (by simpa only [mul_comm] using hover)
  change (Probability.finiteIIDSampleLaw law count).real
      (finiteIIDVCPopulationUnderestimateBadEvent law concepts count error ∪
        finiteIIDVCPopulationOverestimateBadEvent law concepts count error) ≤ _
  calc
    (Probability.finiteIIDSampleLaw law count).real
        (finiteIIDVCPopulationUnderestimateBadEvent law concepts count error ∪
          finiteIIDVCPopulationOverestimateBadEvent law concepts count error) ≤
        (Probability.finiteIIDSampleLaw law count).real
          (finiteIIDVCPopulationUnderestimateBadEvent law concepts count error) +
        (Probability.finiteIIDSampleLaw law count).real
          (finiteIIDVCPopulationOverestimateBadEvent law concepts count error) :=
      measureReal_union_le _ _
    _ ≤ ((∑ k ∈ Finset.Iic d, (count + count).choose k : ℝ) *
        Real.exp (-((count : ℝ) * (error / 2)) ^ 2 / (2 * (count : ℝ)))) /
        (1 - Real.exp (-((count : ℝ) * (error / 2)) ^ 2 /
          (2 * (count : ℝ) * (1 / 4 : ℝ)))) +
        ((∑ k ∈ Finset.Iic d, (count + count).choose k : ℝ) *
          Real.exp (-((count : ℝ) * (error / 2)) ^ 2 / (2 * (count : ℝ)))) /
          (1 - Real.exp (-((count : ℝ) * (error / 2)) ^ 2 /
            (2 * (count : ℝ) * (1 / 4 : ℝ)))) := add_le_add hunderDiv hoverDiv
    _ = 2 * ((∑ k ∈ Finset.Iic d, (count + count).choose k : ℝ) *
        Real.exp (-((count : ℝ) * (error / 2)) ^ 2 / (2 * (count : ℝ)))) /
        (1 - Real.exp (-((count : ℝ) * (error / 2)) ^ 2 /
          (2 * (count : ℝ) * (1 / 4 : ℝ)))) := by ring

/--
The quarter-ghost specialization of two-sided VC symmetrization.  Compared
with the half-split bound, its two-sample threshold is `3 * error / 4`, which
is the constant choice that reaches the `exp (-N * error^2 / 4)` source scale.
-/
theorem finiteIID_vc_absolutePopulationError_quarterGhost_bound
    {X : Type*} [MeasurableSpace X] (law : Measure (X × Bool))
    [IsProbabilityMeasure law] {concepts : Set (BinaryClassifier X)}
    {d count : ℕ} (hvc : VCDimensionAtMost concepts d) (hcount : 0 < count)
    (hclassifier_measurable : ∀ classifier, classifier ∈ concepts → Measurable classifier)
    (error : ℝ) (herror : 0 < error)
    (hunderestimateMeasurable : MeasurableSet
      (finiteIIDVCPopulationUnderestimateBadEvent law concepts count error))
    (hoverestimateMeasurable : MeasurableSet
      (finiteIIDVCPopulationOverestimateBadEvent law concepts count error))
    (htwoSampleMeasurable : MeasurableSet
      (finiteIIDVCTwoSampleBadEvent concepts count (error - error / 4)))
    (hpairSwapMeasurable : MeasurableSet
      (finiteIIDVCPairSwapBadEvent concepts count (error - error / 4)))
    (hproductMeasurable : MeasurableSet
      (finiteIIDVCTwoSampleProductBadEvent concepts count (error - error / 4))) :
    (Probability.finiteIIDSampleLaw law count).real
        (finiteIIDVCPopulationAbsoluteBadEvent law concepts count error) ≤
      2 * ((∑ k ∈ Finset.Iic d, (count + count).choose k : ℝ) *
        Real.exp (-((count : ℝ) * (error - error / 4)) ^ 2 /
          (2 * (count : ℝ)))) /
        (1 - Real.exp (-((count : ℝ) * (error / 4)) ^ 2 /
          (2 * (count : ℝ) * (1 / 4 : ℝ)))) := by
  letI : IsProbabilityMeasure (Probability.finiteIIDSampleLaw law count) := by
    dsimp [Probability.finiteIIDSampleLaw]
    infer_instance
  have hcountReal : 0 < (count : ℝ) := by exact_mod_cast hcount
  have hghostSlack : 0 ≤ error / 4 := by linarith
  have hgap : 0 ≤ error - error / 4 := by linarith
  have hdenominatorPos : 0 < 1 - Real.exp (-((count : ℝ) * (error / 4)) ^ 2 /
      (2 * (count : ℝ) * (1 / 4 : ℝ))) := by
    have hbasePos : 0 < (count : ℝ) * (error / 4) := by positivity
    have hexponentNeg : -((count : ℝ) * (error / 4)) ^ 2 /
        (2 * (count : ℝ) * (1 / 4 : ℝ)) < 0 := by
      apply div_neg_of_neg_of_pos
      · exact neg_lt_zero.mpr (sq_pos_of_pos hbasePos)
      · positivity
    have hexpLtOne : Real.exp (-((count : ℝ) * (error / 4)) ^ 2 /
        (2 * (count : ℝ) * (1 / 4 : ℝ))) < 1 :=
      Real.exp_lt_one_iff.mpr hexponentNeg
    linarith
  have hunder := finiteIID_populationUnderestimate_symmetrization_vc_upper_of_ghostSlack
    law hvc hcount hclassifier_measurable error (error / 4) hghostSlack hgap
      hunderestimateMeasurable htwoSampleMeasurable hpairSwapMeasurable hproductMeasurable
  have hover := finiteIID_populationOverestimate_symmetrization_vc_upper_of_ghostSlack
    law hvc hcount hclassifier_measurable error (error / 4) hghostSlack hgap
      hoverestimateMeasurable htwoSampleMeasurable hpairSwapMeasurable hproductMeasurable
  have hunderDiv : (Probability.finiteIIDSampleLaw law count).real
      (finiteIIDVCPopulationUnderestimateBadEvent law concepts count error) ≤
      ((∑ k ∈ Finset.Iic d, (count + count).choose k : ℝ) *
        Real.exp (-((count : ℝ) * (error - error / 4)) ^ 2 /
          (2 * (count : ℝ)))) /
        (1 - Real.exp (-((count : ℝ) * (error / 4)) ^ 2 /
          (2 * (count : ℝ) * (1 / 4 : ℝ)))) :=
    (le_div_iff₀ hdenominatorPos).mpr (by simpa only [mul_comm] using hunder)
  have hoverDiv : (Probability.finiteIIDSampleLaw law count).real
      (finiteIIDVCPopulationOverestimateBadEvent law concepts count error) ≤
      ((∑ k ∈ Finset.Iic d, (count + count).choose k : ℝ) *
        Real.exp (-((count : ℝ) * (error - error / 4)) ^ 2 /
          (2 * (count : ℝ)))) /
        (1 - Real.exp (-((count : ℝ) * (error / 4)) ^ 2 /
          (2 * (count : ℝ) * (1 / 4 : ℝ)))) :=
    (le_div_iff₀ hdenominatorPos).mpr (by simpa only [mul_comm] using hover)
  change (Probability.finiteIIDSampleLaw law count).real
      (finiteIIDVCPopulationUnderestimateBadEvent law concepts count error ∪
        finiteIIDVCPopulationOverestimateBadEvent law concepts count error) ≤ _
  calc
    (Probability.finiteIIDSampleLaw law count).real
        (finiteIIDVCPopulationUnderestimateBadEvent law concepts count error ∪
          finiteIIDVCPopulationOverestimateBadEvent law concepts count error) ≤
        (Probability.finiteIIDSampleLaw law count).real
          (finiteIIDVCPopulationUnderestimateBadEvent law concepts count error) +
        (Probability.finiteIIDSampleLaw law count).real
          (finiteIIDVCPopulationOverestimateBadEvent law concepts count error) :=
      measureReal_union_le _ _
    _ ≤ ((∑ k ∈ Finset.Iic d, (count + count).choose k : ℝ) *
        Real.exp (-((count : ℝ) * (error - error / 4)) ^ 2 /
          (2 * (count : ℝ)))) /
        (1 - Real.exp (-((count : ℝ) * (error / 4)) ^ 2 /
          (2 * (count : ℝ) * (1 / 4 : ℝ)))) +
        ((∑ k ∈ Finset.Iic d, (count + count).choose k : ℝ) *
          Real.exp (-((count : ℝ) * (error - error / 4)) ^ 2 /
            (2 * (count : ℝ)))) /
          (1 - Real.exp (-((count : ℝ) * (error / 4)) ^ 2 /
            (2 * (count : ℝ) * (1 / 4 : ℝ)))) := add_le_add hunderDiv hoverDiv
    _ = 2 * ((∑ k ∈ Finset.Iic d, (count + count).choose k : ℝ) *
        Real.exp (-((count : ℝ) * (error - error / 4)) ^ 2 /
          (2 * (count : ℝ)))) /
        (1 - Real.exp (-((count : ℝ) * (error / 4)) ^ 2 /
          (2 * (count : ℝ) * (1 / 4 : ℝ)))) := by ring

/--
At the quarter-ghost split, a sufficiently large squared error makes the
favorable ghost-section probability at least `2/3`; the resulting two-sided
VC bound has the source-scale exponent `-N * error^2 / 4`.
-/
theorem finiteIID_vc_absolutePopulationError_sourceScale_exponential_bound
    {X : Type*} [MeasurableSpace X] (law : Measure (X × Bool))
    [IsProbabilityMeasure law] {concepts : Set (BinaryClassifier X)}
    {d count : ℕ} (hvc : VCDimensionAtMost concepts d) (hcount : 0 < count)
    (hclassifier_measurable : ∀ classifier, classifier ∈ concepts → Measurable classifier)
    (error : ℝ) (herror : 0 < error)
    (hlarge : 8 * Real.log 3 ≤ (count : ℝ) * error ^ 2)
    (hunderestimateMeasurable : MeasurableSet
      (finiteIIDVCPopulationUnderestimateBadEvent law concepts count error))
    (hoverestimateMeasurable : MeasurableSet
      (finiteIIDVCPopulationOverestimateBadEvent law concepts count error))
    (htwoSampleMeasurable : MeasurableSet
      (finiteIIDVCTwoSampleBadEvent concepts count (error - error / 4)))
    (hpairSwapMeasurable : MeasurableSet
      (finiteIIDVCPairSwapBadEvent concepts count (error - error / 4)))
    (hproductMeasurable : MeasurableSet
      (finiteIIDVCTwoSampleProductBadEvent concepts count (error - error / 4))) :
    (Probability.finiteIIDSampleLaw law count).real
        (finiteIIDVCPopulationAbsoluteBadEvent law concepts count error) ≤
      3 * (∑ k ∈ Finset.Iic d, (count + count).choose k : ℝ) *
        Real.exp (-((count : ℝ) * error ^ 2 / 4)) := by
  letI : IsProbabilityMeasure (Probability.finiteIIDSampleLaw law count) := by
    dsimp [Probability.finiteIIDSampleLaw]
    infer_instance
  have hcountReal : 0 < (count : ℝ) := by exact_mod_cast hcount
  have hquarter := finiteIID_vc_absolutePopulationError_quarterGhost_bound
    law hvc hcount hclassifier_measurable error herror hunderestimateMeasurable
      hoverestimateMeasurable htwoSampleMeasurable hpairSwapMeasurable hproductMeasurable
  have hquarterExponent : -((count : ℝ) * (error / 4)) ^ 2 /
      (2 * (count : ℝ) * (1 / 4 : ℝ)) = -((count : ℝ) * error ^ 2 / 8) := by
    field_simp [hcountReal.ne']
    ring
  have hgapExponent : -((count : ℝ) * (error - error / 4)) ^ 2 /
      (2 * (count : ℝ)) = -(9 * (count : ℝ) * error ^ 2 / 32) := by
    field_simp [hcountReal.ne']
    ring
  let trace : ℝ := ∑ k ∈ Finset.Iic d, (count + count).choose k
  let denominator : ℝ := 1 - Real.exp (-((count : ℝ) * error ^ 2 / 8))
  have hquarterExpLeThird : Real.exp (-((count : ℝ) * error ^ 2 / 8)) ≤ 1 / 3 := by
    have hexponentLe : -((count : ℝ) * error ^ 2 / 8) ≤ -Real.log 3 := by
      nlinarith
    calc
      Real.exp (-((count : ℝ) * error ^ 2 / 8)) ≤ Real.exp (-Real.log 3) :=
        Real.exp_monotone hexponentLe
      _ = 1 / 3 := by
        rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
        norm_num
  have hdenominatorLower : 2 / 3 ≤ denominator := by
    dsimp [denominator]
    linarith
  have hdenominatorPos : 0 < denominator := by linarith
  have htailExponentLe : -(9 * (count : ℝ) * error ^ 2 / 32) ≤
      -((count : ℝ) * error ^ 2 / 4) := by
    have hnonneg : 0 ≤ (count : ℝ) * error ^ 2 := by positivity
    nlinarith
  have htailLe : Real.exp (-(9 * (count : ℝ) * error ^ 2 / 32)) ≤
      Real.exp (-((count : ℝ) * error ^ 2 / 4)) :=
    Real.exp_monotone htailExponentLe
  have htraceNonneg : 0 ≤ trace := by
    dsimp [trace]
    positivity
  have htailNonneg : 0 ≤ Real.exp (-((count : ℝ) * error ^ 2 / 4)) :=
    (Real.exp_pos _).le
  have hnumerator : 2 * (trace * Real.exp (-(9 * (count : ℝ) * error ^ 2 / 32))) ≤
      2 * (trace * Real.exp (-((count : ℝ) * error ^ 2 / 4))) := by
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left htailLe htraceNonneg) (by norm_num)
  have hquotient : 2 * (trace * Real.exp (-((count : ℝ) * error ^ 2 / 4))) /
      denominator ≤ 3 * trace * Real.exp (-((count : ℝ) * error ^ 2 / 4)) := by
    apply (div_le_iff₀ hdenominatorPos).mpr
    have hscaled := mul_le_mul_of_nonneg_left hdenominatorLower
      (show 0 ≤ trace * Real.exp (-((count : ℝ) * error ^ 2 / 4)) by positivity)
    nlinarith
  calc
    (Probability.finiteIIDSampleLaw law count).real
        (finiteIIDVCPopulationAbsoluteBadEvent law concepts count error) ≤
        2 * (trace * Real.exp (-(9 * (count : ℝ) * error ^ 2 / 32))) /
          denominator := by
      simpa only [trace, denominator, hquarterExponent, hgapExponent] using hquarter
    _ ≤ 2 * (trace * Real.exp (-((count : ℝ) * error ^ 2 / 4))) /
          denominator :=
      (div_le_div_iff_of_pos_right hdenominatorPos).mpr hnumerator
    _ ≤ 3 * trace * Real.exp (-((count : ℝ) * error ^ 2 / 4)) := hquotient

/--
Combining the source-scale two-sample tail with the sharp binomial VC-growth
envelope gives the entropy form of the uniform-convergence exponent.  The
range `0 < d ≤ 2N` is exactly the range in which that binomial envelope uses
the displayed `d (log (2N / d) + 1)` term.
-/
theorem finiteIID_vc_absolutePopulationError_source_entropy_bound
    {X : Type*} [MeasurableSpace X] (law : Measure (X × Bool))
    [IsProbabilityMeasure law] {concepts : Set (BinaryClassifier X)}
    {d count : ℕ} (hvc : VCDimensionAtMost concepts d) (hcount : 0 < count)
    (hd : 0 < d) (hdcount : d ≤ count + count)
    (hclassifier_measurable : ∀ classifier, classifier ∈ concepts → Measurable classifier)
    (error : ℝ) (herror : 0 < error)
    (hlarge : 8 * Real.log 3 ≤ (count : ℝ) * error ^ 2)
    (hunderestimateMeasurable : MeasurableSet
      (finiteIIDVCPopulationUnderestimateBadEvent law concepts count error))
    (hoverestimateMeasurable : MeasurableSet
      (finiteIIDVCPopulationOverestimateBadEvent law concepts count error))
    (htwoSampleMeasurable : MeasurableSet
      (finiteIIDVCTwoSampleBadEvent concepts count (error - error / 4)))
    (hpairSwapMeasurable : MeasurableSet
      (finiteIIDVCPairSwapBadEvent concepts count (error - error / 4)))
    (hproductMeasurable : MeasurableSet
      (finiteIIDVCTwoSampleProductBadEvent concepts count (error - error / 4))) :
    (Probability.finiteIIDSampleLaw law count).real
        (finiteIIDVCPopulationAbsoluteBadEvent law concepts count error) ≤
      3 * Real.exp ((d : ℝ) * (Real.log ((count + count : ℕ) / (d : ℝ)) + 1) -
        (count : ℝ) * error ^ 2 / 4) := by
  have hbase := finiteIID_vc_absolutePopulationError_sourceScale_exponential_bound
    law hvc hcount hclassifier_measurable error herror hlarge hunderestimateMeasurable
      hoverestimateMeasurable htwoSampleMeasurable hpairSwapMeasurable hproductMeasurable
  have hsum := sum_choose_le_exp_mul_log_div_add_one
    (n := count + count) hd hdcount
  calc
    (Probability.finiteIIDSampleLaw law count).real
        (finiteIIDVCPopulationAbsoluteBadEvent law concepts count error) ≤
        3 * (∑ k ∈ Finset.Iic d, (count + count).choose k : ℝ) *
          Real.exp (-((count : ℝ) * error ^ 2 / 4)) := hbase
    _ ≤ 3 * Real.exp ((d : ℝ) *
          (Real.log ((count + count : ℕ) / (d : ℝ)) + 1)) *
          Real.exp (-((count : ℝ) * error ^ 2 / 4)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsum (by norm_num)) (Real.exp_pos _).le
    _ = 3 * Real.exp ((d : ℝ) *
          (Real.log ((count + count : ℕ) / (d : ℝ)) + 1) -
            (count : ℝ) * error ^ 2 / 4) := by
      rw [show 3 * Real.exp ((d : ℝ) *
            (Real.log ((count + count : ℕ) / (d : ℝ)) + 1)) *
              Real.exp (-((count : ℝ) * error ^ 2 / 4)) =
            3 * (Real.exp ((d : ℝ) *
              (Real.log ((count + count : ℕ) / (d : ℝ)) + 1)) *
                Real.exp (-((count : ℝ) * error ^ 2 / 4))) by ring]
      rw [← Real.exp_add]
      congr 1

/-- The confidence radius displayed in the quoted Vapnik generalization bound. -/
noncomputable def finiteIIDVCSourceConfidenceRadius (d count : ℕ) (delta : ℝ) : ℝ :=
  2 * Real.sqrt (((d : ℝ) * (Real.log ((count + count : ℕ) / (d : ℝ)) + 1) +
    Real.log (9 / delta)) / (count : ℝ))

/--
The nontrivial confidence-range form of the quoted Vapnik bound.  The explicit
`0 < d ≤ 2N` conditions make its logarithm and the sharp growth envelope
well-defined; the named event-measurability witnesses are the permissible-class
condition needed for an arbitrary, possibly infinite, hypothesis class.
-/
theorem finiteIID_vc_absolutePopulationError_source_confidence_bound
    {X : Type*} [MeasurableSpace X] (law : Measure (X × Bool))
    [IsProbabilityMeasure law] {concepts : Set (BinaryClassifier X)}
    {d count : ℕ} (hvc : VCDimensionAtMost concepts d) (hcount : 0 < count)
    (hd : 0 < d) (hdcount : d ≤ count + count)
    (hclassifier_measurable : ∀ classifier, classifier ∈ concepts → Measurable classifier)
    (delta : ℝ) (hdelta : 0 < delta) (hdeltaone : delta ≤ 1)
    (hunderestimateMeasurable : MeasurableSet
      (finiteIIDVCPopulationUnderestimateBadEvent law concepts count
        (finiteIIDVCSourceConfidenceRadius d count delta)))
    (hoverestimateMeasurable : MeasurableSet
      (finiteIIDVCPopulationOverestimateBadEvent law concepts count
        (finiteIIDVCSourceConfidenceRadius d count delta)))
    (htwoSampleMeasurable : MeasurableSet
      (finiteIIDVCTwoSampleBadEvent concepts count
        (finiteIIDVCSourceConfidenceRadius d count delta -
          finiteIIDVCSourceConfidenceRadius d count delta / 4)))
    (hpairSwapMeasurable : MeasurableSet
      (finiteIIDVCPairSwapBadEvent concepts count
        (finiteIIDVCSourceConfidenceRadius d count delta -
          finiteIIDVCSourceConfidenceRadius d count delta / 4)))
    (hproductMeasurable : MeasurableSet
      (finiteIIDVCTwoSampleProductBadEvent concepts count
        (finiteIIDVCSourceConfidenceRadius d count delta -
          finiteIIDVCSourceConfidenceRadius d count delta / 4))) :
    (Probability.finiteIIDSampleLaw law count).real
        (finiteIIDVCPopulationAbsoluteBadEvent law concepts count
          (finiteIIDVCSourceConfidenceRadius d count delta)) ≤ delta := by
  let complexity : ℝ :=
    (d : ℝ) * (Real.log ((count + count : ℕ) / (d : ℝ)) + 1)
  let budget : ℝ := complexity + Real.log (9 / delta)
  let epsilon : ℝ := 2 * Real.sqrt (budget / (count : ℝ))
  change (Probability.finiteIIDSampleLaw law count).real
      (finiteIIDVCPopulationAbsoluteBadEvent law concepts count epsilon) ≤ delta
  have hcountReal : 0 < (count : ℝ) := by
    exact_mod_cast hcount
  have hdReal : 0 < (d : ℝ) := by
    exact_mod_cast hd
  have hlogratio : 0 ≤ Real.log ((count + count : ℕ) / (d : ℝ)) := by
    apply Real.log_nonneg
    apply (le_div_iff₀ hdReal).mpr
    have hcast : (d : ℝ) ≤ ((count + count : ℕ) : ℝ) := by
      exact_mod_cast hdcount
    nlinarith
  have hcomplexity : 0 ≤ complexity := by
    dsimp [complexity]
    positivity
  have hlogbudget : 2 * Real.log 3 ≤ Real.log (9 / delta) := by
    have hlogdelta : Real.log delta ≤ 0 := Real.log_nonpos hdelta.le hdeltaone
    have hnine : Real.log (9 : ℝ) = 2 * Real.log 3 := by
      have h : (9 : ℝ) = 3 ^ (2 : ℕ) := by norm_num
      rw [h, Real.log_pow]
      norm_num
    rw [Real.log_div (by norm_num) hdelta.ne', hnine]
    linarith
  have hbudgetLarge : 2 * Real.log 3 ≤ budget := by
    dsimp [budget]
    linarith
  have hlogthree : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hbudgetPos : 0 < budget := by linarith
  have hbudgetNonneg : 0 ≤ budget := hbudgetPos.le
  have hepsilonPos : 0 < epsilon := by
    dsimp [epsilon]
    positivity
  have hepsilonSq : (count : ℝ) * epsilon ^ 2 / 4 = budget := by
    dsimp [epsilon]
    have hsquare : Real.sqrt (budget / (count : ℝ)) ^ 2 = budget / (count : ℝ) :=
      Real.sq_sqrt (by positivity)
    rw [show (2 * Real.sqrt (budget / (count : ℝ))) ^ 2 =
      4 * Real.sqrt (budget / (count : ℝ)) ^ 2 by ring, hsquare]
    field_simp [hcountReal.ne']
  have hlarge : 8 * Real.log 3 ≤ (count : ℝ) * epsilon ^ 2 := by
    nlinarith [hepsilonSq, hbudgetLarge]
  have htail := finiteIID_vc_absolutePopulationError_source_entropy_bound
    law hvc hcount hd hdcount hclassifier_measurable epsilon hepsilonPos hlarge
      hunderestimateMeasurable hoverestimateMeasurable htwoSampleMeasurable
        hpairSwapMeasurable hproductMeasurable
  have htailValue :
      3 * Real.exp (complexity - (count : ℝ) * epsilon ^ 2 / 4) = delta / 3 := by
    rw [hepsilonSq]
    have hpositive : 0 < 9 / delta := by positivity
    dsimp [budget]
    rw [show complexity - (complexity + Real.log (9 / delta)) =
      -Real.log (9 / delta) by ring, Real.exp_neg, Real.exp_log hpositive]
    field_simp [hdelta.ne']
    ring
  calc
    (Probability.finiteIIDSampleLaw law count).real
        (finiteIIDVCPopulationAbsoluteBadEvent law concepts count epsilon) ≤
        3 * Real.exp (complexity - (count : ℝ) * epsilon ^ 2 / 4) := by
      exact htail
    _ = delta / 3 := htailValue
    _ ≤ delta := by nlinarith

/--
Strict-event form of the source confidence bound.  The preceding theorem
bounds the closed `radius ≤ |empirical - population|` event; the source's
strict event is its subset.
-/
theorem finiteIID_vc_generalization_theorem7_of_confidence
    {X : Type*} [MeasurableSpace X] (law : Measure (X × Bool))
    [IsProbabilityMeasure law] {concepts : Set (BinaryClassifier X)}
    {d count : ℕ} (hvc : VCDimensionAtMost concepts d) (hcount : 0 < count)
    (hd : 0 < d) (hdcount : d ≤ count + count)
    (hclassifier_measurable : ∀ classifier, classifier ∈ concepts → Measurable classifier)
    (delta : ℝ) (hdelta : 0 < delta) (hdeltaone : delta ≤ 1)
    (hunderestimateMeasurable : MeasurableSet
      (finiteIIDVCPopulationUnderestimateBadEvent law concepts count
        (finiteIIDVCSourceConfidenceRadius d count delta)))
    (hoverestimateMeasurable : MeasurableSet
      (finiteIIDVCPopulationOverestimateBadEvent law concepts count
        (finiteIIDVCSourceConfidenceRadius d count delta)))
    (htwoSampleMeasurable : MeasurableSet
      (finiteIIDVCTwoSampleBadEvent concepts count
        (finiteIIDVCSourceConfidenceRadius d count delta -
          finiteIIDVCSourceConfidenceRadius d count delta / 4)))
    (hpairSwapMeasurable : MeasurableSet
      (finiteIIDVCPairSwapBadEvent concepts count
        (finiteIIDVCSourceConfidenceRadius d count delta -
          finiteIIDVCSourceConfidenceRadius d count delta / 4)))
    (hproductMeasurable : MeasurableSet
      (finiteIIDVCTwoSampleProductBadEvent concepts count
        (finiteIIDVCSourceConfidenceRadius d count delta -
          finiteIIDVCSourceConfidenceRadius d count delta / 4))) :
    (Probability.finiteIIDSampleLaw law count).real {trainingSample |
      ∃ classifier, classifier ∈ concepts ∧
        finiteIIDVCSourceConfidenceRadius d count delta <
          |finiteBinaryEmpiricalError trainingSample classifier -
            binaryPopulationError law classifier|} ≤ delta := by
  letI : IsProbabilityMeasure (Probability.finiteIIDSampleLaw law count) := by
    dsimp [Probability.finiteIIDSampleLaw]
    infer_instance
  have hclosed := finiteIID_vc_absolutePopulationError_source_confidence_bound
    law hvc hcount hd hdcount hclassifier_measurable delta hdelta hdeltaone
      hunderestimateMeasurable hoverestimateMeasurable htwoSampleMeasurable
        hpairSwapMeasurable hproductMeasurable
  have hsubset : {trainingSample | ∃ classifier, classifier ∈ concepts ∧
      finiteIIDVCSourceConfidenceRadius d count delta <
        |finiteBinaryEmpiricalError trainingSample classifier -
          binaryPopulationError law classifier|} ⊆
      finiteIIDVCPopulationAbsoluteBadEvent law concepts count
        (finiteIIDVCSourceConfidenceRadius d count delta) := by
    intro trainingSample hstrict
    rw [mem_finiteIIDVCPopulationAbsoluteBadEvent_iff]
    rcases hstrict with ⟨classifier, hclassifier, hgap⟩
    exact ⟨classifier, hclassifier, le_of_lt hgap⟩
  exact (measureReal_mono hsubset (measure_ne_top _ _)).trans hclosed

/--
Source-facing form of Theorem 7 as quoted in Freund--Schapire: for every
positive confidence parameter, the probability of a classifier whose empirical
and population errors differ by more than the displayed VC radius is at most
that parameter.  The nontrivial `0 < delta ≤ 1` case is proved above; for
`delta > 1` this follows from probability normalization.
-/
theorem finiteIID_vc_generalization_theorem7
    {X : Type*} [MeasurableSpace X] (law : Measure (X × Bool))
    [IsProbabilityMeasure law] {concepts : Set (BinaryClassifier X)}
    {d count : ℕ} (hvc : VCDimensionAtMost concepts d) (hcount : 0 < count)
    (hd : 0 < d) (hdcount : d ≤ count + count)
    (hclassifier_measurable : ∀ classifier, classifier ∈ concepts → Measurable classifier)
    (delta : ℝ) (hdelta : 0 < delta)
    (hunderestimateMeasurable : MeasurableSet
      (finiteIIDVCPopulationUnderestimateBadEvent law concepts count
        (finiteIIDVCSourceConfidenceRadius d count delta)))
    (hoverestimateMeasurable : MeasurableSet
      (finiteIIDVCPopulationOverestimateBadEvent law concepts count
        (finiteIIDVCSourceConfidenceRadius d count delta)))
    (htwoSampleMeasurable : MeasurableSet
      (finiteIIDVCTwoSampleBadEvent concepts count
        (finiteIIDVCSourceConfidenceRadius d count delta -
          finiteIIDVCSourceConfidenceRadius d count delta / 4)))
    (hpairSwapMeasurable : MeasurableSet
      (finiteIIDVCPairSwapBadEvent concepts count
        (finiteIIDVCSourceConfidenceRadius d count delta -
          finiteIIDVCSourceConfidenceRadius d count delta / 4)))
    (hproductMeasurable : MeasurableSet
      (finiteIIDVCTwoSampleProductBadEvent concepts count
        (finiteIIDVCSourceConfidenceRadius d count delta -
          finiteIIDVCSourceConfidenceRadius d count delta / 4))) :
    (Probability.finiteIIDSampleLaw law count).real {trainingSample |
      ∃ classifier, classifier ∈ concepts ∧
        finiteIIDVCSourceConfidenceRadius d count delta <
          |finiteBinaryEmpiricalError trainingSample classifier -
            binaryPopulationError law classifier|} ≤ delta := by
  letI : IsProbabilityMeasure (Probability.finiteIIDSampleLaw law count) := by
    dsimp [Probability.finiteIIDSampleLaw]
    infer_instance
  by_cases hdeltaone : delta ≤ 1
  · exact finiteIID_vc_generalization_theorem7_of_confidence
      law hvc hcount hd hdcount hclassifier_measurable delta hdelta hdeltaone
        hunderestimateMeasurable hoverestimateMeasurable htwoSampleMeasurable
          hpairSwapMeasurable hproductMeasurable
  · exact (measureReal_le_one (μ := Probability.finiteIIDSampleLaw law count)).trans
      (le_of_lt (lt_of_not_ge hdeltaone))

/--
Finite-class binary generalization under iid examples.  The source's iid
condition is split into independence and coordinate-wise identical
distribution, so the equality between every coordinate's expected loss and
the population error is a proved bridge.
-/
theorem finite_uniform_binaryClassification_generalization
    {Ω X Hypothesis : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Fintype Hypothesis]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (sample : ℕ → Ω → X × Bool) (count : ℕ) (hcount : 0 < count)
    (hindependent : iIndepFun sample law)
    (hidentical : ∀ index, IdentDistrib (sample index) (sample 0) law law)
    (hsample_measurable : ∀ index, Measurable (sample index))
    (classifier : Hypothesis → BinaryClassifier X)
    (hclassifier_measurable : ∀ hypothesis, Measurable (classifier hypothesis))
    (error : ℝ) (herror : 0 ≤ error) :
    law.real {outcome | ∃ hypothesis,
      error < |Probability.empiricalMean
          (fun h index omega => binaryClassificationLoss (classifier h) (sample index omega))
          count hypothesis outcome -
        Probability.populationMean law
          (fun h index omega => binaryClassificationLoss (classifier h) (sample index omega))
          hypothesis|} ≤
      (Fintype.card Hypothesis : ℝ) * 2 *
        Real.exp (-((count : ℝ) * error) ^ 2 /
          (2 * (count : ℝ) * (1 / 4 : ℝ))) := by
  apply Probability.finite_uniform_empiricalMean_abs_gt law
    (fun h index omega => binaryClassificationLoss (classifier h) (sample index omega))
    count hcount
  · intro hypothesis
    simpa [Function.comp_def] using
      hindependent.comp
        (fun _ datum => binaryClassificationLoss (classifier hypothesis) datum)
        (fun _ => measurable_binaryClassificationLoss (classifier hypothesis)
          (hclassifier_measurable hypothesis))
  · intro hypothesis index
    have hcomp := (hidentical index).comp
      (measurable_binaryClassificationLoss (classifier hypothesis)
        (hclassifier_measurable hypothesis))
    simpa [Function.comp_def] using hcomp.integral_eq
  · intro hypothesis index
    exact (measurable_binaryClassificationLoss (classifier hypothesis)
      (hclassifier_measurable hypothesis)).comp (hsample_measurable index)
  · intro hypothesis index _
    filter_upwards with outcome
    exact binaryClassificationLoss_mem_Icc (classifier hypothesis) (sample index outcome)
  · exact herror

/-- The finite binary-class generalization bound with exponent `-2 N ε²`. -/
theorem finite_uniform_binaryClassification_generalization_exp_neg_two_mul
    {Ω X Hypothesis : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Fintype Hypothesis]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (sample : ℕ → Ω → X × Bool) (count : ℕ) (hcount : 0 < count)
    (hindependent : iIndepFun sample law)
    (hidentical : ∀ index, IdentDistrib (sample index) (sample 0) law law)
    (hsample_measurable : ∀ index, Measurable (sample index))
    (classifier : Hypothesis → BinaryClassifier X)
    (hclassifier_measurable : ∀ hypothesis, Measurable (classifier hypothesis))
    (error : ℝ) (herror : 0 ≤ error) :
    law.real {outcome | ∃ hypothesis,
      error < |Probability.empiricalMean
          (fun h index omega => binaryClassificationLoss (classifier h) (sample index omega))
          count hypothesis outcome -
        Probability.populationMean law
          (fun h index omega => binaryClassificationLoss (classifier h) (sample index omega))
          hypothesis|} ≤
      (Fintype.card Hypothesis : ℝ) * 2 *
        Real.exp (-2 * (count : ℝ) * error ^ 2) := by
  simpa only [Probability.boundedHoeffdingExponent_eq_neg_two_mul count hcount error] using
    finite_uniform_binaryClassification_generalization law sample count hcount hindependent
      hidentical hsample_measurable classifier hclassifier_measurable error herror

end Statistics
end AppliedModelingLib
