import AppliedModelingLib.Foundations.Probability.FiniteExpectation
import AppliedModelingLib.Foundations.Probability.OrderStatistics
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

open scoped BigOperators

namespace PRPKG24AccuracyDiversity

noncomputable section

/--
Candidate index sets for the sum of the best `k` values.  We use "at most
`k`" rather than "exactly `k`"; under the nonnegative value assumptions used in
Theorem 1(i), this agrees with the paper's top-`k` sum and gives a cleaner
finite maximization interface.
-/
def topKCandidateSets (ι : Type*) [Fintype ι] [DecidableEq ι] (k : ℕ) :
    Finset (Finset ι) := (Finset.univ : Finset ι).powerset.filter (fun s => s.card ≤ k)

theorem topKCandidateSets_nonempty
    (ι : Type*) [Fintype ι] [DecidableEq ι] (k : ℕ) :
    (topKCandidateSets ι k).Nonempty := by
  classical
  simpa [topKCandidateSets, AppliedModelingLib.Probability.topKCandidateSets] using
    AppliedModelingLib.Probability.topKCandidateSets_nonempty ι k

/-- Sum of the best at-most-`k` values over a finite sample. -/
def topKSumOn {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (v : ι → ℝ) : ℝ :=
  (topKCandidateSets ι k).sup' (topKCandidateSets_nonempty ι k)
    (fun s => ∑ i ∈ s, v i)

/-- A concrete candidate set is bounded by the top-`k` value. -/
theorem sum_le_topKSumOn {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (v : ι → ℝ) (s : Finset ι) (hs_card : s.card ≤ k) :
    (∑ i ∈ s, v i) ≤ topKSumOn k v := by
  classical
  simpa [topKSumOn, AppliedModelingLib.Probability.topKSumOn,
    topKCandidateSets, AppliedModelingLib.Probability.topKCandidateSets] using
    AppliedModelingLib.Probability.sum_le_topKSumOn (ι := ι) k v s hs_card

/-- The empty candidate makes the at-most-`k` top value nonnegative. -/
theorem topKSumOn_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (v : ι → ℝ) :
    0 ≤ topKSumOn k v := by
  classical
  simpa [topKSumOn, AppliedModelingLib.Probability.topKSumOn,
    topKCandidateSets, AppliedModelingLib.Probability.topKCandidateSets] using
    AppliedModelingLib.Probability.topKSumOn_nonneg (ι := ι) k v

/-- Reindexing the finite sample does not change its top-`k` sum. -/
theorem topKSumOn_comp_equiv {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (k : ℕ) (v : κ → ℝ) :
    topKSumOn k (fun i : ι => v (e i)) = topKSumOn k v := by
  classical
  simpa [topKSumOn, AppliedModelingLib.Probability.topKSumOn,
    topKCandidateSets, AppliedModelingLib.Probability.topKCandidateSets] using
    AppliedModelingLib.Probability.topKSumOn_comp_equiv (e := e) (k := k) (v := v)

theorem finset_sum_le_card_mul_of_forall_le {ι : Type*}
    (s : Finset ι) (v : ι → ℝ) (C : ℝ)
    (h : ∀ i ∈ s, v i ≤ C) :
    (∑ i ∈ s, v i) ≤ (s.card : ℝ) * C := by
  exact AppliedModelingLib.FiniteSum.finset_sum_le_card_mul_of_forall_le s v C h

/-- If every sample value is at most `C`, then the top-`k` sum is at most `k*C`. -/
theorem topKSumOn_le_card_mul_of_forall_le {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (k : ℕ) (v : ι → ℝ) {C : ℝ}
    (hC_nonneg : 0 ≤ C) (h_le : ∀ i, v i ≤ C) :
    topKSumOn k v ≤ (k : ℝ) * C := by
  classical
  simpa [topKSumOn, AppliedModelingLib.Probability.topKSumOn,
    topKCandidateSets, AppliedModelingLib.Probability.topKCandidateSets] using
    AppliedModelingLib.Probability.topKSumOn_le_card_mul_of_forall_le
      (ι := ι) k v hC_nonneg h_le

/-- A witnessed set of `k` top values pins the top-`k` sum to `k * xTop`. -/
theorem topKSumOn_eq_card_mul_of_top_witness {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (k : ℕ) (v : ι → ℝ) {xTop : ℝ}
    (hxTop_nonneg : 0 ≤ xTop) (h_le : ∀ i, v i ≤ xTop)
    (sTop : Finset ι) (hsTop_card : sTop.card = k)
    (hsTop_value : ∀ i ∈ sTop, v i = xTop) :
    topKSumOn k v = (k : ℝ) * xTop := by
  classical
  simpa [topKSumOn, AppliedModelingLib.Probability.topKSumOn,
    topKCandidateSets, AppliedModelingLib.Probability.topKCandidateSets] using
    AppliedModelingLib.Probability.topKSumOn_eq_card_mul_of_top_witness
      (ι := ι) k v hxTop_nonneg h_le sTop hsTop_card hsTop_value

/-- The sample has at least `k` entries equal to the top support value. -/
def hasKTopValues {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (xTop : ℝ) (v : ι → ℝ) : Prop := ∃ s : Finset ι, s.card = k ∧ ∀ i ∈ s, v i = xTop

/-- Number of entries equal to the top support value. -/
def topValueCount {ι : Type*} [Fintype ι]
    (xTop : ℝ) (v : ι → ℝ) : ℕ := ((Finset.univ : Finset ι).filter (fun i => v i = xTop)).card

/-- The set of coordinates where a sample satisfies a predicate. -/
def successIndexSet {ι α : Type*} [Fintype ι]
    (p : α → Prop) [DecidablePred p] (sample : ι → α) : Finset ι := (Finset.univ : Finset ι).filter (fun i => p (sample i))

/-- Add one independent draw to a sample indexed by `ι`. -/
abbrev extendDraw {ι α : Type*} (sample : ι → α) (newItem : α) : Option ι → α :=
  AppliedModelingLib.extendDraw sample newItem

/-- Functions on `Option ι` are equivalent to a distinguished new draw and an old sample. -/
abbrev optionFunEquivProd (ι α : Type*) : (Option ι → α) ≃ α × (ι → α) :=
  AppliedModelingLib.optionFunEquivProd ι α

/-- `Option (Fin a)` is a canonical one-point extension of `Fin a`. -/
abbrev optionFinEquivFinSucc (a : ℕ) : Option (Fin a) ≃ Fin (a + 1) :=
  AppliedModelingLib.optionFinEquivFinSucc a

/-- Having `k` top values is the same as the top-value count being at least `k`. -/
theorem hasKTopValues_iff_le_topValueCount {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (k : ℕ) (xTop : ℝ) (v : ι → ℝ) :
    hasKTopValues k xTop v ↔ k ≤ topValueCount xTop v := by
  classical
  simpa [hasKTopValues, AppliedModelingLib.Probability.hasKTopValues,
    topValueCount, AppliedModelingLib.Probability.topValueCount] using
    AppliedModelingLib.Probability.hasKTopValues_iff_le_topValueCount
      (ι := ι) k xTop v

/--
The old sample has exactly `k-1` top-support values and every other value is
at most the second support value.
-/
abbrev hasPredTopValuesWithSecondBound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (xTop xSecond : ℝ) (v : ι → ℝ) : Prop :=
  AppliedModelingLib.Probability.hasPredTopValuesWithSecondBound k xTop xSecond v

/--
When every value is either the top value or at most the second support value,
and the second support value is strictly below the top one, the promoting-event
predicate is exactly the statement that the top-value count is `k-1`.
-/
theorem hasPredTopValuesWithSecondBound_iff_topValueCount_eq {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (k : ℕ) {xTop xSecond : ℝ} (v : ι → ℝ)
    (hsecond_lt_top : xSecond < xTop)
    (hvalue_split : ∀ i, v i = xTop ∨ v i ≤ xSecond) :
    hasPredTopValuesWithSecondBound k xTop xSecond v ↔
      topValueCount xTop v = k - 1 := by
  classical
  simpa [topValueCount, AppliedModelingLib.Probability.topValueCount,
    hasPredTopValuesWithSecondBound] using
    AppliedModelingLib.Probability.hasPredTopValuesWithSecondBound_iff_topValueCount_eq
      (ι := ι) k (v := v) hsecond_lt_top hvalue_split

/-- Add one new value to a finite sample. -/
abbrev extendSample {ι : Type*} (v : ι → ℝ) (newValue : ℝ) : Option ι → ℝ :=
  AppliedModelingLib.Probability.extendSample v newValue

/-- Adding one more value cannot reduce the at-most-`k` top value. -/
theorem topKSumOn_le_extend {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (v : ι → ℝ) (newValue : ℝ) :
    topKSumOn k v ≤ topKSumOn k (extendSample v newValue) := by
  classical
  simpa [topKSumOn, AppliedModelingLib.Probability.topKSumOn,
    topKCandidateSets, AppliedModelingLib.Probability.topKCandidateSets,
    extendSample] using
    AppliedModelingLib.Probability.topKSumOn_le_extend (ι := ι) k v newValue

/--
If the old sample has fewer than `k` coordinates, a maximizing old candidate
set can be augmented by the new coordinate.  Thus the top-`k` value after the
extension is at least the old top-`k` value plus the new value.
-/
theorem topKSumOn_add_newValue_le_extend_of_card_lt {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (k : ℕ) (v : ι → ℝ) (newValue : ℝ)
    (hcard_lt : Fintype.card ι < k) :
    topKSumOn k v + newValue ≤
      topKSumOn k (extendSample v newValue) := by
  classical
  simpa [topKSumOn, AppliedModelingLib.Probability.topKSumOn,
    topKCandidateSets, AppliedModelingLib.Probability.topKCandidateSets,
    extendSample] using
    AppliedModelingLib.Probability.topKSumOn_add_newValue_le_extend_of_card_lt
      (ι := ι) k v newValue hcard_lt

/--
When the old sample has fewer than `k` coordinates, the marginal gain from
adding a new value is at least that value.
-/
theorem newValue_le_topKSumOn_extend_sub_of_card_lt {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (k : ℕ) (v : ι → ℝ) (newValue : ℝ)
    (hcard_lt : Fintype.card ι < k) :
    newValue ≤ topKSumOn k (extendSample v newValue) - topKSumOn k v := by
  simpa [topKSumOn, AppliedModelingLib.Probability.topKSumOn,
    topKCandidateSets, AppliedModelingLib.Probability.topKCandidateSets,
    extendSample] using
    AppliedModelingLib.Probability.newValue_le_topKSumOn_extend_sub_of_card_lt
      (ι := ι) k v newValue hcard_lt

theorem hasKTopValues_extend_of_hasKTopValues {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    {k : ℕ} {xTop : ℝ} {v : ι → ℝ} {newValue : ℝ}
    (h : hasKTopValues k xTop v) :
    hasKTopValues k xTop (extendSample v newValue) := by
  classical
  simpa [hasKTopValues, AppliedModelingLib.Probability.hasKTopValues,
    extendSample] using
    AppliedModelingLib.Probability.hasKTopValues_extend_of_hasKTopValues
      (v := v) (newValue := newValue)
      (by
        simpa [hasKTopValues, AppliedModelingLib.Probability.hasKTopValues] using h)

/--
If a sample already has `k` top-support values, adding one more bounded item
leaves the top-`k` sum unchanged.
-/
theorem topKSumOn_extend_eq_of_hasKTopValues {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (k : ℕ) (v : ι → ℝ) {xTop newValue : ℝ}
    (hxTop_nonneg : 0 ≤ xTop)
    (h_le : ∀ i, v i ≤ xTop) (hnew_le : newValue ≤ xTop)
    (hTop : hasKTopValues k xTop v) :
    topKSumOn k (extendSample v newValue) = topKSumOn k v := by
  classical
  simpa [topKSumOn, AppliedModelingLib.Probability.topKSumOn,
    topKCandidateSets, AppliedModelingLib.Probability.topKCandidateSets,
    extendSample, hasKTopValues, AppliedModelingLib.Probability.hasKTopValues] using
    AppliedModelingLib.Probability.topKSumOn_extend_eq_of_hasKTopValues
      (ι := ι) k v hxTop_nonneg h_le hnew_le
      (by
        simpa [hasKTopValues, AppliedModelingLib.Probability.hasKTopValues] using hTop)

/--
Pointwise upper marginal bound for the finite-discrete top-mass failure event:
outside failure, the marginal is zero; on failure, it is at most `k * xTop`.
-/
theorem topKSumOn_extend_sub_le_top_failure_indicator {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (k : ℕ) (v : ι → ℝ) {xTop newValue : ℝ}
    [Decidable (hasKTopValues k xTop v)]
    (hxTop_nonneg : 0 ≤ xTop)
    (h_le : ∀ i, v i ≤ xTop) (hnew_le : newValue ≤ xTop) :
    topKSumOn k (extendSample v newValue) - topKSumOn k v ≤
      (k : ℝ) * xTop *
        (if hasKTopValues k xTop v then (0 : ℝ) else 1) := by
  classical
  simpa [topKSumOn, AppliedModelingLib.Probability.topKSumOn,
    topKCandidateSets, AppliedModelingLib.Probability.topKCandidateSets,
    extendSample, hasKTopValues, AppliedModelingLib.Probability.hasKTopValues] using
    AppliedModelingLib.Probability.topKSumOn_extend_sub_le_top_failure_indicator
      (ι := ι) k v hxTop_nonneg h_le hnew_le

/-- Expectation upper bound from a pointwise event-indicator upper bound. -/
theorem pmfExp_le_const_mul_pmfProb_of_forall_le_indicator {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (μ : PMF Ω) (p : Ω → Prop) [DecidablePred p]
    (f : Ω → ℝ) (C : ℝ)
    (hpoint : ∀ ω, f ω ≤ C * (if p ω then (1 : ℝ) else 0)) :
    AppliedModelingLib.pmfExp μ f ≤ C * AppliedModelingLib.pmfProb μ p :=
  AppliedModelingLib.pmfExp_le_const_mul_pmfProb_of_forall_le_indicator
    μ p f C hpoint

/--
Finite-PMF lift of the top-mass failure upper marginal bound, for an old
sample drawn from `sampleLaw` and an independent new item drawn from `itemLaw`.
-/
theorem pmfPairExp_topK_extend_sub_le_top_failure_prob
    {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Ω] [DecidableEq Ω]
    (sampleLaw : PMF (ι → Ω)) (itemLaw : PMF Ω)
    (k : ℕ) (value : Ω → ℝ) {xTop : ℝ}
    (hxTop_nonneg : 0 ≤ xTop)
    (hvalue_le : ∀ ω, value ω ≤ xTop)
    [DecidablePred
      (fun sample : ι → Ω =>
        ¬ hasKTopValues k xTop (fun i => value (sample i)))] :
    AppliedModelingLib.pmfPairExp sampleLaw itemLaw
        (fun sample newItem =>
          topKSumOn k
              (extendSample (fun i => value (sample i)) (value newItem)) -
            topKSumOn k (fun i => value (sample i)))
      ≤
        (k : ℝ) * xTop *
          AppliedModelingLib.pmfProb sampleLaw
            (fun sample =>
              ¬ hasKTopValues k xTop (fun i => value (sample i))) := by
  classical
  unfold AppliedModelingLib.pmfPairExp
  refine pmfExp_le_const_mul_pmfProb_of_forall_le_indicator
    sampleLaw
    (fun sample => ¬ hasKTopValues k xTop (fun i => value (sample i)))
    (fun sample =>
      AppliedModelingLib.pmfExp itemLaw
        (fun newItem =>
          topKSumOn k
              (extendSample (fun i => value (sample i)) (value newItem)) -
            topKSumOn k (fun i => value (sample i))))
    ((k : ℝ) * xTop) ?_
  intro sample
  refine AppliedModelingLib.pmfExp_le_of_forall_le itemLaw _ _ ?_
  intro newItem
  simpa [mul_assoc] using
    topKSumOn_extend_sub_le_top_failure_indicator
      (ι := ι) k (fun i => value (sample i))
      hxTop_nonneg (fun i => hvalue_le (sample i))
      (hvalue_le newItem)

/--
For an independent finite product PMF, the probability of a coordinate-wise
event with coordinate-dependent predicates factors into the product of the
one-coordinate probabilities.
-/
theorem pmfProduct_prob_forall_dependent
    {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α]
    (μ : PMF α) (P : ι → α → Prop)
    [∀ i, DecidablePred (P i)] :
    AppliedModelingLib.pmfProb (AppliedModelingLib.pmfProduct ι α μ)
        (fun f : ι → α => ∀ i : ι, P i (f i)) =
      ∏ i : ι, AppliedModelingLib.pmfProb μ (P i) := by
  classical
  exact AppliedModelingLib.pmfProduct_prob_forall_dependent μ P

/-- Product of a two-valued coordinate weight over a finite type. -/
theorem prod_ite_mem_eq_pow_mul_pow {ι : Type*}
    [Fintype ι] [DecidableEq ι] (s : Finset ι) (q rho : ℝ) :
    (∏ i : ι, if i ∈ s then q else rho) =
      q ^ s.card * rho ^ (Fintype.card ι - s.card) := by
  classical
  exact AppliedModelingLib.FiniteSum.prod_ite_mem_eq_pow_mul_pow s q rho

/-- The success-index set equals `s` iff each coordinate has the prescribed status. -/
theorem successIndexSet_eq_iff {ι α : Type*}
    [Fintype ι] [DecidableEq ι]
    {p : α → Prop} [DecidablePred p]
    (sample : ι → α) (s : Finset ι) :
    successIndexSet p sample = s ↔
      ∀ i : ι, p (sample i) ↔ i ∈ s := by
  classical
  simpa [successIndexSet, AppliedModelingLib.successIndexSet] using
    AppliedModelingLib.successIndexSet_eq_iff (sample := sample) (s := s)

/--
For an independent finite product PMF, the probability of a fixed success-index
set is `q^|s| rho^(n-|s|)`, where `q` and `rho` are the one-draw success and
failure probabilities.
-/
theorem pmfProduct_prob_successIndexSet_eq
    {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p] (s : Finset ι) :
    AppliedModelingLib.pmfProb (AppliedModelingLib.pmfProduct ι α μ)
        (fun sample : ι → α => successIndexSet p sample = s) =
      (AppliedModelingLib.pmfProb μ p) ^ s.card *
        (AppliedModelingLib.pmfProb μ (fun a => ¬ p a)) ^
          (Fintype.card ι - s.card) := by
  classical
  simpa [successIndexSet, AppliedModelingLib.successIndexSet] using
    AppliedModelingLib.pmfProduct_prob_successIndexSet_eq (ι := ι) μ p s

/--
The number of successes in an independent finite product has the usual binomial
mass formula, stated directly for finite PMFs and real-valued finite
probabilities.
-/
theorem pmfProduct_prob_successIndexSet_card_eq
    {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p] (j : ℕ) :
    AppliedModelingLib.pmfProb (AppliedModelingLib.pmfProduct ι α μ)
        (fun sample : ι → α => (successIndexSet p sample).card = j) =
      (Nat.choose (Fintype.card ι) j : ℝ) *
        (AppliedModelingLib.pmfProb μ p) ^ j *
          (AppliedModelingLib.pmfProb μ (fun a : α => ¬ p a)) ^
            (Fintype.card ι - j) := by
  classical
  simpa [successIndexSet, AppliedModelingLib.successIndexSet] using
    AppliedModelingLib.pmfProduct_prob_successIndexSet_card_eq (ι := ι) μ p j

/--
The lower-tail probability for the number of successes in an independent
finite product is the corresponding finite binomial sum over `j < k`.
-/
theorem pmfProduct_prob_successIndexSet_card_lt_eq_sum
    {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p] (k : ℕ) :
    AppliedModelingLib.pmfProb (AppliedModelingLib.pmfProduct ι α μ)
        (fun sample : ι → α => (successIndexSet p sample).card < k) =
      ∑ j ∈ Finset.range k,
        (Nat.choose (Fintype.card ι) j : ℝ) *
          (AppliedModelingLib.pmfProb μ p) ^ j *
            (AppliedModelingLib.pmfProb μ (fun a : α => ¬ p a)) ^
              (Fintype.card ι - j) := by
  classical
  simpa [successIndexSet, AppliedModelingLib.successIndexSet] using
    AppliedModelingLib.pmfProduct_prob_successIndexSet_card_lt_eq_sum (ι := ι) μ p k

/--
For independent finite PMFs, the pair expectation of an event indicator
`p a ∧ q b` factors as the product of the two event probabilities.
-/
theorem pmfPairExp_indicator_and_eq_mul_pmfProb
    {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (μ : PMF α) (ν : PMF β)
    (p : α → Prop) (q : β → Prop)
    [DecidablePred p] [DecidablePred q] :
    AppliedModelingLib.pmfPairExp μ ν
        (fun a b => if p a ∧ q b then (1 : ℝ) else 0) =
      AppliedModelingLib.pmfProb μ p * AppliedModelingLib.pmfProb ν q := AppliedModelingLib.pmfPairExp_indicator_and_eq_mul_pmfProb μ ν p q

/-- Subtractive linearity for finite pair expectations. -/
theorem pmfPairExp_sub
    {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (μ : PMF α) (ν : PMF β)
    (f g : α → β → ℝ) :
    AppliedModelingLib.pmfPairExp μ ν (fun a b => f a b - g a b) =
      AppliedModelingLib.pmfPairExp μ ν f - AppliedModelingLib.pmfPairExp μ ν g := by
  unfold AppliedModelingLib.pmfPairExp
  calc
    AppliedModelingLib.pmfExp μ
        (fun a => AppliedModelingLib.pmfExp ν (fun b => f a b - g a b))
        =
        AppliedModelingLib.pmfExp μ
          (fun a => AppliedModelingLib.pmfExp ν (f a) - AppliedModelingLib.pmfExp ν (g a)) := by
          refine AppliedModelingLib.pmfExp_congr μ ?_
          intro a
          exact AppliedModelingLib.pmfExp_sub ν (f a) (g a)
    _ =
        AppliedModelingLib.pmfExp μ (fun a => AppliedModelingLib.pmfExp ν (f a)) -
          AppliedModelingLib.pmfExp μ (fun a => AppliedModelingLib.pmfExp ν (g a)) :=
          AppliedModelingLib.pmfExp_sub μ
            (fun a => AppliedModelingLib.pmfExp ν (f a))
            (fun a => AppliedModelingLib.pmfExp ν (g a))

/--
An iid product sample on `Option ι` has the same finite expectation as first
drawing an iid old sample on `ι` and then drawing one independent new item.
-/
theorem pmfExp_pmfProduct_option_eq_pairExp
    {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α]
    (μ : PMF α) (F : (Option ι → α) → ℝ) :
    AppliedModelingLib.pmfExp (AppliedModelingLib.pmfProduct (Option ι) α μ) F =
      AppliedModelingLib.pmfPairExp (AppliedModelingLib.pmfProduct ι α μ) μ
        (fun sample newItem => F (extendDraw sample newItem)) := by
  classical
  simpa [extendDraw] using
    AppliedModelingLib.pmfExp_pmfProduct_option_eq_pairExp (ι := ι) μ F

/-- Expected top-`k` value for an iid finite sample indexed by `ι`. -/
def iidTopKExpectedOn (ι Ω : Type*) [Fintype ι] [DecidableEq ι]
    [Fintype Ω] [DecidableEq Ω]
    (itemLaw : PMF Ω) (k : ℕ) (value : Ω → ℝ) : ℝ :=
  AppliedModelingLib.pmfExp (AppliedModelingLib.pmfProduct ι Ω itemLaw)
    (fun sample : ι → Ω => topKSumOn k (fun i => value (sample i)))

/-- Expected top-`k` value for an iid finite sample of natural size `a`. -/
def finiteDiscreteIidTopKExpected (Ω : Type*) [Fintype Ω] [DecidableEq Ω]
    (itemLaw : PMF Ω) (k : ℕ) (value : Ω → ℝ) (a : ℕ) : ℝ := iidTopKExpectedOn (Fin a) Ω itemLaw k value

/--
Pair-expectation form of the one-draw iid marginal equals the difference
between the option-extended iid expectation and the old iid expectation.
-/
theorem pmfPairExp_topK_extend_sub_eq_iidTopKExpectedOn_option_sub
    {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Ω] [DecidableEq Ω]
    (itemLaw : PMF Ω) (k : ℕ) (value : Ω → ℝ) :
    AppliedModelingLib.pmfPairExp (AppliedModelingLib.pmfProduct ι Ω itemLaw) itemLaw
        (fun sample newItem =>
          topKSumOn k
              (extendSample (fun i => value (sample i)) (value newItem)) -
            topKSumOn k (fun i => value (sample i))) =
      iidTopKExpectedOn (Option ι) Ω itemLaw k value -
        iidTopKExpectedOn ι Ω itemLaw k value := by
  classical
  simpa [iidTopKExpectedOn, AppliedModelingLib.Probability.iidTopKExpectedOn,
    topKSumOn, AppliedModelingLib.Probability.topKSumOn,
    topKCandidateSets, AppliedModelingLib.Probability.topKCandidateSets,
    extendSample, AppliedModelingLib.Probability.extendSample] using
    AppliedModelingLib.Probability.pmfPairExp_topK_extend_sub_eq_iidTopKExpectedOn_option_sub
      (ι := ι) itemLaw k value

/-- Reindexing an iid finite sample does not change the expected top-`k` value. -/
theorem iidTopKExpectedOn_equiv {ι κ Ω : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Fintype Ω] [DecidableEq Ω]
    (e : ι ≃ κ) (itemLaw : PMF Ω) (k : ℕ) (value : Ω → ℝ) :
    iidTopKExpectedOn ι Ω itemLaw k value =
      iidTopKExpectedOn κ Ω itemLaw k value := by
  classical
  simpa [iidTopKExpectedOn, AppliedModelingLib.Probability.iidTopKExpectedOn,
    topKSumOn, AppliedModelingLib.Probability.topKSumOn,
    topKCandidateSets, AppliedModelingLib.Probability.topKCandidateSets] using
    AppliedModelingLib.Probability.iidTopKExpectedOn_equiv
      (e := e) itemLaw k value

/-- The option-step expectation for `Fin a` is the natural-size expectation at `a+1`. -/
theorem iidTopKExpectedOn_option_fin_eq_succ
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (itemLaw : PMF Ω) (k a : ℕ) (value : Ω → ℝ) :
    iidTopKExpectedOn (Option (Fin a)) Ω itemLaw k value =
      finiteDiscreteIidTopKExpected Ω itemLaw k value (a + 1) := by
  simpa [finiteDiscreteIidTopKExpected, AppliedModelingLib.Probability.finiteIidTopKExpected,
    iidTopKExpectedOn, AppliedModelingLib.Probability.iidTopKExpectedOn,
    topKSumOn, AppliedModelingLib.Probability.topKSumOn,
    topKCandidateSets, AppliedModelingLib.Probability.topKCandidateSets] using
    AppliedModelingLib.Probability.iidTopKExpectedOn_option_fin_eq_succ
      (itemLaw := itemLaw) (k := k) (a := a) (value := value)

/-- Arithmetic bound behind the `k-1`-top promoting event. -/
theorem top_second_count_bound
    {k b c : ℕ} {xTop xSecond : ℝ}
    (hk_pos : 0 < k)
    (hb : b ≤ k - 1) (hbc : b + c ≤ k)
    (hxSecond_nonneg : 0 ≤ xSecond)
    (hsecond_le_top : xSecond ≤ xTop) :
    (b : ℝ) * xTop + (c : ℝ) * xSecond ≤
      ((k - 1 : ℕ) : ℝ) * xTop + xSecond := by
  exact AppliedModelingLib.Probability.top_second_count_bound
    hk_pos hb hbc hxSecond_nonneg hsecond_le_top

/--
If a candidate set contains at most `k` indices, while the whole sample has
exactly `k-1` top-support values and every other value is at most `xSecond`,
then that candidate's sum is at most `(k-1) * xTop + xSecond`.
-/
theorem finset_sum_le_pred_top_add_second {ι : Type*}
    [DecidableEq ι]
    {k : ℕ} {v : ι → ℝ} {xTop xSecond : ℝ}
    (hk_pos : 0 < k)
    (hxSecond_nonneg : 0 ≤ xSecond)
    (hsecond_le_top : xSecond ≤ xTop)
    (topSet s : Finset ι)
    (htop_card : topSet.card = k - 1)
    (hs_card : s.card ≤ k)
    (htop_value : ∀ i ∈ topSet, v i = xTop)
    (hnontop_le : ∀ i, i ∉ topSet → v i ≤ xSecond) :
    (∑ i ∈ s, v i) ≤ ((k - 1 : ℕ) : ℝ) * xTop + xSecond := by
  classical
  exact AppliedModelingLib.Probability.finset_sum_le_pred_top_add_second
    hk_pos hxSecond_nonneg hsecond_le_top topSet s htop_card hs_card
    htop_value hnontop_le

/--
Under the exact `k-1` top-count event, the old top-`k` value is at most
`(k-1) * xTop + xSecond`.
-/
theorem topKSumOn_le_pred_top_add_second {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (k : ℕ) (v : ι → ℝ) {xTop xSecond : ℝ}
    (hk_pos : 0 < k)
    (hxSecond_nonneg : 0 ≤ xSecond)
    (hsecond_le_top : xSecond ≤ xTop)
    (topSet : Finset ι)
    (htop_card : topSet.card = k - 1)
    (htop_value : ∀ i ∈ topSet, v i = xTop)
    (hnontop_le : ∀ i, i ∉ topSet → v i ≤ xSecond) :
    topKSumOn k v ≤ ((k - 1 : ℕ) : ℝ) * xTop + xSecond := by
  classical
  simpa [topKSumOn, AppliedModelingLib.Probability.topKSumOn,
    topKCandidateSets, AppliedModelingLib.Probability.topKCandidateSets] using
    AppliedModelingLib.Probability.topKSumOn_le_pred_top_add_second
      (ι := ι) k v hk_pos hxSecond_nonneg hsecond_le_top
      topSet htop_card htop_value hnontop_le

/--
Deterministic promoting-event lower bound.  If the old sample has exactly
`k-1` top-support values, all other old values are at most `xSecond`, and the
new draw is top-support, then the top-`k` sum increases by at least the gap
`xTop - xSecond`.
-/
theorem topKSumOn_extend_sub_ge_top_gap_of_pred_top_witness {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (k : ℕ) (v : ι → ℝ) {xTop xSecond newValue : ℝ}
    (hk_pos : 0 < k)
    (hxTop_nonneg : 0 ≤ xTop)
    (hxSecond_nonneg : 0 ≤ xSecond)
    (hsecond_le_top : xSecond ≤ xTop)
    (topSet : Finset ι)
    (htop_card : topSet.card = k - 1)
    (htop_value : ∀ i ∈ topSet, v i = xTop)
    (hnontop_le : ∀ i, i ∉ topSet → v i ≤ xSecond)
    (hnew_eq : newValue = xTop) :
    xTop - xSecond ≤
      topKSumOn k (extendSample v newValue) - topKSumOn k v := by
  classical
  simpa [topKSumOn, AppliedModelingLib.Probability.topKSumOn,
    topKCandidateSets, AppliedModelingLib.Probability.topKCandidateSets,
    extendSample] using
    AppliedModelingLib.Probability.topKSumOn_extend_sub_ge_top_gap_of_pred_top_witness
      (ι := ι) k v hk_pos hxTop_nonneg hxSecond_nonneg hsecond_le_top
      topSet htop_card htop_value hnontop_le hnew_eq

/--
Pointwise lower marginal bound for the finite-discrete promoting event.
Outside the event the bound is zero; on the event the increase is at least the
top gap `xTop - xSecond`.
-/
theorem topKSumOn_extend_sub_ge_top_gap_promoting_indicator {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (k : ℕ) (v : ι → ℝ) {xTop xSecond newValue : ℝ}
    [Decidable
      (hasPredTopValuesWithSecondBound k xTop xSecond v ∧
        newValue = xTop)]
    (hk_pos : 0 < k)
    (hxTop_nonneg : 0 ≤ xTop)
    (hxSecond_nonneg : 0 ≤ xSecond)
    (hsecond_le_top : xSecond ≤ xTop) :
    (xTop - xSecond) *
        (if hasPredTopValuesWithSecondBound k xTop xSecond v ∧
            newValue = xTop then (1 : ℝ) else 0) ≤
      topKSumOn k (extendSample v newValue) - topKSumOn k v := by
  classical
  simpa [topKSumOn, AppliedModelingLib.Probability.topKSumOn,
    topKCandidateSets, AppliedModelingLib.Probability.topKCandidateSets,
    extendSample, hasPredTopValuesWithSecondBound] using
    AppliedModelingLib.Probability.topKSumOn_extend_sub_ge_top_gap_promoting_indicator
      (ι := ι) k v hk_pos hxTop_nonneg hxSecond_nonneg hsecond_le_top

/--
Finite-PMF lift of the promoting-event lower marginal bound, using the pair
expectation of the event indicator as the event probability.
-/
theorem top_gap_mul_pmfPairExp_promoting_indicator_le_topK_extend_sub
    {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Ω] [DecidableEq Ω]
    (sampleLaw : PMF (ι → Ω)) (itemLaw : PMF Ω)
    (k : ℕ) (value : Ω → ℝ) {xTop xSecond : ℝ}
    (hk_pos : 0 < k)
    (hxTop_nonneg : 0 ≤ xTop)
    (hxSecond_nonneg : 0 ≤ xSecond)
    (hsecond_le_top : xSecond ≤ xTop)
    [∀ sample : ι → Ω,
      DecidablePred
        (fun newItem : Ω =>
          hasPredTopValuesWithSecondBound k xTop xSecond
              (fun i => value (sample i)) ∧
            value newItem = xTop)] :
    (xTop - xSecond) *
        AppliedModelingLib.pmfPairExp sampleLaw itemLaw
          (fun sample newItem =>
            if hasPredTopValuesWithSecondBound k xTop xSecond
                (fun i => value (sample i)) ∧
              value newItem = xTop then (1 : ℝ) else 0)
      ≤
        AppliedModelingLib.pmfPairExp sampleLaw itemLaw
          (fun sample newItem =>
            topKSumOn k
                (extendSample (fun i => value (sample i)) (value newItem)) -
              topKSumOn k (fun i => value (sample i))) := by
  classical
  unfold AppliedModelingLib.pmfPairExp
  rw [← AppliedModelingLib.pmfExp_const_mul]
  refine AppliedModelingLib.pmfExp_le_pmfExp_of_forall_le sampleLaw _ _ ?_
  intro sample
  rw [← AppliedModelingLib.pmfExp_const_mul]
  refine AppliedModelingLib.pmfExp_le_pmfExp_of_forall_le itemLaw _ _ ?_
  intro newItem
  exact topKSumOn_extend_sub_ge_top_gap_promoting_indicator
    (ι := ι) k (fun i => value (sample i))
    hk_pos hxTop_nonneg hxSecond_nonneg hsecond_le_top

/--
Small-sample lower marginal bound.  If the old sample has fewer than `k`
coordinates, then whenever the new item is top-support the top-`k` value grows
by at least `xTop`; averaging gives `xTop` times the top-support probability.
-/
theorem top_value_mul_pmfProb_le_pmfPairExp_topK_extend_sub_of_card_lt
    {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Ω] [DecidableEq Ω]
    (sampleLaw : PMF (ι → Ω)) (itemLaw : PMF Ω)
    (k : ℕ) (value : Ω → ℝ) {xTop : ℝ}
    (hcard_lt : Fintype.card ι < k)
    (hxTop_nonneg : 0 ≤ xTop) :
    xTop * AppliedModelingLib.pmfProb itemLaw (fun ω => value ω = xTop) ≤
      AppliedModelingLib.pmfPairExp sampleLaw itemLaw
        (fun sample newItem =>
          topKSumOn k
              (extendSample (fun i => value (sample i)) (value newItem)) -
            topKSumOn k (fun i => value (sample i))) := by
  classical
  unfold AppliedModelingLib.pmfPairExp
  have hinner :
      ∀ sample : ι → Ω,
        xTop * AppliedModelingLib.pmfProb itemLaw (fun ω => value ω = xTop) ≤
          AppliedModelingLib.pmfExp itemLaw
            (fun newItem =>
              topKSumOn k
                  (extendSample (fun i => value (sample i))
                    (value newItem)) -
                topKSumOn k (fun i => value (sample i))) := by
    intro sample
    have hpoint :
        ∀ newItem : Ω,
          xTop * (if value newItem = xTop then (1 : ℝ) else 0) ≤
            topKSumOn k
                (extendSample (fun i => value (sample i))
                  (value newItem)) -
              topKSumOn k (fun i => value (sample i)) := by
      intro newItem
      by_cases htop : value newItem = xTop
      · have hlower :
            value newItem ≤
              topKSumOn k
                  (extendSample (fun i => value (sample i))
                    (value newItem)) -
                topKSumOn k (fun i => value (sample i)) :=
          newValue_le_topKSumOn_extend_sub_of_card_lt
            (ι := ι) k (fun i => value (sample i)) (value newItem)
            hcard_lt
        simpa [htop] using hlower
      · have hmono :=
          topKSumOn_le_extend k (fun i => value (sample i))
            (value newItem)
        have hdiff_nonneg :
            0 ≤
              topKSumOn k
                  (extendSample (fun i => value (sample i))
                    (value newItem)) -
                topKSumOn k (fun i => value (sample i)) := by
          linarith
        simpa [htop, hxTop_nonneg] using hdiff_nonneg
    have hexp :=
      AppliedModelingLib.pmfExp_le_pmfExp_of_forall_le itemLaw
        (fun newItem =>
          xTop * (if value newItem = xTop then (1 : ℝ) else 0))
        (fun newItem =>
            topKSumOn k
              (extendSample (fun i => value (sample i))
                (value newItem)) -
            topKSumOn k (fun i => value (sample i)))
        hpoint
    rw [AppliedModelingLib.pmfExp_const_mul] at hexp
    simpa [AppliedModelingLib.pmfProb] using hexp
  have houter :=
    AppliedModelingLib.pmfExp_le_pmfExp_of_forall_le sampleLaw
      (fun _sample : ι → Ω =>
        xTop * AppliedModelingLib.pmfProb itemLaw (fun ω => value ω = xTop))
      (fun sample =>
        AppliedModelingLib.pmfExp itemLaw
          (fun newItem =>
            topKSumOn k
                (extendSample (fun i => value (sample i))
                  (value newItem)) -
              topKSumOn k (fun i => value (sample i))))
      hinner
  simpa using houter

end

end PRPKG24AccuracyDiversity
