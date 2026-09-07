import AppliedModelingLib.Foundations.Probability.FiniteExpectation
import AppliedModelingLib.Foundations.Probability.UniformFinsetExpectation
import AppliedModelingLib.Foundations.Math.FiniteAverage
import AppliedModelingLib.Foundations.Math.FiniteSum
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic

/-!
# Finite sample variance normalizations

Finite empirical laws naturally use the denominator `n`, whereas classical
empirical-Bernstein inequalities are often stated with the unbiased
denominator `n - 1`.  This file records the exact finite conversion without
conflating the two estimators.
-/

namespace AppliedModelingLib

open scoped BigOperators

/-- The arithmetic mean of a finite real sample. This is the scalar sample-value
specialization of the domain-neutral `finiteAverage`. -/
noncomputable def finiteRealSampleMean {n : ℕ} (sample : Fin n → ℝ) : ℝ :=
  finiteAverage sample

@[simp] theorem finiteRealSampleMean_eq_div {n : ℕ} (sample : Fin n → ℝ) :
    finiteRealSampleMean sample = (∑ index, sample index) / (n : ℝ) := by
  simpa [finiteRealSampleMean] using finiteAverage_real_eq_div_card sample

/-- The finite-indexed sum underlying a list sample is its ordinary ordered
list sum.  This is useful when a finite sample is represented by a filtered
event trace rather than by an a priori fixed index type. -/
theorem finiteSample_sum_list_get_eq_list_sum
    {α : Type*} (observations : List α) (statistic : α → ℝ) :
    (∑ index : Fin observations.length, statistic (observations.get index)) =
      (observations.map statistic).sum := by
  induction observations with
  | nil => simp
  | cons observation observations ih =>
      change
        (∑ index : Fin (observations.length + 1),
          statistic ((observation :: observations).get index)) =
          (statistic observation :: observations.map statistic).sum
      rw [Fin.sum_univ_succ]
      simp only [List.get_cons_zero, List.sum_cons]
      exact congrArg (statistic observation + ·) ih

/-- The variance of the uniform empirical law, normalized by `n`. -/
noncomputable def finiteSampleEmpiricalVariance {n : ℕ} (sample : Fin n → ℝ) : ℝ :=
  (∑ index, (sample index - finiteRealSampleMean sample) ^ 2) / (n : ℝ)

/-- The unbiased finite sample variance, normalized by `n - 1` whenever
`n ≥ 2`.  The definition remains total outside that source regime, while
all comparison theorems state their required positive-count premise. -/
noncomputable def finiteSampleUnbiasedVariance {n : ℕ} (sample : Fin n → ℝ) : ℝ :=
  (∑ index, (sample index - finiteRealSampleMean sample) ^ 2) / ((n : ℝ) - 1)

/-- The ordered-pair numerator in Maurer--Pontil's finite sample variance.
Only the orientation `i < j` is included, so every unordered pair occurs once. -/
noncomputable def finiteSampleOrderedPairSqSum {n : ℕ} (sample : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n,
    if i < j then (sample i - sample j) ^ 2 else 0

/-- Maurer--Pontil's pairwise sample-variance normalization. -/
noncomputable def finiteSamplePairwiseVariance {n : ℕ} (sample : Fin n → ℝ) : ℝ :=
  finiteSampleOrderedPairSqSum sample / ((n : ℝ) * ((n : ℝ) - 1))

/-- Complementing a nonempty unit-interval sample complements its arithmetic mean. -/
theorem finiteSampleMean_one_sub {n : ℕ} (sample : Fin n → ℝ) (hn : 0 < n) :
    finiteRealSampleMean (fun index => 1 - sample index) = 1 - finiteRealSampleMean sample := by
  simp only [finiteRealSampleMean_eq_div]
  rw [Finset.sum_sub_distrib]
  simp [Fintype.card_fin]
  have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  field_simp [hn_ne]

/-- Complementing every sample value preserves the unbiased sample variance. -/
theorem finiteSampleUnbiasedVariance_one_sub {n : ℕ} (sample : Fin n → ℝ) (hn : 0 < n) :
    finiteSampleUnbiasedVariance (fun index => 1 - sample index) =
      finiteSampleUnbiasedVariance sample := by
  unfold finiteSampleUnbiasedVariance
  rw [finiteSampleMean_one_sub sample hn]
  congr 1
  apply Finset.sum_congr rfl
  intro index _
  ring

/-- Complementing every sample value preserves the empirical-law variance. -/
theorem finiteSampleEmpiricalVariance_one_sub {n : ℕ} (sample : Fin n → ℝ) (hn : 0 < n) :
    finiteSampleEmpiricalVariance (fun index => 1 - sample index) =
      finiteSampleEmpiricalVariance sample := by
  unfold finiteSampleEmpiricalVariance
  rw [finiteSampleMean_one_sub sample hn]
  congr 1
  apply Finset.sum_congr rfl
  intro index _
  ring

/-- The expectation of a complemented statistic is the complement of its
expectation. -/
theorem pmfExp_one_sub
    {α : Type*} [Fintype α] [DecidableEq α]
    (law : PMF α) (statistic : α → ℝ) :
    pmfExp law (fun outcome => 1 - statistic outcome) = 1 - pmfExp law statistic := by
  rw [pmfExp_sub, pmfExp_const]

/-- The variance of a statistic is invariant under complementation. -/
theorem pmfVariance_one_sub
    {α : Type*} [Fintype α] [DecidableEq α]
    (law : PMF α) (statistic : α → ℝ) :
    pmfVariance law (fun outcome => 1 - statistic outcome) = pmfVariance law statistic := by
  unfold pmfVariance
  rw [pmfExp_sub, pmfExp_const]
  apply pmfExp_congr
  intro outcome
  ring

/-- Reindexing a finite sample by a bijection preserves its arithmetic mean. -/
theorem finiteSampleMean_comp_equiv {n : ℕ}
    (sample : Fin n → ℝ) (equiv : Fin n ≃ Fin n) :
    finiteRealSampleMean (sample ∘ equiv) = finiteRealSampleMean sample := by
  simp only [finiteRealSampleMean_eq_div]
  congr 1
  exact Fintype.sum_equiv equiv
    (fun index => sample (equiv index)) sample (fun _ => rfl)

/-- Reindexing a finite sample through an equivalence between propositionally
different `Fin` cardinalities preserves its arithmetic mean. -/
theorem finiteSampleMean_comp_equiv_of_equiv {m n : ℕ}
    (sample : Fin n → ℝ) (equiv : Fin m ≃ Fin n) :
    finiteRealSampleMean (sample ∘ equiv) = finiteRealSampleMean sample := by
  have hcard : m = n := by
    simpa using Fintype.card_congr equiv
  subst m
  exact finiteSampleMean_comp_equiv sample equiv

/-- The `n`-normalized variance depends only on the finite multiset of sample
values, not on their enumeration. -/
theorem finiteSampleEmpiricalVariance_comp_equiv {n : ℕ}
    (sample : Fin n → ℝ) (equiv : Fin n ≃ Fin n) :
    finiteSampleEmpiricalVariance (sample ∘ equiv) =
      finiteSampleEmpiricalVariance sample := by
  unfold finiteSampleEmpiricalVariance
  rw [finiteSampleMean_comp_equiv]
  congr 1
  exact Fintype.sum_equiv equiv
    (fun index => (sample (equiv index) - finiteRealSampleMean sample) ^ 2)
    (fun index => (sample index - finiteRealSampleMean sample) ^ 2) (fun _ => rfl)

/-- The Maurer--Pontil unbiased finite variance is invariant under a bijective
reindexing of the observations. -/
theorem finiteSampleUnbiasedVariance_comp_equiv {n : ℕ}
    (sample : Fin n → ℝ) (equiv : Fin n ≃ Fin n) :
    finiteSampleUnbiasedVariance (sample ∘ equiv) =
      finiteSampleUnbiasedVariance sample := by
  unfold finiteSampleUnbiasedVariance
  rw [finiteSampleMean_comp_equiv]
  congr 1
  exact Fintype.sum_equiv equiv
    (fun index => (sample (equiv index) - finiteRealSampleMean sample) ^ 2)
    (fun index => (sample index - finiteRealSampleMean sample) ^ 2) (fun _ => rfl)

/-- The unbiased finite sample variance is invariant under an equivalence
between finite index types of equal cardinality. -/
theorem finiteSampleUnbiasedVariance_comp_equiv_of_equiv {m n : ℕ}
    (sample : Fin n → ℝ) (equiv : Fin m ≃ Fin n) :
    finiteSampleUnbiasedVariance (sample ∘ equiv) =
      finiteSampleUnbiasedVariance sample := by
  have hcard : m = n := by
    simpa using Fintype.card_congr equiv
  subst m
  exact finiteSampleUnbiasedVariance_comp_equiv sample equiv

/-- Scaling every observation scales its finite sample mean by the same
factor. -/
theorem finiteSampleMean_mul_left {n : ℕ} (scale : ℝ) (sample : Fin n → ℝ) :
    finiteRealSampleMean (fun index => scale * sample index) =
      scale * finiteRealSampleMean sample := by
  simp only [finiteRealSampleMean_eq_div]
  rw [← Finset.mul_sum]
  ring

/-- The empirical-law variance is homogeneous of degree two. -/
theorem finiteSampleEmpiricalVariance_mul_left {n : ℕ}
    (scale : ℝ) (sample : Fin n → ℝ) :
    finiteSampleEmpiricalVariance (fun index => scale * sample index) =
      scale ^ 2 * finiteSampleEmpiricalVariance sample := by
  unfold finiteSampleEmpiricalVariance
  rw [finiteSampleMean_mul_left]
  have hsum :
      (∑ index : Fin n,
        (scale * sample index - scale * finiteRealSampleMean sample) ^ 2) =
        scale ^ 2 * ∑ index : Fin n,
          (sample index - finiteRealSampleMean sample) ^ 2 := by
    calc
      (∑ index : Fin n,
        (scale * sample index - scale * finiteRealSampleMean sample) ^ 2) =
          ∑ index : Fin n,
            scale ^ 2 * (sample index - finiteRealSampleMean sample) ^ 2 := by
              apply Finset.sum_congr rfl
              intro index _
              ring
      _ = scale ^ 2 * ∑ index : Fin n,
            (sample index - finiteRealSampleMean sample) ^ 2 := by
              rw [Finset.mul_sum]
  rw [hsum]
  ring

/-- The pairwise Maurer--Pontil variance is homogeneous of degree two. -/
theorem finiteSamplePairwiseVariance_mul_left {n : ℕ}
    (scale : ℝ) (sample : Fin n → ℝ) :
    finiteSamplePairwiseVariance (fun index => scale * sample index) =
      scale ^ 2 * finiteSamplePairwiseVariance sample := by
  unfold finiteSamplePairwiseVariance finiteSampleOrderedPairSqSum
  change
    (∑ first : Fin n, ∑ second : Fin n,
      if first < second then (scale * sample first - scale * sample second) ^ 2 else 0) /
        ((n : ℝ) * ((n : ℝ) - 1)) =
      scale ^ 2 *
        ((∑ first : Fin n, ∑ second : Fin n,
          if first < second then (sample first - sample second) ^ 2 else 0) /
          ((n : ℝ) * ((n : ℝ) - 1)))
  have hsum :
      (∑ first : Fin n, ∑ second : Fin n,
        if first < second then (scale * sample first - scale * sample second) ^ 2 else 0) =
        scale ^ 2 * ∑ first : Fin n, ∑ second : Fin n,
          if first < second then (sample first - sample second) ^ 2 else 0 := by
    calc
      (∑ first : Fin n, ∑ second : Fin n,
        if first < second then (scale * sample first - scale * sample second) ^ 2 else 0) =
          ∑ first : Fin n, ∑ second : Fin n,
            scale ^ 2 *
              (if first < second then (sample first - sample second) ^ 2 else 0) := by
                apply Finset.sum_congr rfl
                intro first _
                apply Finset.sum_congr rfl
                intro second _
                by_cases horder : first < second
                · simp [horder]
                  ring
                · simp [horder]
      _ = ∑ first : Fin n,
            scale ^ 2 * (∑ second : Fin n,
              if first < second then (sample first - sample second) ^ 2 else 0) := by
                apply Finset.sum_congr rfl
                intro first _
                rw [Finset.mul_sum]
      _ = scale ^ 2 * ∑ first : Fin n, ∑ second : Fin n,
            if first < second then (sample first - sample second) ^ 2 else 0 := by
                rw [Finset.mul_sum]
  rw [hsum]
  ring

/-- The unbiased finite sample variance is homogeneous of degree two. -/
theorem finiteSampleUnbiasedVariance_mul_left {n : ℕ}
    (scale : ℝ) (sample : Fin n → ℝ) :
    finiteSampleUnbiasedVariance (fun index => scale * sample index) =
      scale ^ 2 * finiteSampleUnbiasedVariance sample := by
  unfold finiteSampleUnbiasedVariance
  rw [finiteSampleMean_mul_left]
  have hsum :
      (∑ index : Fin n,
        (scale * sample index - scale * finiteRealSampleMean sample) ^ 2) =
        scale ^ 2 * ∑ index : Fin n,
          (sample index - finiteRealSampleMean sample) ^ 2 := by
    calc
      (∑ index : Fin n,
        (scale * sample index - scale * finiteRealSampleMean sample) ^ 2) =
          ∑ index : Fin n,
            scale ^ 2 * (sample index - finiteRealSampleMean sample) ^ 2 := by
              apply Finset.sum_congr rfl
              intro index _
              ring
      _ = scale ^ 2 * ∑ index : Fin n,
            (sample index - finiteRealSampleMean sample) ^ 2 := by
              rw [Finset.mul_sum]
  rw [hsum]
  ring

/-- Enumerating a finite ordered set through its canonical `Fin` index gives
the same sum as the literal finset sum. -/
theorem finiteSample_sum_orderEmbOfFin_eq_sum_finset
    {α : Type*} [DecidableEq α] [LinearOrder α]
    (s : Finset α) (f : α → ℝ) :
    (∑ index : Fin s.card, f (s.orderEmbOfFin rfl index)) = ∑ value ∈ s, f value := by
  classical
  calc
    (∑ index : Fin s.card, f (s.orderEmbOfFin rfl index)) =
        ∑ index : Fin s.card, f ((s.orderIsoOfFin rfl index).1) := by rfl
    _ = ∑ value : s, f value.1 :=
      Fintype.sum_equiv (s.orderIsoOfFin rfl).toEquiv
        (fun index => f ((s.orderIsoOfFin rfl index).1))
        (fun value => f value.1) (fun _ => rfl)
    _ = ∑ value ∈ s, f value := Finset.sum_attach s f

/-- A choice-free finite enumeration of a finset, requiring no pre-existing
order on its carrier. -/
noncomputable def finiteSampleFinsetEquiv
    {α : Type*} [DecidableEq α] (s : Finset α) :
    Fin s.card ≃ {value // value ∈ s} :=
  (Fin.castOrderIso (by simp)).toEquiv.trans (Fintype.equivFin _).symm

/-- The finite enumeration in `finiteSampleFinsetEquiv` preserves literal
finset sums. -/
theorem finiteSample_sum_finiteSampleFinsetEquiv_eq_sum_finset
    {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℝ) :
    (∑ index : Fin s.card, f ((finiteSampleFinsetEquiv s index).1)) =
      ∑ value ∈ s, f value := by
  calc
    (∑ index : Fin s.card, f ((finiteSampleFinsetEquiv s index).1)) =
        ∑ value : {value // value ∈ s}, f value.1 :=
      Fintype.sum_equiv (finiteSampleFinsetEquiv s)
        (fun index => f ((finiteSampleFinsetEquiv s index).1))
        (fun value => f value.1) (fun _ => rfl)
    _ = ∑ value ∈ s, f value := Finset.sum_attach s f

/-- Finite-PMF variance commutes with a deterministic pushforward. -/
theorem pmfVariance_map
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (μ : PMF α) (map : α → β) (statistic : β → ℝ) :
    pmfVariance (μ.map map) statistic = pmfVariance μ (statistic ∘ map) := by
  unfold pmfVariance
  rw [pmfExp_map]
  have hmean : pmfExp (μ.map map) statistic = pmfExp μ (statistic ∘ map) := by
    exact pmfExp_map μ map statistic
  rw [hmean]
  rfl

/-- The variance of a uniform finite empirical law is the `n`-normalized
finite sample variance of its canonical enumeration. -/
theorem pmfVariance_uniformOfFinset_eq_finiteSampleEmpiricalVariance
    {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (hs : s.Nonempty) (f : α → ℝ) :
    pmfVariance (PMF.uniformOfFinset s hs) f =
      finiteSampleEmpiricalVariance (fun index : Fin s.card =>
        f ((finiteSampleFinsetEquiv s index).1)) := by
  let sample : Fin s.card → ℝ := fun index => f ((finiteSampleFinsetEquiv s index).1)
  have hsum : (∑ index : Fin s.card, sample index) = ∑ value ∈ s, f value := by
    exact finiteSample_sum_finiteSampleFinsetEquiv_eq_sum_finset s f
  have hmean : finiteRealSampleMean sample =
      (∑ value ∈ s, f value) / (s.card : ℝ) := by
    rw [finiteRealSampleMean_eq_div, hsum]
  unfold pmfVariance
  rw [pmfExp_uniformOfFinset_eq_sum_div_card s hs f]
  rw [pmfExp_uniformOfFinset_eq_sum_div_card s hs
    (fun value =>
      (f value - (∑ priorValue ∈ s, f priorValue) / (s.card : ℝ)) ^ 2)]
  change
    (∑ value ∈ s,
      (f value - (∑ value ∈ s, f value) / (s.card : ℝ)) ^ 2) / (s.card : ℝ) =
        finiteSampleEmpiricalVariance sample
  unfold finiteSampleEmpiricalVariance
  rw [hmean]
  apply congrArg (fun total : ℝ => total / (s.card : ℝ))
  symm
  simpa [sample] using
    (finiteSample_sum_finiteSampleFinsetEquiv_eq_sum_finset s
      (fun value => (f value - (∑ priorValue ∈ s, f priorValue) / (s.card : ℝ)) ^ 2))

/-- The full ordered double sum of squared differences is twice `n` times the
sum of squared deviations about the sample mean. -/
theorem finiteSample_doublePairSqSum_eq_two_card_mul_centeredSqSum
    {n : ℕ} (sample : Fin n → ℝ) (hn : 0 < n) :
    (∑ i : Fin n, ∑ j : Fin n, (sample i - sample j) ^ 2) =
      2 * (n : ℝ) * ∑ i : Fin n, (sample i - finiteRealSampleMean sample) ^ 2 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  let S : ℝ := ∑ i : Fin n, sample i
  let Q : ℝ := ∑ i : Fin n, sample i ^ 2
  have hsum_const (x : ℝ) : (∑ _ : Fin n, x) = (n : ℝ) * x := by simp
  have hfirst :
      (∑ i : Fin n, ∑ j : Fin n, sample i ^ 2) = (n : ℝ) * Q := by
    calc
      (∑ i : Fin n, ∑ j : Fin n, sample i ^ 2) =
          ∑ i : Fin n, (n : ℝ) * sample i ^ 2 := by
            apply Finset.sum_congr rfl
            intro i _
            exact hsum_const _
      _ = (n : ℝ) * Q := by
            rw [Finset.mul_sum]
  have hcross :
      (∑ i : Fin n, ∑ j : Fin n, sample i * sample j) = S ^ 2 := by
    calc
      (∑ i : Fin n, ∑ j : Fin n, sample i * sample j) =
          ∑ i : Fin n, sample i * S := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
      _ = S ^ 2 := by
            rw [← Finset.sum_mul]
            simp only [S]
            ring
  have hthird :
      (∑ i : Fin n, ∑ j : Fin n, sample j ^ 2) = (n : ℝ) * Q := by
    calc
      (∑ i : Fin n, ∑ j : Fin n, sample j ^ 2) = ∑ _ : Fin n, Q := by
            apply Finset.sum_congr rfl
            intro _ _
            rfl
      _ = (n : ℝ) * Q := hsum_const _
  have hdouble :
      (∑ i : Fin n, ∑ j : Fin n, (sample i - sample j) ^ 2) =
        2 * (n : ℝ) * Q - 2 * S ^ 2 := by
    calc
      (∑ i : Fin n, ∑ j : Fin n, (sample i - sample j) ^ 2) =
          (∑ i : Fin n, ∑ j : Fin n, sample i ^ 2) -
            2 * (∑ i : Fin n, ∑ j : Fin n, sample i * sample j) +
              (∑ i : Fin n, ∑ j : Fin n, sample j ^ 2) := by
            simp_rw [sub_sq]
            calc
              (∑ i : Fin n, ∑ j : Fin n,
                  (sample i ^ 2 - 2 * sample i * sample j + sample j ^ 2)) =
                  ∑ i : Fin n,
                    ((∑ j : Fin n, sample i ^ 2) -
                      2 * (∑ j : Fin n, sample i * sample j) +
                        (∑ j : Fin n, sample j ^ 2)) := by
                    apply Finset.sum_congr rfl
                    intro i _
                    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
                    have hcrossrow :
                        (∑ j : Fin n, 2 * sample i * sample j) =
                          2 * (∑ j : Fin n, sample i * sample j) := by
                      calc
                        (∑ j : Fin n, 2 * sample i * sample j) =
                            ∑ j : Fin n, 2 * (sample i * sample j) := by
                              apply Finset.sum_congr rfl
                              intro j _
                              ring
                        _ = 2 * (∑ j : Fin n, sample i * sample j) := by
                              rw [Finset.mul_sum]
                    rw [hcrossrow]
              _ = (∑ i : Fin n, ∑ j : Fin n, sample i ^ 2) -
                    2 * (∑ i : Fin n, ∑ j : Fin n, sample i * sample j) +
                      (∑ i : Fin n, ∑ j : Fin n, sample j ^ 2) := by
                    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
                    rw [← Finset.mul_sum]
      _ = 2 * (n : ℝ) * Q - 2 * S ^ 2 := by rw [hfirst, hcross, hthird]; ring
  have hcentered :
      (∑ i : Fin n, (sample i - finiteRealSampleMean sample) ^ 2) =
        Q - S ^ 2 / (n : ℝ) := by
    rw [finiteRealSampleMean_eq_div]
    change (∑ i : Fin n, (sample i - S / (n : ℝ)) ^ 2) = _
    have hlinear (c : ℝ) : (∑ i : Fin n, 2 * sample i * c) = 2 * S * c := by
      calc
        (∑ i : Fin n, 2 * sample i * c) =
            ∑ i : Fin n, 2 * (sample i * c) := by
              apply Finset.sum_congr rfl
              intro i _
              ring
        _ = 2 * (∑ i : Fin n, sample i * c) := by rw [Finset.mul_sum]
        _ = 2 * S * c := by
              rw [← Finset.sum_mul]
              simp only [S]
              ring
    calc
      (∑ i : Fin n, (sample i - S / (n : ℝ)) ^ 2) =
          ∑ i : Fin n,
            (sample i ^ 2 - 2 * sample i * (S / (n : ℝ)) + (S / (n : ℝ)) ^ 2) := by
              apply Finset.sum_congr rfl
              intro i _
              ring
      _ = (∑ i : Fin n, sample i ^ 2) -
            (∑ i : Fin n, 2 * sample i * (S / (n : ℝ))) +
              (∑ _ : Fin n, (S / (n : ℝ)) ^ 2) := by
              rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      _ = Q - 2 * S * (S / (n : ℝ)) + (n : ℝ) * (S / (n : ℝ)) ^ 2 := by
              rw [hlinear, hsum_const]
      _ = Q - S ^ 2 / (n : ℝ) := by
              field_simp [hn0]
              ring
  rw [hdouble, hcentered]
  field_simp [hn0]

/-- The ordered-pair numerator is one half of the full double sum of squared
differences. -/
theorem finiteSampleOrderedPairSqSum_eq_half_doublePairSqSum
    {n : ℕ} (sample : Fin n → ℝ) :
    finiteSampleOrderedPairSqSum sample =
      (1 / 2 : ℝ) * (∑ i : Fin n, ∑ j : Fin n, (sample i - sample j) ^ 2) := by
  classical
  have hpair := FiniteSum.pair_sum_eq_ordered_swap_sum
    (fun i j : Fin n => (sample i - sample j) ^ 2) (by
      intro i
      ring)
  have hordered :
      (∑ i : Fin n, ∑ j : Fin n,
        if i < j then (sample i - sample j) ^ 2 + (sample j - sample i) ^ 2 else 0) =
          2 * finiteSampleOrderedPairSqSum sample := by
    calc
      (∑ i : Fin n, ∑ j : Fin n,
        if i < j then (sample i - sample j) ^ 2 + (sample j - sample i) ^ 2 else 0) =
          ∑ i : Fin n, ∑ j : Fin n,
            2 * (if i < j then (sample i - sample j) ^ 2 else 0) := by
              apply Finset.sum_congr rfl
              intro i _
              apply Finset.sum_congr rfl
              intro j _
              by_cases hij : i < j
              · simp [hij]
                ring
              · simp [hij]
      _ = ∑ i : Fin n,
            2 * (∑ j : Fin n, if i < j then (sample i - sample j) ^ 2 else 0) := by
              apply Finset.sum_congr rfl
              intro i _
              rw [Finset.mul_sum]
      _ = 2 * finiteSampleOrderedPairSqSum sample := by
              change (∑ i : Fin n,
                2 * (∑ j : Fin n, if i < j then (sample i - sample j) ^ 2 else 0)) =
                  2 * (∑ i : Fin n, ∑ j : Fin n,
                    if i < j then (sample i - sample j) ^ 2 else 0)
              rw [Finset.mul_sum]
  have hdouble :
      (∑ i : Fin n, ∑ j : Fin n, (sample i - sample j) ^ 2) =
        2 * finiteSampleOrderedPairSqSum sample := by
    calc
      (∑ i : Fin n, ∑ j : Fin n, (sample i - sample j) ^ 2) =
          ∑ i : Fin n, ∑ j : Fin n,
            if i < j then (sample i - sample j) ^ 2 + (sample j - sample i) ^ 2 else 0 := hpair
      _ = 2 * finiteSampleOrderedPairSqSum sample := hordered
  rw [hdouble]
  ring

/-- Maurer--Pontil's pairwise variance is exactly the usual unbiased finite
sample variance. -/
theorem finiteSamplePairwiseVariance_eq_unbiasedVariance
    {n : ℕ} (sample : Fin n → ℝ) (hn : 2 ≤ n) :
    finiteSamplePairwiseVariance sample = finiteSampleUnbiasedVariance sample := by
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le (by omega) hn))
  have hden : (n : ℝ) - 1 ≠ 0 := by
    have hgt : (1 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by omega) hn)
    linarith
  have hnum :
      finiteSampleOrderedPairSqSum sample =
        (n : ℝ) * ∑ i : Fin n, (sample i - finiteRealSampleMean sample) ^ 2 := by
    rw [finiteSampleOrderedPairSqSum_eq_half_doublePairSqSum,
      finiteSample_doublePairSqSum_eq_two_card_mul_centeredSqSum sample
        (lt_of_lt_of_le (by omega) hn)]
    ring
  unfold finiteSamplePairwiseVariance finiteSampleUnbiasedVariance
  rw [hnum]
  field_simp [hn0, hden]

/-- Both finite sample-variance normalizations are nonnegative in their
defined positive-denominator regimes. -/
theorem finiteSampleEmpiricalVariance_nonneg {n : ℕ} (sample : Fin n → ℝ) :
    0 ≤ finiteSampleEmpiricalVariance sample := by
  unfold finiteSampleEmpiricalVariance
  apply div_nonneg
  · exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  · positivity

/-- A pointwise nonnegative finite sample has a nonnegative arithmetic mean. -/
theorem finiteSampleMean_nonneg_of_forall_nonneg
    {n : ℕ} (sample : Fin n → ℝ) (hnonneg : ∀ index, 0 ≤ sample index) :
    0 ≤ finiteRealSampleMean sample := by
  rw [finiteRealSampleMean_eq_div]
  exact div_nonneg (Finset.sum_nonneg fun index _ => hnonneg index) (by positivity)

/-- A nonempty finite sample bounded above by `scale` has mean at most `scale`. -/
theorem finiteSampleMean_le_of_forall_le
    {n : ℕ} (sample : Fin n → ℝ) (scale : ℝ) (hn : 0 < n)
    (hupper : ∀ index, sample index ≤ scale) :
    finiteRealSampleMean sample ≤ scale := by
  have hsum : (∑ index, sample index) ≤ ∑ _index : Fin n, scale := by
    exact Finset.sum_le_sum fun index _ => hupper index
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [finiteRealSampleMean_eq_div]
  apply (div_le_iff₀ hnReal).mpr
  simpa [Fintype.card_fin, mul_comm] using hsum

/-- The empirical (`1/n`) variance of a range-bounded nonempty sample is at
most the squared range.  The sharper one-quarter constant is available from
the finite-PMF Popoviciu inequality when it is needed; this elementary form is
useful for normalization corrections. -/
theorem finiteSampleEmpiricalVariance_le_sq_of_nonneg_le_scale
    {n : ℕ} (sample : Fin n → ℝ) (scale : ℝ) (hn : 0 < n)
    (hbounded : ∀ index, 0 ≤ sample index ∧ sample index ≤ scale) :
    finiteSampleEmpiricalVariance sample ≤ scale ^ 2 := by
  have hmean_nonneg : 0 ≤ finiteRealSampleMean sample :=
    finiteSampleMean_nonneg_of_forall_nonneg sample (fun index => (hbounded index).1)
  have hmean_upper : finiteRealSampleMean sample ≤ scale :=
    finiteSampleMean_le_of_forall_le sample scale hn (fun index => (hbounded index).2)
  have hpoint : ∀ index, (sample index - finiteRealSampleMean sample) ^ 2 ≤ scale ^ 2 := by
    intro index
    have hleft : 0 ≤ scale - (sample index - finiteRealSampleMean sample) := by
      linarith [(hbounded index).2]
    have hright : 0 ≤ scale + (sample index - finiteRealSampleMean sample) := by
      linarith [(hbounded index).1]
    have hproduct : 0 ≤
        (scale - (sample index - finiteRealSampleMean sample)) *
          (scale + (sample index - finiteRealSampleMean sample)) :=
      mul_nonneg hleft hright
    nlinarith
  have hsum : (∑ index, (sample index - finiteRealSampleMean sample) ^ 2) ≤
      ∑ _index : Fin n, scale ^ 2 := by
    exact Finset.sum_le_sum fun index _ => hpoint index
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
  unfold finiteSampleEmpiricalVariance
  apply (div_le_iff₀ hnReal).mpr
  simpa [Fintype.card_fin, mul_comm] using hsum

/-- At a source-legal sample size, replacing the empirical (`1/n`) standard
deviation by the unbiased (`1/(n-1)`) one costs at most
`scale * sqrt (2 / n)` for a `[0, scale]` sample.  This is the exact
normalization correction needed when a finite MLE is compared with a theorem
stated using the unbiased variance. -/
theorem finiteSample_sqrtUnbiasedVariance_le_sqrtEmpiricalVariance_add_scale_sqrt_two_div_card
    {n : ℕ} (sample : Fin n → ℝ) (scale : ℝ) (hn : 2 ≤ n)
    (hbounded : ∀ index, 0 ≤ sample index ∧ sample index ≤ scale) :
    Real.sqrt (finiteSampleUnbiasedVariance sample) ≤
      Real.sqrt (finiteSampleEmpiricalVariance sample) +
        scale * Real.sqrt (2 / (n : ℝ)) := by
  have hnPos : 0 < n := by omega
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hnPos
  have hnSubPos : 0 < (n : ℝ) - 1 := by
    have : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    linarith
  have hnTwo : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hscale_nonneg : 0 ≤ scale := by
    have := (hbounded ⟨0, hnPos⟩).1
    linarith [(hbounded ⟨0, hnPos⟩).2]
  have hvariance_nonneg : 0 ≤ finiteSampleEmpiricalVariance sample :=
    finiteSampleEmpiricalVariance_nonneg sample
  have hvariance_upper : finiteSampleEmpiricalVariance sample ≤ scale ^ 2 :=
    finiteSampleEmpiricalVariance_le_sq_of_nonneg_le_scale sample scale hnPos hbounded
  have hdenominator : 1 / ((n : ℝ) - 1) ≤ 2 / (n : ℝ) := by
    rw [div_le_div_iff₀ hnSubPos hnReal]
    nlinarith
  have hcorrection : finiteSampleEmpiricalVariance sample / ((n : ℝ) - 1) ≤
      scale ^ 2 * (2 / (n : ℝ)) := by
    calc
      finiteSampleEmpiricalVariance sample / ((n : ℝ) - 1) =
          finiteSampleEmpiricalVariance sample * (1 / ((n : ℝ) - 1)) := by ring
      _ ≤ finiteSampleEmpiricalVariance sample * (2 / (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hdenominator hvariance_nonneg
      _ ≤ scale ^ 2 * (2 / (n : ℝ)) := by
        apply mul_le_mul_of_nonneg_right hvariance_upper
        positivity
  have hnormalization : finiteSampleUnbiasedVariance sample =
      finiteSampleEmpiricalVariance sample +
        finiteSampleEmpiricalVariance sample / ((n : ℝ) - 1) := by
    unfold finiteSampleUnbiasedVariance finiteSampleEmpiricalVariance
    field_simp [ne_of_gt hnReal, ne_of_gt hnSubPos]
    ring
  rw [hnormalization]
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · have hroot_sq : (Real.sqrt (finiteSampleEmpiricalVariance sample)) ^ 2 =
      finiteSampleEmpiricalVariance sample := Real.sq_sqrt hvariance_nonneg
    have hscale_root_sq :
        (scale * Real.sqrt (2 / (n : ℝ))) ^ 2 = scale ^ 2 * (2 / (n : ℝ)) := by
      rw [mul_pow, Real.sq_sqrt]
      positivity
    have hroot_nonneg : 0 ≤ Real.sqrt (finiteSampleEmpiricalVariance sample) :=
      Real.sqrt_nonneg _
    have hscaled_root_nonneg : 0 ≤ scale * Real.sqrt (2 / (n : ℝ)) :=
      mul_nonneg hscale_nonneg (Real.sqrt_nonneg _)
    have hcross_nonneg : 0 ≤
        Real.sqrt (finiteSampleEmpiricalVariance sample) *
          (scale * Real.sqrt (2 / (n : ℝ))) :=
      mul_nonneg hroot_nonneg hscaled_root_nonneg
    nlinarith

/-- The unbiased finite-sample variance dominates its empirical (`1/n`)
counterpart at every source-legal sample size. -/
theorem finiteSample_sqrtEmpiricalVariance_le_sqrtUnbiasedVariance
    {n : ℕ} (sample : Fin n → ℝ) (hn : 2 ≤ n) :
    Real.sqrt (finiteSampleEmpiricalVariance sample) ≤
      Real.sqrt (finiteSampleUnbiasedVariance sample) := by
  apply Real.sqrt_le_sqrt
  unfold finiteSampleEmpiricalVariance finiteSampleUnbiasedVariance
  have hsum_nonneg : 0 ≤ ∑ index, (sample index - finiteRealSampleMean sample) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hnReal : 0 < (n : ℝ) := by
    have hnNat : 0 < n := by omega
    exact_mod_cast hnNat
  have hnSubPos : 0 < (n : ℝ) - 1 := by
    have : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    linarith
  rw [div_le_div_iff₀ hnReal hnSubPos]
  nlinarith

/-- The unbiased finite sample variance is nonnegative once its source
denominator is positive. -/
theorem finiteSampleUnbiasedVariance_nonneg {n : ℕ} (sample : Fin n → ℝ)
    (hn : 2 ≤ n) :
    0 ≤ finiteSampleUnbiasedVariance sample := by
  unfold finiteSampleUnbiasedVariance
  apply div_nonneg
  · exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  · exact sub_nonneg.mpr (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr
      (by omega : n ≠ 0)))

/-- At every source-legal sample size, the unbiased estimator is exactly the
empirical-law variance multiplied by `n / (n - 1)`. -/
theorem finiteSampleUnbiasedVariance_eq_card_scale_empiricalVariance
    {n : ℕ} (sample : Fin n → ℝ) (hn : 2 ≤ n) :
    finiteSampleUnbiasedVariance sample =
      (n : ℝ) / ((n : ℝ) - 1) * finiteSampleEmpiricalVariance sample := by
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le (by omega) hn))
  have hden : (n : ℝ) - 1 ≠ 0 := by
    have hgt : (1 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by omega) hn)
    linarith
  unfold finiteSampleUnbiasedVariance finiteSampleEmpiricalVariance
  field_simp [hn0, hden]

/-- A source-legal unbiased sample variance of a sample in `[0, scale]` is
at most twice the squared scale.  The factor two is the exact worst-case
normalization loss at two observations; it is convenient when a later
empirical-Bernstein bound only needs a count-only radius. -/
theorem finiteSampleUnbiasedVariance_le_two_mul_sq_of_nonneg_le_scale
    {n : ℕ} (sample : Fin n → ℝ) (scale : ℝ) (hn : 2 ≤ n)
    (hbounded : ∀ index, 0 ≤ sample index ∧ sample index ≤ scale) :
    finiteSampleUnbiasedVariance sample ≤ 2 * scale ^ 2 := by
  have hnPos : 0 < n := by omega
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hnPos
  have hnSubPos : 0 < (n : ℝ) - 1 := by
    have : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    linarith
  have hnTwo : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hratio : (n : ℝ) / ((n : ℝ) - 1) ≤ 2 := by
    rw [div_le_iff₀ hnSubPos]
    linarith
  have hempiricalNonneg : 0 ≤ finiteSampleEmpiricalVariance sample :=
    finiteSampleEmpiricalVariance_nonneg sample
  have hempirical : finiteSampleEmpiricalVariance sample ≤ scale ^ 2 :=
    finiteSampleEmpiricalVariance_le_sq_of_nonneg_le_scale sample scale hnPos hbounded
  rw [finiteSampleUnbiasedVariance_eq_card_scale_empiricalVariance sample hn]
  calc
    (n : ℝ) / ((n : ℝ) - 1) * finiteSampleEmpiricalVariance sample ≤
        2 * finiteSampleEmpiricalVariance sample :=
      mul_le_mul_of_nonneg_right hratio hempiricalNonneg
    _ ≤ 2 * scale ^ 2 := by
      exact mul_le_mul_of_nonneg_left hempirical (by norm_num)

/-- The source pairwise statistic is the empirical-law variance with its
exact finite-sample correction factor. -/
theorem finiteSamplePairwiseVariance_eq_card_scale_empiricalVariance
    {n : ℕ} (sample : Fin n → ℝ) (hn : 2 ≤ n) :
    finiteSamplePairwiseVariance sample =
      (n : ℝ) / ((n : ℝ) - 1) * finiteSampleEmpiricalVariance sample := by
  rw [finiteSamplePairwiseVariance_eq_unbiasedVariance sample hn]
  exact finiteSampleUnbiasedVariance_eq_card_scale_empiricalVariance sample hn

end AppliedModelingLib
