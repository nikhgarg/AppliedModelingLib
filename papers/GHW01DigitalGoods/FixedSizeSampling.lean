import AppliedModelingLib.Foundations.Probability.FiniteExpectation
import AppliedModelingLib.Foundations.Probability.MeasureInequalities
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Uniform fixed-size sampling

This file supplies the exact without-replacement concentration statement used
by Goldberg--Hartline--Wright Lemma 6.1.  The key finite inequality is the
Maclaurin bound for elementary symmetric means; it compares the exponential
moment of a uniform fixed-size sample with the corresponding with-replacement
moment.
-/

namespace GHW01DigitalGoods

open AppliedModelingLib
open scoped BigOperators

noncomputable section

/-- Sum of all `r`-fold squarefree products drawn from a finite index set. -/
def elementarySubsetSum {α : Type*} [DecidableEq α]
    (s : Finset α) (x : α → ℝ) (r : ℕ) : ℝ :=
  ∑ t ∈ s.powersetCard r, ∏ i ∈ t, x i

@[simp]
theorem elementarySubsetSum_zero {α : Type*} [DecidableEq α]
    (s : Finset α) (x : α → ℝ) :
    elementarySubsetSum s x 0 = 1 := by
  simp [elementarySubsetSum]

@[simp]
theorem elementarySubsetSum_empty_succ {α : Type*} [DecidableEq α]
    (x : α → ℝ) (r : ℕ) :
    elementarySubsetSum ∅ x (r + 1) = 0 := by
  rw [elementarySubsetSum, Finset.powersetCard_eq_empty.mpr (by simp)]
  simp

/-- Pascal recurrence for elementary subset products. -/
theorem elementarySubsetSum_insert_succ {α : Type*} [DecidableEq α]
    (s : Finset α) (x : α → ℝ) {a : α} (ha : a ∉ s) (r : ℕ) :
    elementarySubsetSum (insert a s) x (r + 1) =
      elementarySubsetSum s x (r + 1) +
        x a * elementarySubsetSum s x r := by
  classical
  rw [elementarySubsetSum, Finset.powersetCard_succ_insert ha]
  have hdisj :
      Disjoint (s.powersetCard (r + 1))
        ((s.powersetCard r).image (insert a)) := by
    rw [Finset.disjoint_left]
    intro t htleft htright
    rcases Finset.mem_image.mp htright with ⟨u, hu, rfl⟩
    have hsub : u ⊆ s := (Finset.mem_powersetCard.mp hu).1
    have hat : a ∈ insert a u := by simp
    have hnot : a ∉ insert a u := by
      intro hamem
      have hsubset : insert a u ⊆ s :=
        (Finset.mem_powersetCard.mp htleft).1
      exact ha (hsubset hamem)
    exact hnot hat
  rw [Finset.sum_union hdisj]
  congr 1
  rw [Finset.sum_image]
  · calc
      (∑ u ∈ s.powersetCard r, ∏ i ∈ insert a u, x i) =
          ∑ u ∈ s.powersetCard r, x a * ∏ i ∈ u, x i := by
            refine Finset.sum_congr rfl ?_
            intro u hu
            have hau : a ∉ u := by
              intro hamem
              exact ha ((Finset.mem_powersetCard.mp hu).1 hamem)
            rw [Finset.prod_insert hau]
      _ = x a * elementarySubsetSum s x r := by
            rw [elementarySubsetSum, Finset.mul_sum]
  · intro u hu v hv huv
    have hau : a ∉ u := by
      intro hamem
      exact ha ((Finset.mem_powersetCard.mp hu).1 hamem)
    have hav : a ∉ v := by
      intro hamem
      exact ha ((Finset.mem_powersetCard.mp hv).1 hamem)
    calc
      u = (insert a u).erase a := (Finset.erase_insert hau).symm
      _ = (insert a v).erase a := congrArg (Finset.erase · a) huv
      _ = v := Finset.erase_insert hav

theorem elementarySubsetSum_nonneg {α : Type*} [DecidableEq α]
    (s : Finset α) (x : α → ℝ) (hx : ∀ i ∈ s, 0 ≤ x i) (r : ℕ) :
    0 ≤ elementarySubsetSum s x r := by
  classical
  unfold elementarySubsetSum
  exact Finset.sum_nonneg fun t ht =>
    Finset.prod_nonneg fun i hi =>
      hx i ((Finset.mem_powersetCard.mp ht).1 hi)

/--
Maclaurin's inequality in the finite form needed for sampling without
replacement: the average squarefree `r`-fold product is no larger than the
`r`-th power of the arithmetic mean.
-/
theorem elementarySubsetSum_le_choose_mul_mean_pow
    {α : Type*} [DecidableEq α]
    (s : Finset α) (x : α → ℝ) (hx : ∀ i ∈ s, 0 ≤ x i) (r : ℕ) :
    elementarySubsetSum s x r ≤
      (s.card.choose r : ℝ) *
        ((∑ i ∈ s, x i) / (s.card : ℝ)) ^ r := by
  classical
  induction s using Finset.induction_on generalizing r with
  | empty =>
      cases r with
      | zero => simp
      | succ r =>
          simp [elementarySubsetSum, Finset.powersetCard_eq_empty.mpr]
  | @insert a s ha ih =>
      have hxa : 0 ≤ x a := hx a (by simp)
      have hxs : ∀ i ∈ s, 0 ≤ x i := by
        intro i hi
        exact hx i (by simp [hi])
      cases r with
      | zero => simp
      | succ q =>
          let r : ℕ := q + 1
          let m : ℕ := s.card
          let n : ℕ := m + 1
          have hn_pos : 0 < n := by simp [n]
          have hn_ne : (n : ℝ) ≠ 0 := by positivity
          by_cases hrn : r ≤ n
          · have hqm : q ≤ m := by
              dsimp [r, n, m] at hrn ⊢
              omega
            by_cases hs0 : s = ∅
            · subst s
              have hm0 : m = 0 := by simp [m]
              have hn1 : n = 1 := by simp [n, hm0]
              have hr1 : r = 1 := by omega
              have hq0 : q = 0 := by simp [r] at hr1; omega
              subst q
              rw [elementarySubsetSum_insert_succ ∅ x ha 0]
              simp
            · have hm_pos : 0 < m := by
                simpa [m, Finset.card_pos] using
                  (Finset.nonempty_iff_ne_empty.mpr hs0)
              have hm_ne : (m : ℝ) ≠ 0 := by positivity
              let mean : ℝ := (∑ i ∈ s, x i) / (m : ℝ)
              have hsum_nonneg : 0 ≤ ∑ i ∈ s, x i :=
                Finset.sum_nonneg fun i hi => hxs i hi
              have hmean_nonneg : 0 ≤ mean := by
                exact div_nonneg hsum_nonneg (Nat.cast_nonneg m)
              have hiq := ih hxs q
              have hir :
                  elementarySubsetSum s x r ≤
                    (m.choose r : ℝ) * mean ^ r := by
                by_cases hrm : r ≤ m
                · simpa [m, mean] using ih hxs r
                · have hmr : m < r := Nat.lt_of_not_ge hrm
                  rw [elementarySubsetSum]
                  rw [Finset.powersetCard_eq_empty.mpr (by simpa [m] using hmr)]
                  simp [Nat.choose_eq_zero_of_lt hmr]
              have hiq' :
                  elementarySubsetSum s x q ≤
                    (m.choose q : ℝ) * mean ^ q := by
                simpa [m, mean] using hiq
              have hchoose_q_nat :
                  n * m.choose q = n.choose r * r := by
                simpa [n, m, r, Nat.mul_comm] using
                  (Nat.add_one_mul_choose_eq m q)
              have hchoose_q :
                  (m.choose q : ℝ) =
                    (n.choose r : ℝ) * (r : ℝ) / (n : ℝ) := by
                have hcast :
                    (n : ℝ) * (m.choose q : ℝ) =
                      (n.choose r : ℝ) * (r : ℝ) := by
                  exact_mod_cast hchoose_q_nat
                apply (eq_div_iff hn_ne).2
                nlinarith [hcast]
              have hchoose_r_nat :
                  m.choose r * n = n.choose r * (n - r) := by
                simpa [n, m] using Nat.choose_mul_succ_eq m r
              have hchoose_r :
                  (m.choose r : ℝ) =
                    (n.choose r : ℝ) * ((n : ℝ) - (r : ℝ)) / (n : ℝ) := by
                have hsubcast : ((n - r : ℕ) : ℝ) = (n : ℝ) - (r : ℝ) := by
                  rw [Nat.cast_sub hrn]
                have hcast :
                    (m.choose r : ℝ) * (n : ℝ) =
                      (n.choose r : ℝ) * ((n : ℝ) - (r : ℝ)) := by
                  exact_mod_cast hchoose_r_nat
                apply (eq_div_iff hn_ne).2
                nlinarith [hcast]
              let b : ℝ := (x a - mean) / (n : ℝ)
              have hb_lower : 0 ≤ 2 * mean + b := by
                dsimp [b]
                have hn_one : (1 : ℝ) ≤ n := by exact_mod_cast hn_pos
                have hdiv_lower : -mean ≤ (x a - mean) / (n : ℝ) := by
                  apply (le_div_iff₀ (by positivity : (0 : ℝ) < n)).2
                  have : -mean * (n : ℝ) ≤ -mean := by
                    have hneg : -mean ≤ 0 := neg_nonpos.mpr hmean_nonneg
                    nlinarith [mul_le_mul_of_nonpos_left hn_one hneg]
                  nlinarith
                nlinarith
              have hbern :=
                pow_add_mul_le_add_pow hmean_nonneg hb_lower r
              have hmean_update :
                  mean + b =
                    ((∑ i ∈ insert a s, x i) / (n : ℝ)) := by
                rw [Finset.sum_insert ha]
                dsimp [mean, b]
                field_simp
                simp [n]
                ring
              rw [elementarySubsetSum_insert_succ s x ha q]
              calc
                elementarySubsetSum s x r +
                    x a * elementarySubsetSum s x q
                    ≤ (m.choose r : ℝ) * mean ^ r +
                        x a * ((m.choose q : ℝ) * mean ^ q) := by
                      gcongr
                _ = (n.choose r : ℝ) *
                      (mean ^ r + (r : ℝ) * mean ^ (r - 1) * b) := by
                      rw [hchoose_q, hchoose_r]
                      have hqr : q = r - 1 := by simp [r]
                      rw [hqr]
                      have hpow : mean ^ r = mean * mean ^ (r - 1) := by
                        calc
                          mean ^ r = mean ^ ((r - 1) + 1) := by congr 1
                          _ = mean ^ (r - 1) * mean := by rw [pow_succ]
                          _ = mean * mean ^ (r - 1) := mul_comm _ _
                      dsimp [b]
                      field_simp
                      rw [hpow]
                      ring
                _ ≤ (n.choose r : ℝ) * (mean + b) ^ r := by
                      gcongr
                _ = (n.choose r : ℝ) *
                      ((∑ i ∈ insert a s, x i) / (n : ℝ)) ^ r := by
                      rw [hmean_update]
                _ = ((insert a s).card.choose r : ℝ) *
                      ((∑ i ∈ insert a s, x i) /
                        ((insert a s).card : ℝ)) ^ r := by
                      simp [ha, n, m]
          · have hnr : n < r := Nat.lt_of_not_ge hrn
            have hcard_lt : (insert a s).card < r := by
              simpa [n, m, ha] using hnr
            rw [elementarySubsetSum]
            rw [Finset.powersetCard_eq_empty.mpr hcard_lt]
            rw [Nat.choose_eq_zero_of_lt hcard_lt]
            simp

/-! ## Uniform fixed-size sample probabilities -/

/--
Probability of an event under the uniform law on the `k`-element subsets of
`A`, written as the exact finite cardinality ratio.
-/
def fixedSizeSampleProbability {α : Type*} [DecidableEq α]
    (A : Finset α) (k : ℕ) (event : Finset α → Prop)
    [DecidablePred event] : ℝ :=
  (((A.powersetCard k).filter event).card : ℝ) /
    ((A.powersetCard k).card : ℝ)

/-- Number of selected points that lie in `B`. -/
def fixedSizeHitCount {α : Type*} [DecidableEq α]
    (B sample : Finset α) : ℕ :=
  (sample ∩ B).card

theorem prod_membership_exp_eq_exp_hitCount
    {α : Type*} [DecidableEq α]
    (B sample : Finset α) (δ : ℝ) :
    (∏ i ∈ sample, if i ∈ B then Real.exp (-δ) else 1) =
      Real.exp (-δ * (fixedSizeHitCount B sample : ℝ)) := by
  classical
  rw [Finset.prod_ite]
  simp only [Finset.prod_const, mul_one,
    Finset.filter_mem_eq_inter, one_pow]
  rw [← Real.exp_nat_mul]
  congr 1
  simp [fixedSizeHitCount]
  ring

theorem sum_membership_exp
    {α : Type*} [DecidableEq α]
    {A B : Finset α} (hBA : B ⊆ A) (δ : ℝ) :
    (∑ i ∈ A, if i ∈ B then Real.exp (-δ) else 1) =
      (B.card : ℝ) * Real.exp (-δ) + ((A.card - B.card : ℕ) : ℝ) := by
  classical
  rw [Finset.sum_ite]
  have hfilter : A.filter (fun i => i ∈ B) = B := by
    ext i
    constructor
    · exact fun hi => (Finset.mem_filter.mp hi).2
    · intro hi
      exact Finset.mem_filter.mpr ⟨hBA hi, hi⟩
  have hfilter_not : A.filter (fun i => i ∉ B) = A \ B := by
    ext i
    simp
  have hcard_sdiff : (A \ B).card = A.card - B.card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hBA]
  rw [hfilter, hfilter_not]
  simp [hcard_sdiff]

/--
The exponential moment of a uniform fixed-size sample is at most the
corresponding with-replacement moment.  This is Hoeffding's comparison step,
derived here from the finite Maclaurin inequality.
-/
theorem fixedSize_exponential_sum_le
    {α : Type*} [DecidableEq α]
    {A B : Finset α} (hBA : B ⊆ A) (k : ℕ) (δ : ℝ) :
    (∑ sample ∈ A.powersetCard k,
        Real.exp (-δ * (fixedSizeHitCount B sample : ℝ))) ≤
      (A.card.choose k : ℝ) *
        (((A.card - B.card : ℕ) : ℝ) +
            (B.card : ℝ) * Real.exp (-δ)) ^ k /
          (A.card : ℝ) ^ k := by
  classical
  let weight : α → ℝ := fun i =>
    if i ∈ B then Real.exp (-δ) else 1
  have hweight_nonneg : ∀ i ∈ A, 0 ≤ weight i := by
    intro i hi
    by_cases hiB : i ∈ B
    · simp [weight, hiB, (Real.exp_pos (-δ)).le]
    · simp [weight, hiB]
  have hmac :=
    elementarySubsetSum_le_choose_mul_mean_pow A weight hweight_nonneg k
  have hsum :
      (∑ i ∈ A, weight i) =
        (B.card : ℝ) * Real.exp (-δ) +
          ((A.card - B.card : ℕ) : ℝ) := by
    simpa [weight] using sum_membership_exp hBA δ
  have hproduct :
      elementarySubsetSum A weight k =
        ∑ sample ∈ A.powersetCard k,
          Real.exp (-δ * (fixedSizeHitCount B sample : ℝ)) := by
    unfold elementarySubsetSum
    refine Finset.sum_congr rfl ?_
    intro sample hsample
    simpa [weight] using prod_membership_exp_eq_exp_hitCount B sample δ
  rw [hproduct, hsum] at hmac
  calc
    (∑ sample ∈ A.powersetCard k,
        Real.exp (-δ * (fixedSizeHitCount B sample : ℝ)))
        ≤ (A.card.choose k : ℝ) *
            (((B.card : ℝ) * Real.exp (-δ) +
                ((A.card - B.card : ℕ) : ℝ)) /
              (A.card : ℝ)) ^ k := hmac
    _ = (A.card.choose k : ℝ) *
        (((A.card - B.card : ℕ) : ℝ) +
            (B.card : ℝ) * Real.exp (-δ)) ^ k /
          (A.card : ℝ) ^ k := by
      rw [div_pow]
      ring

/-- The strict quadratic Taylor upper bound used in multiplicative Chernoff. -/
theorem exp_neg_lt_one_sub_add_sq_half {δ : ℝ} (hδ : 0 < δ) :
    Real.exp (-δ) < 1 - δ + δ ^ 2 / 2 := by
  let f : ℝ → ℝ := fun x => 1 - x + x ^ 2 / 2 - Real.exp (-x)
  have hfderiv : ∀ x : ℝ,
      HasDerivAt f (-1 + x + Real.exp (-x)) x := by
    intro x
    dsimp [f]
    convert
      (((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).add
        (((hasDerivAt_id x).pow 2).div_const 2)).sub
          ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)) using 1
    all_goals simp [id]
  have hcont : ContinuousOn f (Set.Icc 0 δ) := by
    intro x hx
    exact (hfderiv x).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ f (Set.Ioo 0 δ) := by
    intro x hx
    exact (hfderiv x).differentiableAt.differentiableWithinAt
  obtain ⟨c, hc, hslope⟩ :=
    exists_deriv_eq_slope f hδ hcont hdiff
  have hcderiv : deriv f c = -1 + c + Real.exp (-c) :=
    (hfderiv c).deriv
  have hcpos : 0 < deriv f c := by
    rw [hcderiv]
    have hexp : 1 - c < Real.exp (-c) :=
      Real.one_sub_lt_exp_neg hc.1.ne'
    linarith
  have hquot : 0 < (f δ - f 0) / (δ - 0) := by
    rw [← hslope]
    exact hcpos
  have hfdiff : 0 < f δ - f 0 :=
    ((div_pos_iff.mp hquot).resolve_right (by
      intro hneg
      linarith [hneg.2, hδ])).1
  dsimp [f] at hfdiff ⊢
  norm_num at hfdiff
  linarith

/--
Non-strict strengthening of the fixed-cardinality lower tail used in the
Theorem 6.2 fixed-half proof.  The eligible set is nonempty; without that
condition, the non-strict zero threshold event would be certain.
-/
theorem lemma6_1_fixed_size_lower_tail_le_of_nonempty
    {α : Type*} [DecidableEq α]
    {A B : Finset α} (hBA : B ⊆ A) (hB : B.Nonempty) {k : ℕ}
    (hk_pos : 0 < k) (hk_lt : k < A.card)
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_le_one : δ ≤ 1) :
    fixedSizeSampleProbability A k
        (fun sample =>
          (fixedSizeHitCount B sample : ℝ) ≤
            (1 - δ) * (B.card : ℝ) * (k : ℝ) / (A.card : ℝ)) <
      Real.exp
        (-((B.card : ℝ) * (k : ℝ) * δ ^ 2 /
          (2 * (A.card : ℝ)))) := by
  classical
  by_cases hB0 : B = ∅
  · exact False.elim ((Finset.nonempty_iff_ne_empty.mp hB) hB0)
  · let N : ℕ := A.card
    let b : ℕ := B.card
    let μ : ℝ := (b : ℝ) * (k : ℝ) / (N : ℝ)
    let threshold : ℝ := (1 - δ) * μ
    let samples : Finset (Finset α) := A.powersetCard k
    let bad : Finset (Finset α) :=
      samples.filter fun sample =>
        (fixedSizeHitCount B sample : ℝ) ≤ threshold
    let moment : ℝ :=
      ∑ sample ∈ samples,
        Real.exp (-δ * (fixedSizeHitCount B sample : ℝ))
    have hN_pos : 0 < N := by
      dsimp [N]
      omega
    have hN_ne : (N : ℝ) ≠ 0 := by positivity
    have hb_pos : 0 < b := by
      simpa [b, Finset.card_pos] using
        (Finset.nonempty_iff_ne_empty.mpr hB0)
    have hμ_pos : 0 < μ := by
      dsimp [μ]
      positivity
    have hchoose_pos_nat : 0 < N.choose k := by
      apply Nat.choose_pos
      simpa [N] using hk_lt.le
    have hchoose_pos : 0 < (N.choose k : ℝ) := by
      exact_mod_cast hchoose_pos_nat
    have hbad_point :
        ∀ sample ∈ bad,
          Real.exp (-δ * threshold) ≤
            Real.exp (-δ * (fixedSizeHitCount B sample : ℝ)) := by
      intro sample hsample
      have hle :
          (fixedSizeHitCount B sample : ℝ) ≤ threshold :=
        (Finset.mem_filter.mp hsample).2
      apply Real.exp_le_exp.mpr
      nlinarith
    have hbad_sum :
        (bad.card : ℝ) * Real.exp (-δ * threshold) ≤ moment := by
      have hto_bad :
          (bad.card : ℝ) * Real.exp (-δ * threshold) =
            ∑ sample ∈ bad, Real.exp (-δ * threshold) := by
        simp
      rw [hto_bad]
      calc
        (∑ sample ∈ bad, Real.exp (-δ * threshold)) ≤
            ∑ sample ∈ bad,
              Real.exp (-δ * (fixedSizeHitCount B sample : ℝ)) := by
              exact Finset.sum_le_sum fun sample hsample =>
                hbad_point sample hsample
        _ ≤ ∑ sample ∈ samples,
              Real.exp (-δ * (fixedSizeHitCount B sample : ℝ)) := by
              exact Finset.sum_le_sum_of_subset_of_nonneg
                (Finset.filter_subset _ _)
                (fun sample hsample hnot => (Real.exp_pos _).le)
        _ = moment := rfl
    have hmarkov :
        fixedSizeSampleProbability A k
            (fun sample =>
              (fixedSizeHitCount B sample : ℝ) ≤ threshold) ≤
          Real.exp (δ * threshold) *
            (moment / (N.choose k : ℝ)) := by
      have hscale_nonneg :
          0 ≤ Real.exp (δ * threshold) / (N.choose k : ℝ) := by
        positivity
      have hscaled :=
        mul_le_mul_of_nonneg_right hbad_sum hscale_nonneg
      have hbad_eq :
          ((samples.filter fun sample =>
              (fixedSizeHitCount B sample : ℝ) ≤ threshold).card : ℝ) =
            (bad.card : ℝ) := by rfl
      rw [fixedSizeSampleProbability, Finset.card_powersetCard]
      change
        ((bad.card : ℝ) / (N.choose k : ℝ)) ≤
          Real.exp (δ * threshold) *
            (moment / (N.choose k : ℝ))
      calc
        (bad.card : ℝ) / (N.choose k : ℝ) =
            ((bad.card : ℝ) * Real.exp (-δ * threshold)) *
              (Real.exp (δ * threshold) / (N.choose k : ℝ)) := by
                field_simp
                rw [mul_assoc, ← Real.exp_add]
                ring_nf
                simp
        _ ≤ moment *
              (Real.exp (δ * threshold) / (N.choose k : ℝ)) := hscaled
        _ = Real.exp (δ * threshold) *
              (moment / (N.choose k : ℝ)) := by ring
    have hmoment_raw :=
      fixedSize_exponential_sum_le hBA k δ
    have hmoment :
        moment / (N.choose k : ℝ) ≤
          ((((N - b : ℕ) : ℝ) +
              (b : ℝ) * Real.exp (-δ)) / (N : ℝ)) ^ k := by
      have hraw :
          moment ≤ (N.choose k : ℝ) *
            ((((N - b : ℕ) : ℝ) +
                (b : ℝ) * Real.exp (-δ)) / (N : ℝ)) ^ k := by
        have hraw' :
            moment ≤ (N.choose k : ℝ) *
                (((N - b : ℕ) : ℝ) +
                    (b : ℝ) * Real.exp (-δ)) ^ k /
                  (N : ℝ) ^ k := by
          simpa [moment, samples, N, b] using hmoment_raw
        calc
          moment ≤ (N.choose k : ℝ) *
                (((N - b : ℕ) : ℝ) +
                    (b : ℝ) * Real.exp (-δ)) ^ k /
                  (N : ℝ) ^ k := hraw'
          _ = (N.choose k : ℝ) *
                ((((N - b : ℕ) : ℝ) +
                    (b : ℝ) * Real.exp (-δ)) / (N : ℝ)) ^ k := by
              rw [div_pow]
              ring
      exact (div_le_iff₀ hchoose_pos).2 (by
        simpa [mul_comm] using hraw)
    let mean : ℝ :=
      (((N - b : ℕ) : ℝ) +
          (b : ℝ) * Real.exp (-δ)) / (N : ℝ)
    let u : ℝ := (b : ℝ) / (N : ℝ) * (Real.exp (-δ) - 1)
    have hb_le_N : b ≤ N := by
      simpa [b, N] using Finset.card_le_card hBA
    have hmean_eq : mean = 1 + u := by
      have hsubcast : ((N - b : ℕ) : ℝ) = (N : ℝ) - (b : ℝ) := by
        rw [Nat.cast_sub hb_le_N]
      dsimp [mean, u]
      rw [hsubcast]
      field_simp
      ring
    have hmean_nonneg : 0 ≤ mean := by
      dsimp [mean]
      positivity
    have hmean_exp : mean ^ k ≤ Real.exp ((k : ℝ) * u) := by
      have hbase : mean ≤ Real.exp u := by
        rw [hmean_eq]
        simpa [add_comm] using Real.add_one_le_exp u
      calc
        mean ^ k ≤ (Real.exp u) ^ k :=
          pow_le_pow_left₀ hmean_nonneg hbase k
        _ = Real.exp ((k : ℝ) * u) := by
          rw [← Real.exp_nat_mul]
    have hpre_exp :
        fixedSizeSampleProbability A k
            (fun sample =>
              (fixedSizeHitCount B sample : ℝ) ≤ threshold) ≤
          Real.exp (δ * threshold + (k : ℝ) * u) := by
      calc
        fixedSizeSampleProbability A k
            (fun sample =>
              (fixedSizeHitCount B sample : ℝ) ≤ threshold)
            ≤ Real.exp (δ * threshold) *
                (moment / (N.choose k : ℝ)) := hmarkov
        _ ≤ Real.exp (δ * threshold) * mean ^ k := by
              gcongr
        _ ≤ Real.exp (δ * threshold) *
              Real.exp ((k : ℝ) * u) := by
              gcongr
        _ = Real.exp (δ * threshold + (k : ℝ) * u) := by
              rw [Real.exp_add]
    have hexp_quad :
        Real.exp (-δ) < 1 - δ + δ ^ 2 / 2 :=
      exp_neg_lt_one_sub_add_sq_half hδ_pos
    have hexponent :
        δ * threshold + (k : ℝ) * u < -(μ * δ ^ 2 / 2) := by
      have hkR_pos : 0 < (k : ℝ) := by exact_mod_cast hk_pos
      have hbN_pos : 0 < (b : ℝ) / (N : ℝ) := by positivity
      have hku_eq :
          (k : ℝ) * u = μ * (Real.exp (-δ) - 1) := by
        dsimp [u, μ]
        field_simp
      rw [hku_eq]
      dsimp [threshold]
      have hmul := mul_lt_mul_of_pos_left
        (sub_lt_sub_right hexp_quad 1) hμ_pos
      nlinarith
    have hstrict_exp :
        Real.exp (δ * threshold + (k : ℝ) * u) <
          Real.exp (-(μ * δ ^ 2 / 2)) :=
      Real.exp_lt_exp.mpr hexponent
    have hfinal := lt_of_le_of_lt hpre_exp hstrict_exp
    convert hfinal using 1 <;> dsimp [threshold, μ, N, b] <;>
      field_simp

/-- Monotonicity of a fixed-size sample event under implication.  This is a
finite counting fact, kept separate from the source Lemma 6.1 statement. -/
theorem fixedSizeSampleProbability_mono
    {α : Type*} [DecidableEq α] (A : Finset α) (k : ℕ)
    {P Q : Finset α → Prop} [DecidablePred P] [DecidablePred Q]
    (hPQ : ∀ sample, P sample → Q sample) :
    fixedSizeSampleProbability A k P ≤ fixedSizeSampleProbability A k Q := by
  unfold fixedSizeSampleProbability
  apply div_le_div_of_nonneg_right
  · exact_mod_cast Finset.card_le_card (by
      intro sample hsample
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hsample).1,
          hPQ sample (Finset.mem_filter.mp hsample).2⟩)
  · positivity

/--
Goldberg--Hartline--Wright Lemma 6.1, exactly in the fixed-cardinality
without-replacement model.  The non-strict support strengthening above is
used only where the source proof's selected-prefix event requires it.
-/
theorem lemma6_1_fixed_size_lower_tail
    {α : Type*} [DecidableEq α]
    {A B : Finset α} (hBA : B ⊆ A) {k : ℕ}
    (hk_pos : 0 < k) (hk_lt : k < A.card)
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_le_one : δ ≤ 1) :
    fixedSizeSampleProbability A k
        (fun sample =>
          (fixedSizeHitCount B sample : ℝ) <
            (1 - δ) * (B.card : ℝ) * (k : ℝ) / (A.card : ℝ)) <
      Real.exp
        (-((B.card : ℝ) * (k : ℝ) * δ ^ 2 /
          (2 * (A.card : ℝ)))) := by
  classical
  by_cases hB : B.Nonempty
  · refine lt_of_le_of_lt ?_ (lemma6_1_fixed_size_lower_tail_le_of_nonempty
      hBA hB hk_pos hk_lt hδ_pos hδ_le_one)
    apply fixedSizeSampleProbability_mono A k
    intro sample hsample
    exact le_of_lt hsample
  · have hB0 : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hB
    subst B
    have hcardA_pos : 0 < A.card := lt_of_lt_of_le hk_pos hk_lt.le
    have hchoose_pos : 0 < A.card.choose k :=
      Nat.choose_pos hk_lt.le
    simp [fixedSizeSampleProbability, fixedSizeHitCount,
      Finset.card_powersetCard]

end

end GHW01DigitalGoods
