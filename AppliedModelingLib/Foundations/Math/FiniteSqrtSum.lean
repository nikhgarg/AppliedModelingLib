import Mathlib

/-!
# Finite inverse-square-root sums

The elementary bound `∑_{k = 1}^n 1 / √k ≤ 2 √n` is used whenever
count-indexed confidence radii are summed over a finite observation history.
The proof is finite and algebraic; it does not invoke an integral comparison.
-/

namespace AppliedModelingLib

open scoped BigOperators

/-- A single inverse-square-root term is dominated by the corresponding
increment of `2 √n`. -/
theorem one_div_sqrt_cast_succ_le_two_mul_sqrt_sub
    (n : ℕ) :
    (1 : ℝ) / Real.sqrt ((n + 1 : ℕ) : ℝ) ≤
      2 * (Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt (n : ℝ)) := by
  have hsucc_pos : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hb_pos : 0 < Real.sqrt ((n + 1 : ℕ) : ℝ) := Real.sqrt_pos.2 hsucc_pos
  have ha_nonneg : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hb_nonneg : 0 ≤ Real.sqrt ((n + 1 : ℕ) : ℝ) := Real.sqrt_nonneg _
  have hsq : (Real.sqrt ((n + 1 : ℕ) : ℝ)) ^ 2 - (Real.sqrt (n : ℝ)) ^ 2 = 1 := by
    rw [Real.sq_sqrt (by positivity : 0 ≤ ((n + 1 : ℕ) : ℝ)),
      Real.sq_sqrt (by positivity : 0 ≤ (n : ℝ))]
    norm_num
  have horder : Real.sqrt (n : ℝ) ≤ Real.sqrt ((n + 1 : ℕ) : ℝ) := by
    exact Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ n)
  rw [div_le_iff₀ hb_pos]
  nlinarith

/-- The finite inverse-square-root sum has the sharp elementary envelope
`2 √n`. -/
theorem sum_range_one_div_sqrt_cast_le_two_sqrt (n : ℕ) :
    (∑ k ∈ Finset.range n, (1 : ℝ) / Real.sqrt ((k + 1 : ℕ) : ℝ)) ≤
      2 * Real.sqrt (n : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      calc
        (∑ k ∈ Finset.range n, (1 : ℝ) / Real.sqrt ((k + 1 : ℕ) : ℝ)) +
            (1 : ℝ) / Real.sqrt ((n + 1 : ℕ) : ℝ) ≤
            2 * Real.sqrt (n : ℝ) + (1 : ℝ) / Real.sqrt ((n + 1 : ℕ) : ℝ) :=
          by simpa [add_comm] using
            add_le_add_right ih ((1 : ℝ) / Real.sqrt ((n + 1 : ℕ) : ℝ))
        _ ≤ 2 * Real.sqrt (n : ℝ) +
            2 * (Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt (n : ℝ)) :=
          by simpa [add_comm] using
            add_le_add_left (one_div_sqrt_cast_succ_le_two_mul_sqrt_sub n)
              (2 * Real.sqrt (n : ℝ))
        _ = 2 * Real.sqrt ((n + 1 : ℕ) : ℝ) := by ring

/-- The cumulative count preceding one finite batch of observations. -/
def batchPrefix (batch : ℕ → ℕ) (time : ℕ) : ℕ :=
  ∑ index ∈ Finset.range time, batch index

/-- A finite prefix of batches bounded by `cap` has at most `time * cap`
observations.  This is the count invariant used when an entire episode batch
shares one pre-batch confidence radius. -/
theorem batchPrefix_le_mul_cap
    (batch : ℕ → ℕ) (cap time : ℕ)
    (hcap : ∀ index, index < time → batch index ≤ cap) :
    batchPrefix batch time ≤ time * cap := by
  unfold batchPrefix
  calc
    (∑ index ∈ Finset.range time, batch index) ≤
        ∑ _index ∈ Finset.range time, cap := by
          refine Finset.sum_le_sum ?_
          intro index hindex
          exact hcap index (Finset.mem_range.mp hindex)
    _ = time * cap := by simp

/--
A finite count may be held fixed while a bounded batch of observations is
written.  The resulting batched inverse-square-root sum is at most the batch
cap times the usual square-root envelope.  This is weaker than a one-visit
reindexing but needs no one-visit-per-episode assumption.
-/
theorem sum_range_batch_div_sqrt_prefix_le_two_mul_cap_mul_sqrt_total
    (batch : ℕ → ℕ) (cap n : ℕ)
    (hcap : ∀ time, time < n → batch time ≤ cap) :
    (∑ time ∈ Finset.range n,
      (batch time : ℝ) /
        Real.sqrt ((batchPrefix batch time + 1 : ℕ) : ℝ)) ≤
      2 * (cap : ℝ) *
        Real.sqrt ((∑ time ∈ Finset.range n, batch time : ℕ) : ℝ) := by
  induction n with
  | zero => simp [batchPrefix]
  | succ n ih =>
      let total : ℕ := ∑ time ∈ Finset.range n, batch time
      have hcapPrefix : ∀ time, time < n → batch time ≤ cap := by
        intro time htime
        exact hcap time (Nat.lt_trans htime (Nat.lt_succ_self n))
      have hprefix : batchPrefix batch n = total := by
        rfl
      have htotalSucc : (∑ time ∈ Finset.range (n + 1), batch time : ℕ) =
          total + batch n := by
        change (∑ time ∈ Finset.range (n + 1), batch time) =
          (∑ time ∈ Finset.range n, batch time) + batch n
        rw [Finset.sum_range_succ]
      rw [Finset.sum_range_succ, hprefix, htotalSucc]
      have hih := ih hcapPrefix
      change
        (∑ time ∈ Finset.range n,
          (batch time : ℝ) / Real.sqrt ((batchPrefix batch time + 1 : ℕ) : ℝ)) +
            (batch n : ℝ) / Real.sqrt ((total + 1 : ℕ) : ℝ) ≤
          2 * (cap : ℝ) * Real.sqrt ((total + batch n : ℕ) : ℝ)
      by_cases hbatch : batch n = 0
      · simp [hbatch]
        simpa [total] using hih
      · have hbatchPos : 0 < batch n := Nat.pos_of_ne_zero hbatch
        have hbatchOne : 1 ≤ batch n := hbatchPos
        have hbatchCapNat : batch n ≤ cap := hcap n (Nat.lt_succ_self n)
        have hbatchCap : (batch n : ℝ) ≤ cap := by exact_mod_cast hbatchCapNat
        have hsqrtPos : 0 < Real.sqrt ((total + 1 : ℕ) : ℝ) := by positivity
        have htermCap : (batch n : ℝ) / Real.sqrt ((total + 1 : ℕ) : ℝ) ≤
            (cap : ℝ) / Real.sqrt ((total + 1 : ℕ) : ℝ) := by
          apply (div_le_div_iff₀ hsqrtPos hsqrtPos).2
          exact mul_le_mul_of_nonneg_right hbatchCap hsqrtPos.le
        have hincrement := one_div_sqrt_cast_succ_le_two_mul_sqrt_sub total
        have hscaledIncrement :
            (cap : ℝ) / Real.sqrt ((total + 1 : ℕ) : ℝ) ≤
              (cap : ℝ) *
                (2 * (Real.sqrt ((total + 1 : ℕ) : ℝ) - Real.sqrt (total : ℝ))) := by
          calc
            (cap : ℝ) / Real.sqrt ((total + 1 : ℕ) : ℝ) =
                (cap : ℝ) * ((1 : ℝ) / Real.sqrt ((total + 1 : ℕ) : ℝ)) := by
                  ring
            _ ≤ (cap : ℝ) *
                (2 * (Real.sqrt ((total + 1 : ℕ) : ℝ) - Real.sqrt (total : ℝ))) :=
              mul_le_mul_of_nonneg_left hincrement (by positivity)
        have htotalOrder : total + 1 ≤ total + batch n := by omega
        have hsqrtOrder : Real.sqrt ((total + 1 : ℕ) : ℝ) ≤
            Real.sqrt ((total + batch n : ℕ) : ℝ) := by
          exact Real.sqrt_le_sqrt (by exact_mod_cast htotalOrder)
        have hscaledOrder : (cap : ℝ) *
              (2 * (Real.sqrt ((total + 1 : ℕ) : ℝ) - Real.sqrt (total : ℝ))) ≤
            (cap : ℝ) *
              (2 * (Real.sqrt ((total + batch n : ℕ) : ℝ) - Real.sqrt (total : ℝ))) := by
          gcongr
        calc
          (∑ time ∈ Finset.range n,
            (batch time : ℝ) / Real.sqrt ((batchPrefix batch time + 1 : ℕ) : ℝ)) +
              (batch n : ℝ) / Real.sqrt ((total + 1 : ℕ) : ℝ) ≤
              2 * (cap : ℝ) * Real.sqrt (total : ℝ) +
                (batch n : ℝ) / Real.sqrt ((total + 1 : ℕ) : ℝ) := by
                exact add_le_add_left (by simpa [total] using hih) _
          _ ≤ 2 * (cap : ℝ) * Real.sqrt (total : ℝ) +
              (cap : ℝ) *
                (2 * (Real.sqrt ((total + batch n : ℕ) : ℝ) - Real.sqrt (total : ℝ))) := by
                gcongr
                exact htermCap.trans (hscaledIncrement.trans hscaledOrder)
          _ = 2 * (cap : ℝ) * Real.sqrt ((total + batch n : ℕ) : ℝ) := by ring

/-- The finite real harmonic sum through `n` observations. -/
noncomputable def finiteHarmonicSum (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, (1 : ℝ) / ((k + 1 : ℕ) : ℝ)

/-- `finiteHarmonicSum` is the real coercion of Mathlib's rational harmonic
number. -/
theorem finiteHarmonicSum_eq_harmonic (n : ℕ) :
    finiteHarmonicSum n = (harmonic n : ℝ) := by
  simp [finiteHarmonicSum, harmonic, div_eq_mul_inv]

/-- The elementary logarithmic envelope for the finite harmonic sum. -/
theorem finiteHarmonicSum_le_one_add_log (n : ℕ) :
    finiteHarmonicSum n ≤ 1 + Real.log (n : ℝ) := by
  rw [finiteHarmonicSum_eq_harmonic]
  exact harmonic_le_one_add_log n

/-- The finite harmonic sum is monotone in its endpoint. -/
theorem finiteHarmonicSum_mono {m n : ℕ} (h : m ≤ n) :
    finiteHarmonicSum m ≤ finiteHarmonicSum n := by
  unfold finiteHarmonicSum
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h)
  intro _ _ _
  positivity

/-- Charging each finite batch to the *post*-batch cumulative count has no
batch-cap loss: every batch can be expanded into its individual unit visits.
This is the sharp harmonic bookkeeping used when a source-good-set condition
ensures the pre-batch count already dominates the possible batch size. -/
theorem sum_range_batch_div_prefix_add_batch_le_harmonic
    (batch : ℕ → ℕ) (n : ℕ) :
    (∑ time ∈ Finset.range n,
      (batch time : ℝ) /
        ((batchPrefix batch time + batch time : ℕ) : ℝ)) ≤
      finiteHarmonicSum (∑ time ∈ Finset.range n, batch time) := by
  induction n with
  | zero => simp [finiteHarmonicSum]
  | succ n ih =>
      let total : ℕ := ∑ time ∈ Finset.range n, batch time
      have hprefix : batchPrefix batch n = total := by rfl
      have htotalSucc :
          (∑ time ∈ Finset.range (n + 1), batch time : ℕ) = total + batch n := by
        change (∑ time ∈ Finset.range (n + 1), batch time) =
          (∑ time ∈ Finset.range n, batch time) + batch n
        rw [Finset.sum_range_succ]
      rw [Finset.sum_range_succ, hprefix, htotalSucc]
      have hihBound :
          (∑ time ∈ Finset.range n,
            (batch time : ℝ) /
              ((batchPrefix batch time + batch time : ℕ) : ℝ)) ≤
            finiteHarmonicSum total := by
        simpa [total] using ih
      by_cases hzero : batch n = 0
      · simp [hzero]
        simpa [total] using ih
      · have hbatchPos : 0 < batch n := Nat.pos_of_ne_zero hzero
        have hsplit :
            finiteHarmonicSum (total + batch n) = finiteHarmonicSum total +
              ∑ k ∈ Finset.range (batch n),
                (1 : ℝ) / ((total + k + 1 : ℕ) : ℝ) := by
          simp only [finiteHarmonicSum]
          rw [Finset.sum_range_add]
        have hterm : (batch n : ℝ) / ((total + batch n : ℕ) : ℝ) ≤
            ∑ k ∈ Finset.range (batch n),
              (1 : ℝ) / ((total + k + 1 : ℕ) : ℝ) := by
          have hconstant : (batch n : ℝ) / ((total + batch n : ℕ) : ℝ) =
              ∑ _k ∈ Finset.range (batch n),
                (1 : ℝ) / ((total + batch n : ℕ) : ℝ) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            ring
          rw [hconstant]
          apply Finset.sum_le_sum
          intro k hk
          apply one_div_le_one_div_of_le
          · positivity
          · exact_mod_cast (show total + k + 1 ≤ total + batch n by
              exact Nat.add_le_add_left (Nat.succ_le_of_lt (Finset.mem_range.mp hk)) total)
        calc
          (∑ time ∈ Finset.range n,
            (batch time : ℝ) /
              ((batchPrefix batch time + batch time : ℕ) : ℝ)) +
              (batch n : ℝ) / ((total + batch n : ℕ) : ℝ) ≤
              finiteHarmonicSum total + (batch n : ℝ) / ((total + batch n : ℕ) : ℝ) :=
            by linarith
          _ ≤ finiteHarmonicSum total +
              ∑ k ∈ Finset.range (batch n),
                (1 : ℝ) / ((total + k + 1 : ℕ) : ℝ) :=
            by linarith
          _ = finiteHarmonicSum (total + batch n) := by rw [hsplit]

/-- Once a selected batch starts with at least one full batch-cap of prior
observations, its frozen pre-batch reciprocal charge is at most twice the
post-batch harmonic charge.  This is the finite good-set version of the
usual `w_k / n_k` logarithmic argument. -/
theorem sum_range_selected_batch_div_prefix_le_two_mul_harmonic
    (batch : ℕ → ℕ) (cap n : ℕ) (selected : ℕ → Prop) [DecidablePred selected]
    (hcapPositive : 0 < cap)
    (hcap : ∀ time, time < n → batch time ≤ cap)
    (hselected : ∀ time, time < n → selected time → cap ≤ batchPrefix batch time) :
    (∑ time ∈ Finset.range n,
      if selected time then (batch time : ℝ) / (batchPrefix batch time : ℝ) else 0) ≤
      2 * finiteHarmonicSum (∑ time ∈ Finset.range n, batch time) := by
  have hpoint (time : ℕ) (htime : time < n) :
      (if selected time then (batch time : ℝ) / (batchPrefix batch time : ℝ) else 0) ≤
        2 * ((batch time : ℝ) /
          ((batchPrefix batch time + batch time : ℕ) : ℝ)) := by
    by_cases htimeSelected : selected time
    · rw [if_pos htimeSelected]
      have hprefixNat : cap ≤ batchPrefix batch time := hselected time htime htimeSelected
      have hbatchNat : batch time ≤ cap := hcap time htime
      have hbatchPrefixNat : batch time ≤ batchPrefix batch time := hbatchNat.trans hprefixNat
      have hprefixPos : 0 < (batchPrefix batch time : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le hcapPositive hprefixNat)
      have hpostPos : 0 < ((batchPrefix batch time + batch time : ℕ) : ℝ) := by
        exact_mod_cast Nat.add_pos_left (lt_of_lt_of_le hcapPositive hprefixNat) (batch time)
      rw [show 2 * ((batch time : ℝ) /
          ((batchPrefix batch time + batch time : ℕ) : ℝ)) =
          (2 * (batch time : ℝ)) /
            ((batchPrefix batch time + batch time : ℕ) : ℝ) by ring]
      apply (div_le_div_iff₀ hprefixPos hpostPos).2
      have hbatchNonneg : 0 ≤ (batch time : ℝ) := Nat.cast_nonneg _
      have hprefixNonneg : 0 ≤ (batchPrefix batch time : ℝ) := Nat.cast_nonneg _
      have hbatchPrefix : (batch time : ℝ) ≤ (batchPrefix batch time : ℝ) := by
        exact_mod_cast hbatchPrefixNat
      have hmul : (batch time : ℝ) * (batch time : ℝ) ≤
          (batch time : ℝ) * (batchPrefix batch time : ℝ) :=
        mul_le_mul_of_nonneg_left hbatchPrefix hbatchNonneg
      norm_num
      nlinarith
    · rw [if_neg htimeSelected]
      positivity
  calc
    (∑ time ∈ Finset.range n,
      if selected time then (batch time : ℝ) / (batchPrefix batch time : ℝ) else 0) ≤
        ∑ time ∈ Finset.range n,
          2 * ((batch time : ℝ) /
            ((batchPrefix batch time + batch time : ℕ) : ℝ)) := by
          apply Finset.sum_le_sum
          intro time htime
          exact hpoint time (Finset.mem_range.mp htime)
    _ = 2 * (∑ time ∈ Finset.range n,
          (batch time : ℝ) /
            ((batchPrefix batch time + batch time : ℕ) : ℝ)) := by
          rw [Finset.mul_sum]
    _ ≤ 2 * finiteHarmonicSum (∑ time ∈ Finset.range n, batch time) := by
          apply mul_le_mul_of_nonneg_left
            (sum_range_batch_div_prefix_add_batch_le_harmonic batch n)
          norm_num

/-- If a finite batch shares its pre-batch denominator, the batched harmonic
cost is controlled by the batch cap times the harmonic sum at the final total.
Unlike a per-observation reindexing, this permits repeated observations within
one batch. -/
theorem sum_range_batch_div_prefix_succ_le_cap_mul_harmonic
    (batch : ℕ → ℕ) (cap n : ℕ)
    (hcap : ∀ time, time < n → batch time ≤ cap) :
    (∑ time ∈ Finset.range n,
      (batch time : ℝ) / ((batchPrefix batch time + 1 : ℕ) : ℝ)) ≤
      (cap : ℝ) * finiteHarmonicSum
        (∑ time ∈ Finset.range n, batch time) := by
  induction n with
  | zero => simp [finiteHarmonicSum]
  | succ n ih =>
      let total : ℕ := ∑ time ∈ Finset.range n, batch time
      have hcapPrefix : ∀ time, time < n → batch time ≤ cap := by
        intro time htime
        exact hcap time (Nat.lt_trans htime (Nat.lt_succ_self n))
      have hprefix : batchPrefix batch n = total := by rfl
      have htotalSucc :
          (∑ time ∈ Finset.range (n + 1), batch time : ℕ) = total + batch n := by
        change (∑ time ∈ Finset.range (n + 1), batch time) =
          (∑ time ∈ Finset.range n, batch time) + batch n
        rw [Finset.sum_range_succ]
      rw [Finset.sum_range_succ, hprefix, htotalSucc]
      have hih := ih hcapPrefix
      have hihBound :
          (∑ time ∈ Finset.range n,
            (batch time : ℝ) / ((batchPrefix batch time + 1 : ℕ) : ℝ)) ≤
            (cap : ℝ) * finiteHarmonicSum total := by
        simpa [total] using hih
      change
        (∑ time ∈ Finset.range n,
          (batch time : ℝ) / ((batchPrefix batch time + 1 : ℕ) : ℝ)) +
            (batch n : ℝ) / ((total + 1 : ℕ) : ℝ) ≤
          (cap : ℝ) * finiteHarmonicSum (total + batch n)
      by_cases hzero : batch n = 0
      · simp [hzero]
        simpa [total] using hih
      · have hbpos : 0 < batch n := Nat.pos_of_ne_zero hzero
        have hbcap : (batch n : ℝ) ≤ cap := by
          exact_mod_cast hcap n (Nat.lt_succ_self n)
        have hdenPos : 0 < ((total + 1 : ℕ) : ℝ) := by positivity
        have htermCap :
            (batch n : ℝ) / ((total + 1 : ℕ) : ℝ) ≤
              (cap : ℝ) / ((total + 1 : ℕ) : ℝ) := by
          exact (div_le_div_iff_of_pos_right hdenPos).2 hbcap
        have hsplit :
            finiteHarmonicSum (total + batch n) = finiteHarmonicSum total +
              ∑ k ∈ Finset.range (batch n),
                (1 : ℝ) / ((total + k + 1 : ℕ) : ℝ) := by
          simp only [finiteHarmonicSum]
          rw [Finset.sum_range_add]
        have hfirstTail :
            (1 : ℝ) / ((total + 1 : ℕ) : ℝ) ≤
              ∑ k ∈ Finset.range (batch n),
                (1 : ℝ) / ((total + k + 1 : ℕ) : ℝ) := by
          simpa using
            (Finset.single_le_sum
              (f := fun k : ℕ => (1 : ℝ) / ((total + k + 1 : ℕ) : ℝ))
              (s := Finset.range (batch n))
              (fun _ _ => by positivity)
              (Finset.mem_range.mpr hbpos : 0 ∈ Finset.range (batch n)))
        have hscaledTail :
            (cap : ℝ) / ((total + 1 : ℕ) : ℝ) ≤
              (cap : ℝ) * ∑ k ∈ Finset.range (batch n),
                (1 : ℝ) / ((total + k + 1 : ℕ) : ℝ) := by
          simpa [div_eq_mul_inv] using
            mul_le_mul_of_nonneg_left hfirstTail (by positivity : (0 : ℝ) ≤ cap)
        calc
          (∑ time ∈ Finset.range n,
            (batch time : ℝ) / ((batchPrefix batch time + 1 : ℕ) : ℝ)) +
              (batch n : ℝ) / ((total + 1 : ℕ) : ℝ) ≤
              (cap : ℝ) * finiteHarmonicSum total +
                (batch n : ℝ) / ((total + 1 : ℕ) : ℝ) :=
            add_le_add_left hihBound _
          _ ≤ (cap : ℝ) * finiteHarmonicSum total +
                (cap : ℝ) / ((total + 1 : ℕ) : ℝ) := by
            gcongr
          _ ≤ (cap : ℝ) * finiteHarmonicSum total +
                (cap : ℝ) * ∑ k ∈ Finset.range (batch n),
                  (1 : ℝ) / ((total + k + 1 : ℕ) : ℝ) := by
            gcongr
          _ = (cap : ℝ) * finiteHarmonicSum (total + batch n) := by
            rw [hsplit]
            ring

/-- Cauchy--Schwarz aggregates finitely many square roots into the square root
of their total mass. -/
theorem sum_sqrt_le_sqrt_card_mul_sqrt_sum
    {ι : Type*} [Fintype ι] (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) :
    (∑ i, Real.sqrt (f i)) ≤
      Real.sqrt (Fintype.card ι : ℝ) * Real.sqrt (∑ i, f i) := by
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset ι)
    (fun _ => (1 : ℝ)) (fun i => Real.sqrt (f i))
  have hleft : (∑ i, (1 : ℝ) * Real.sqrt (f i)) = ∑ i, Real.sqrt (f i) := by
    simp
  have honeSq : (∑ _i : ι, (1 : ℝ) ^ 2) = (Fintype.card ι : ℝ) := by
    simp
  have hrootSq : (∑ i, (Real.sqrt (f i)) ^ 2) = ∑ i, f i := by
    apply Finset.sum_congr rfl
    intro i _
    exact Real.sq_sqrt (hf i)
  rw [hleft, honeSq, hrootSq] at hcs
  exact hcs

/-- Weighted finite Cauchy--Schwarz for square-root masses.  Unlike the
cardinality specialization above, the coefficient may vary with the index. -/
theorem sum_mul_sqrt_le_sqrt_sum_sq_mul_sqrt_sum
    {ι : Type*} [Fintype ι] (scale mass : ι → ℝ)
    (hmass : ∀ i, 0 ≤ mass i) :
    (∑ i, scale i * Real.sqrt (mass i)) ≤
      Real.sqrt (∑ i, (scale i) ^ 2) * Real.sqrt (∑ i, mass i) := by
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset ι)
    scale (fun i => Real.sqrt (mass i))
  have hrootSq : (∑ i, (Real.sqrt (mass i)) ^ 2) = ∑ i, mass i := by
    apply Finset.sum_congr rfl
    intro i _
    exact Real.sq_sqrt (hmass i)
  rw [hrootSq] at hcs
  exact hcs

/-- Weighted finite Cauchy--Schwarz in the inverse-square-root form used by
occupancy-weighted confidence radii.  Positive counts let the summand
`mass / √count` split into `√mass · √(mass / count)`. -/
theorem sum_div_sqrt_le_sqrt_sum_mul_sqrt_sum_div
    {ι : Type*} [Fintype ι] (mass count : ι → ℝ)
    (hmass : ∀ i, 0 ≤ mass i) (hcount : ∀ i, 0 < count i) :
    (∑ i, mass i / Real.sqrt (count i)) ≤
      Real.sqrt (∑ i, mass i) * Real.sqrt (∑ i, mass i / count i) := by
  have hratioNonneg : ∀ i, 0 ≤ mass i / count i := by
    intro i
    exact div_nonneg (hmass i) (hcount i).le
  have hsplit (i : ι) :
      mass i / Real.sqrt (count i) =
        Real.sqrt (mass i) * Real.sqrt (mass i / count i) := by
    rw [Real.sqrt_div (hmass i)]
    rw [← mul_div_assoc, Real.mul_self_sqrt (hmass i)]
  have hsumSq : (∑ i, (Real.sqrt (mass i)) ^ 2) = ∑ i, mass i := by
    apply Finset.sum_congr rfl
    intro i _
    exact Real.sq_sqrt (hmass i)
  calc
    (∑ i, mass i / Real.sqrt (count i)) =
        ∑ i, Real.sqrt (mass i) * Real.sqrt (mass i / count i) := by
          apply Finset.sum_congr rfl
          intro i _
          exact hsplit i
    _ ≤ Real.sqrt (∑ i, (Real.sqrt (mass i)) ^ 2) *
          Real.sqrt (∑ i, mass i / count i) :=
      sum_mul_sqrt_le_sqrt_sum_sq_mul_sqrt_sum
        (fun i => Real.sqrt (mass i)) (fun i => mass i / count i) hratioNonneg
    _ = Real.sqrt (∑ i, mass i) * Real.sqrt (∑ i, mass i / count i) := by
      rw [hsumSq]

/-- Weighted finite Cauchy--Schwarz for the product of an occupancy mass,
a nonnegative width, and an inverse-square-root count.  It keeps the width
quadratic paired with the same occupancy mass, rather than replacing the
width by a uniform range before aggregation. -/
theorem sum_mass_mul_width_div_sqrt_count_le_sqrt_sum_div_mul_sqrt_sum_mass_mul_sq
    {ι : Type*} [Fintype ι] (mass width count : ι → ℝ)
    (hmass : ∀ i, 0 ≤ mass i) (hwidth : ∀ i, 0 ≤ width i)
    (hcount : ∀ i, 0 < count i) :
    (∑ i, mass i * width i / Real.sqrt (count i)) ≤
      Real.sqrt (∑ i, mass i / count i) *
        Real.sqrt (∑ i, mass i * width i ^ 2) := by
  have hquadratic : ∀ i, 0 ≤ mass i * width i ^ 2 := by
    intro i
    exact mul_nonneg (hmass i) (sq_nonneg (width i))
  have hcs := sum_mul_sqrt_le_sqrt_sum_sq_mul_sqrt_sum
    (fun i => Real.sqrt (mass i / count i))
    (fun i => mass i * width i ^ 2) hquadratic
  have hscaleSq :
      (∑ i, (Real.sqrt (mass i / count i)) ^ 2) =
        ∑ i, mass i / count i := by
    apply Finset.sum_congr rfl
    intro i _
    exact Real.sq_sqrt (div_nonneg (hmass i) (hcount i).le)
  have hfactor (i : ι) :
      mass i * width i / Real.sqrt (count i) =
        Real.sqrt (mass i / count i) * Real.sqrt (mass i * width i ^ 2) := by
    rw [Real.sqrt_div (hmass i), Real.sqrt_mul (hmass i),
      Real.sqrt_sq_eq_abs, abs_of_nonneg (hwidth i)]
    calc
      mass i * width i / Real.sqrt (count i) =
          (Real.sqrt (mass i) * Real.sqrt (mass i)) * width i /
            Real.sqrt (count i) := by rw [Real.mul_self_sqrt (hmass i)]
      _ = _ := by ring
  calc
    (∑ i, mass i * width i / Real.sqrt (count i)) =
        ∑ i, Real.sqrt (mass i / count i) *
          Real.sqrt (mass i * width i ^ 2) := by
            apply Finset.sum_congr rfl
            intro i _
            exact hfactor i
    _ ≤ Real.sqrt (∑ i, (Real.sqrt (mass i / count i)) ^ 2) *
          Real.sqrt (∑ i, mass i * width i ^ 2) := hcs
    _ = _ := by rw [hscaleSq]

/--
The three-term square-root aggregation used when a covariance quadratic is
bounded by twice a reference quadratic, four times a nonnegative bonus-square
mass, and twice a mesh-square term.  This keeps the constants explicit:
`√(2 m² + 4 b + 2 r²) ≤ √2 m + 2 √b + √2 r`.
-/
theorem sqrt_le_sqrt_two_mul_add_two_sqrt_add_sqrt_two_mul_of_le
    {quadratic reference bonusSquare mesh : ℝ}
    (hquadratic : 0 ≤ quadratic) (hreference : 0 ≤ reference)
    (hbonusSquare : 0 ≤ bonusSquare) (hmesh : 0 ≤ mesh)
    (hbound : quadratic ≤
      2 * reference ^ 2 + 4 * bonusSquare + 2 * mesh ^ 2) :
    Real.sqrt quadratic ≤
      Real.sqrt 2 * reference + 2 * Real.sqrt bonusSquare + Real.sqrt 2 * mesh := by
  have hsqrtTwoSq : (Real.sqrt 2) ^ 2 = 2 := by
    exact Real.sq_sqrt (by norm_num)
  have hsqrtBonusSq : (Real.sqrt bonusSquare) ^ 2 = bonusSquare := by
    exact Real.sq_sqrt hbonusSquare
  have hfirstSecond :
      0 ≤ (Real.sqrt 2 * reference) * (2 * Real.sqrt bonusSquare) := by
    positivity
  have hfirstThird :
      0 ≤ (Real.sqrt 2 * reference) * (Real.sqrt 2 * mesh) := by
    positivity
  have hsecondThird :
      0 ≤ (2 * Real.sqrt bonusSquare) * (Real.sqrt 2 * mesh) := by
    positivity
  have hrhsNonneg :
      0 ≤ Real.sqrt 2 * reference + 2 * Real.sqrt bonusSquare + Real.sqrt 2 * mesh := by
    positivity
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) hrhsNonneg).mp
  rw [Real.sq_sqrt hquadratic]
  calc
    quadratic ≤ 2 * reference ^ 2 + 4 * bonusSquare + 2 * mesh ^ 2 := hbound
    _ ≤ (Real.sqrt 2 * reference + 2 * Real.sqrt bonusSquare +
        Real.sqrt 2 * mesh) ^ 2 := by
      nlinarith

end AppliedModelingLib
