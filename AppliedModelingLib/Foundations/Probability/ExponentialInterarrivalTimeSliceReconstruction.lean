import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalDeterministicResidualTail

/-!
# Reconstruction across a deterministic renewal time slice

The deterministic-time factorization of a renewal path retains its complete
finite history and its fresh residual tail.  This module records the converse
path construction.  It is useful when a causal functional must be represented
explicitly on the history component of a deterministic-time factor.
-/

namespace AppliedModelingLib.Probability.PoissonProcess

open MeasureTheory Filter

noncomputable section

/-- Reconstruct an interarrival path from the finite history at a deterministic
clock and the fresh residual tail after that clock.  On an actual time-slice
pair, the first omitted gap is the residual gap plus the elapsed amount of
that gap. -/
def reconstructCanonicalRenewalPath (s : ℝ)
    (history : ℕ × (ℕ → ℝ)) (tail : ℕ → ℝ) : ℕ → ℝ :=
  fun k => if k < history.1 then history.2 k else
    if k = history.1 then
      tail 0 + (s - ∑ r ∈ Finset.range history.1, history.2 r)
    else tail (k - history.1)

/-- The deterministic time-slice reconstruction is Borel. -/
theorem measurable_reconstructCanonicalRenewalPath (s : ℝ) :
    Measurable (fun x : (ℕ × (ℕ → ℝ)) × (ℕ → ℝ) =>
      reconstructCanonicalRenewalPath s x.1 x.2) := by
  apply measurable_pi_iff.2
  intro k
  let h : ∀ x : (ℕ × (ℕ → ℝ)) × (ℕ → ℝ), ∃ n : ℕ, x.1.1 = n :=
    fun x => ⟨x.1.1, rfl⟩
  have hmeas : Measurable (fun x : (ℕ × (ℕ → ℝ)) × (ℕ → ℝ) =>
      if k < Nat.find (h x) then x.1.2 k else
        if k = Nat.find (h x) then
          x.2 0 + (s - ∑ r ∈ Finset.range (Nat.find (h x)), x.1.2 r)
        else x.2 (k - Nat.find (h x))) := by
    apply Measurable.ite
    · exact measurableSet_lt measurable_const (measurable_find h fun n =>
        (measurable_fst.comp measurable_fst) (measurableSet_singleton n))
    · exact (measurable_pi_apply k).comp (measurable_snd.comp measurable_fst)
    · apply Measurable.ite
      · have hfindmeas : Measurable (fun x : (ℕ × (ℕ → ℝ)) × (ℕ → ℝ) =>
            Nat.find (h x)) :=
          measurable_find h fun n =>
            (measurable_fst.comp measurable_fst) (measurableSet_singleton n)
        rw [show {x | k = Nat.find (h x)} =
            (fun x => Nat.find (h x)) ⁻¹' ({k} : Set ℕ) by
          ext x
          simp [eq_comm]]
        exact hfindmeas (measurableSet_singleton k)
      · exact (measurable_pi_apply 0).comp measurable_snd |>.add
          (measurable_const.sub (by
            let S : ℕ → ((ℕ × (ℕ → ℝ)) × (ℕ → ℝ)) → ℝ :=
              fun n x => ∑ r ∈ Finset.range n, x.1.2 r
            have hsum : Measurable (fun x => S (Nat.find (h x)) x) :=
              Measurable.find
                (fun n => (Finset.range n).measurable_sum fun r _ =>
                  (measurable_pi_apply r).comp (measurable_snd.comp measurable_fst))
                (fun n => (measurable_fst.comp measurable_fst)
                  (measurableSet_singleton n)) h
            simpa [S] using hsum))
      · let T : ℕ → ((ℕ × (ℕ → ℝ)) × (ℕ → ℝ)) → ℝ :=
          fun n x => x.2 (k - n)
        have htail : Measurable (fun x => T (Nat.find (h x)) x) :=
          Measurable.find
            (fun n => (measurable_pi_apply (k - n)).comp measurable_snd)
            (fun n => (measurable_fst.comp measurable_fst)
              (measurableSet_singleton n)) h
        simpa [T] using htail
  convert hmeas using 1
  funext x
  have hfind : Nat.find (h x) = x.1.1 := (Nat.find_spec (h x)).symm
  simp [reconstructCanonicalRenewalPath, hfind]

/-- Reconstructing an actual deterministic time slice gives back its original
interarrival path exactly. -/
theorem reconstructCanonicalRenewalPath_apply_timeSlice
    (s : ℝ) (omega : ℕ → ℝ) :
    reconstructCanonicalRenewalPath s (canonicalRenewalPastHistory s omega)
      (residualTail s omega) = omega := by
  funext k
  let n := canonicalRenewalCount s omega
  have hprefix : ∀ r, r < n →
      (canonicalRenewalPastHistory s omega).2 r = interarrival r omega := by
    intro r hr
    change paddedInterarrivalPrefix (canonicalRenewalCount s omega)
      (prefixInterarrival (canonicalRenewalCount s omega) omega) r = interarrival r omega
    rw [paddedInterarrivalPrefix_prefixInterarrival]
    simp only [dif_pos (by simpa [n] using hr)]
  by_cases hklt : k < n
  · simp only [reconstructCanonicalRenewalPath]
    rw [if_pos (by simpa [canonicalRenewalPastHistory, n] using hklt)]
    exact hprefix k hklt
  by_cases hkeq : k = n
  · subst k
    have hsum : ∑ r ∈ Finset.range n,
        (canonicalRenewalPastHistory s omega).2 r = arrivalPrefix n omega := by
      rw [arrivalPrefix]
      exact Finset.sum_congr rfl fun r hr => hprefix r (Finset.mem_range.mp hr)
    simp only [reconstructCanonicalRenewalPath]
    rw [if_neg (by simpa [canonicalRenewalPastHistory, n] using hklt)]
    rw [if_pos (by
      change n = canonicalRenewalCount s omega
      rfl)]
    change residualTail s omega 0 +
        (s - ∑ r ∈ Finset.range n,
          (canonicalRenewalPastHistory s omega).2 r) = omega n
    rw [show residualTail s omega 0 = arrivalTime n omega - s by
      simp [residualTail, n]]
    rw [hsum]
    simp [arrivalTime, arrivalPrefix, Finset.sum_range_succ, interarrival]
  · have hnlt : n < k := lt_of_le_of_ne (Nat.le_of_not_gt hklt) (Ne.symm hkeq)
    obtain ⟨m, hm⟩ : ∃ m, k = n + (m + 1) := by
      refine ⟨k - n - 1, ?_⟩
      omega
    subst k
    have hnotlt : ¬ n + (m + 1) < n := by omega
    have hnoteq : n + (m + 1) ≠ n := by omega
    simp only [reconstructCanonicalRenewalPath]
    rw [if_neg (by simpa [canonicalRenewalPastHistory, n] using hnotlt)]
    rw [if_neg (by simpa [canonicalRenewalPastHistory, n] using hnoteq)]
    change residualTail s omega (n + (m + 1) - n) = omega (n + (m + 1))
    simp [residualTail, n, interarrival]

/-- Replacing the unexposed tail after a deterministic clock with a path whose
first residual interval is positive preserves the complete finite history at
that clock. -/
theorem canonicalRenewalPastHistory_reconstructCanonicalRenewalPath
    (s : ℝ) (omega tail : ℕ → ℝ)
    (hfuture : ∃ m : ℕ, s < arrivalTime m omega)
    (htail : 0 < tail 0) :
    canonicalRenewalPastHistory s
      (reconstructCanonicalRenewalPath s (canonicalRenewalPastHistory s omega) tail) =
      canonicalRenewalPastHistory s omega := by
  let n := canonicalRenewalCount s omega
  let reconstructed := reconstructCanonicalRenewalPath s
    (canonicalRenewalPastHistory s omega) tail
  have hprefix : ∀ k, k < n → reconstructed k = omega k := by
    intro k hk
    simp only [reconstructed, reconstructCanonicalRenewalPath]
    rw [if_pos (by simpa [canonicalRenewalPastHistory, n] using hk)]
    change paddedInterarrivalPrefix n (prefixInterarrival n omega) k = omega k
    rw [paddedInterarrivalPrefix_prefixInterarrival]
    simp only [dif_pos hk, interarrival]
  have harrival_prefix : ∀ k, k < n → arrivalTime k reconstructed = arrivalTime k omega := by
    intro k hk
    unfold arrivalTime
    apply Finset.sum_congr rfl
    intro r hr
    exact hprefix r (Nat.lt_of_lt_of_le (Finset.mem_range.mp hr)
      (Nat.succ_le_of_lt hk))
  have harrival_n : arrivalTime n reconstructed = s + tail 0 := by
    simp only [arrivalTime, interarrival]
    rw [Finset.sum_range_succ]
    have hsum : ∑ r ∈ Finset.range n,
        reconstructed r = ∑ r ∈ Finset.range n, omega r := by
      apply Finset.sum_congr rfl
      intro r hr
      exact hprefix r (Finset.mem_range.mp hr)
    have hhistorysum : ∑ r ∈ Finset.range n,
        (canonicalRenewalPastHistory s omega).2 r =
          ∑ r ∈ Finset.range n, omega r := by
      apply Finset.sum_congr rfl
      intro r hr
      change paddedInterarrivalPrefix n (prefixInterarrival n omega) r = omega r
      rw [paddedInterarrivalPrefix_prefixInterarrival]
      simp only [dif_pos (Finset.mem_range.mp hr), interarrival]
    have hhistorycount : (canonicalRenewalPastHistory s omega).1 = n := rfl
    rw [hsum]
    simp only [reconstructed, reconstructCanonicalRenewalPath]
    rw [if_neg (by simp [hhistorycount]), if_pos hhistorycount.symm,
      hhistorycount, hhistorysum]
    ring
  have hfutureReconstructed : ∃ m : ℕ, s < arrivalTime m reconstructed :=
    ⟨n, by rw [harrival_n]; linarith⟩
  have hcount : canonicalRenewalCount s reconstructed = n := by
    rw [canonicalRenewalCount_eq_find s reconstructed hfutureReconstructed,
      Nat.find_eq_iff]
    constructor
    · simpa [harrival_n] using htail
    · intro m hm
      rw [harrival_prefix m hm]
      exact not_lt_of_ge (arrivalTime_le_of_lt_canonicalRenewalCount s omega hfuture hm)
  apply Prod.ext
  · simpa [canonicalRenewalPastHistory, reconstructed, n] using hcount
  · funext k
    change paddedInterarrivalPrefix (canonicalRenewalCount s reconstructed)
      (prefixInterarrival (canonicalRenewalCount s reconstructed) reconstructed) k =
        paddedInterarrivalPrefix n (prefixInterarrival n omega) k
    rw [hcount]
    by_cases hk : k < n
    · rw [paddedInterarrivalPrefix_prefixInterarrival,
        paddedInterarrivalPrefix_prefixInterarrival]
      simp only [dif_pos hk]
      simpa [interarrival] using hprefix k hk
    · simp [paddedInterarrivalPrefix, hk]

/-- A positive replacement tail has the same renewal count at the clock as the
original path. -/
theorem canonicalRenewalCount_reconstructCanonicalRenewalPath
    (s : ℝ) (omega tail : ℕ → ℝ)
    (hfuture : ∃ m : ℕ, s < arrivalTime m omega)
    (htail : 0 < tail 0) :
    canonicalRenewalCount s
      (reconstructCanonicalRenewalPath s (canonicalRenewalPastHistory s omega) tail) =
      canonicalRenewalCount s omega :=
  congrArg Prod.fst
    (canonicalRenewalPastHistory_reconstructCanonicalRenewalPath s omega tail hfuture htail)

/-- Every interarrival strictly before the deterministic-time count is
unchanged by replacing the unexposed tail with a positive continuation. -/
theorem interarrival_reconstructCanonicalRenewalPath_of_lt_count
    (s : ℝ) (omega tail : ℕ → ℝ)
    (hfuture : ∃ m : ℕ, s < arrivalTime m omega)
    (htail : 0 < tail 0) (k : ℕ)
    (hk : k < canonicalRenewalCount s omega) :
    interarrival k
      (reconstructCanonicalRenewalPath s (canonicalRenewalPastHistory s omega) tail) =
      interarrival k omega := by
  let reconstructed := reconstructCanonicalRenewalPath s
    (canonicalRenewalPastHistory s omega) tail
  have hhistory := canonicalRenewalPastHistory_reconstructCanonicalRenewalPath
    s omega tail hfuture htail
  have hcount := canonicalRenewalCount_reconstructCanonicalRenewalPath
    s omega tail hfuture htail
  have hk_reconstructed : k < canonicalRenewalCount s reconstructed := by
    change k < canonicalRenewalCount s
      (reconstructCanonicalRenewalPath s (canonicalRenewalPastHistory s omega) tail)
    rw [hcount]
    exact hk
  have hleft : (canonicalRenewalPastHistory s reconstructed).2 k =
      interarrival k reconstructed := by
    unfold canonicalRenewalPastHistory
    rw [paddedInterarrivalPrefix_prefixInterarrival]
    simp only [dif_pos hk_reconstructed]
  have hright : (canonicalRenewalPastHistory s omega).2 k = interarrival k omega := by
    unfold canonicalRenewalPastHistory
    rw [paddedInterarrivalPrefix_prefixInterarrival]
    simp only [dif_pos hk]
  calc
    interarrival k reconstructed = (canonicalRenewalPastHistory s reconstructed).2 k := hleft.symm
    _ = (canonicalRenewalPastHistory s omega).2 k := congrFun (congrArg Prod.snd hhistory) k
    _ = interarrival k omega := hright

/-- Arrival epochs after reconstruction split into the deterministic clock
and the renewal epochs of the replacement tail. -/
theorem arrivalTime_reconstructCanonicalRenewalPath_add_count
    (s : ℝ) (omega tail : ℕ → ℝ) (m : ℕ) :
    arrivalTime (canonicalRenewalCount s omega + m)
      (reconstructCanonicalRenewalPath s (canonicalRenewalPastHistory s omega) tail) =
      s + arrivalTime m tail := by
  let n := canonicalRenewalCount s omega
  let reconstructed := reconstructCanonicalRenewalPath s
    (canonicalRenewalPastHistory s omega) tail
  have hprefix : ∀ k, k < n → reconstructed k = omega k := by
    intro k hk
    simp only [reconstructed, reconstructCanonicalRenewalPath]
    rw [if_pos (by simpa [canonicalRenewalPastHistory, n] using hk)]
    change paddedInterarrivalPrefix n (prefixInterarrival n omega) k = omega k
    rw [paddedInterarrivalPrefix_prefixInterarrival]
    simp only [dif_pos hk, interarrival]
  have hsum : ∑ r ∈ Finset.range n, reconstructed r =
      ∑ r ∈ Finset.range n, omega r := by
    apply Finset.sum_congr rfl
    intro r hr
    exact hprefix r (Finset.mem_range.mp hr)
  have hhistorysum : ∑ r ∈ Finset.range n,
      (canonicalRenewalPastHistory s omega).2 r = ∑ r ∈ Finset.range n, omega r := by
    apply Finset.sum_congr rfl
    intro r hr
    change paddedInterarrivalPrefix n (prefixInterarrival n omega) r = omega r
    rw [paddedInterarrivalPrefix_prefixInterarrival]
    simp only [dif_pos (Finset.mem_range.mp hr), interarrival]
  have hcount : (canonicalRenewalPastHistory s omega).1 = n := rfl
  induction m with
  | zero =>
      change arrivalTime n reconstructed = s + arrivalTime 0 tail
      simp only [arrivalTime, interarrival]
      rw [Finset.sum_range_succ, hsum]
      simp only [reconstructed, reconstructCanonicalRenewalPath]
      rw [if_neg (by simp [hcount]), if_pos hcount.symm, hcount, hhistorysum]
      simp
      ring
  | succ m ih =>
      rw [show n + (m + 1) = (n + m) + 1 by omega]
      rw [show arrivalTime (n + m + 1) reconstructed = arrivalTime (n + m) reconstructed +
          interarrival (n + m + 1) reconstructed by
        simp [arrivalTime, Finset.sum_range_succ], ih]
      change s + arrivalTime m tail + reconstructed (n + m + 1) =
        s + arrivalTime (m + 1) tail
      have hgap : reconstructed (n + m + 1) = tail (m + 1) := by
        simp only [reconstructed, reconstructCanonicalRenewalPath]
        rw [if_neg (by omega), if_neg (by omega)]
        congr 1
        omega
      rw [hgap]
      rw [show arrivalTime (m + 1) tail = arrivalTime m tail + interarrival (m + 1) tail by
        simp [arrivalTime, Finset.sum_range_succ]]
      change s + arrivalTime m tail + tail (m + 1) =
        s + (arrivalTime m tail + tail (m + 1))
      ring

/-- A replacement tail with diverging renewal epochs gives a nonexplosive
reconstructed path. -/
theorem tendsto_arrivalTime_reconstructCanonicalRenewalPath
    (s : ℝ) (omega tail : ℕ → ℝ)
    (htail : Tendsto (fun n : ℕ => arrivalTime n tail) atTop atTop) :
    Tendsto (fun n : ℕ => arrivalTime n
      (reconstructCanonicalRenewalPath s (canonicalRenewalPastHistory s omega) tail))
      atTop atTop := by
  let count := canonicalRenewalCount s omega
  have hshift : Tendsto (fun n : ℕ => s + arrivalTime (n - count) tail) atTop atTop := by
    exact (tendsto_atTop_add_const_left atTop s htail).comp
      (tendsto_sub_atTop_nat count)
  apply hshift.congr'
  filter_upwards [eventually_ge_atTop count] with n hn
  rw [show n = count + (n - count) by omega,
    arrivalTime_reconstructCanonicalRenewalPath_add_count]
  congr 2
  omega

/-- Replacing the unexposed tail with a positive tail preserves positivity of
every interarrival, provided the original path reaches beyond the clock. -/
theorem all_interarrival_pos_reconstructCanonicalRenewalPath
    (s : ℝ) (omega tail : ℕ → ℝ)
    (hs : 0 ≤ s)
    (hfuture : ∃ m : ℕ, s < arrivalTime m omega)
    (hsource : ∀ k : ℕ, 0 < interarrival k omega)
    (htail : ∀ k : ℕ, 0 < interarrival k tail) :
    ∀ k : ℕ, 0 < interarrival k
      (reconstructCanonicalRenewalPath s (canonicalRenewalPastHistory s omega) tail) := by
  let n := canonicalRenewalCount s omega
  let reconstructed := reconstructCanonicalRenewalPath s
    (canonicalRenewalPastHistory s omega) tail
  have hhistorycount : (canonicalRenewalPastHistory s omega).1 = n := rfl
  have hncount : canonicalRenewalCount s omega = n := rfl
  intro k
  by_cases hk : k < n
  · rw [interarrival_reconstructCanonicalRenewalPath_of_lt_count s omega tail hfuture
      (htail 0) k hk]
    exact hsource k
  by_cases hkeq : k = n
  · subst k
    have hhistorysum : ∑ r ∈ Finset.range n,
        (canonicalRenewalPastHistory s omega).2 r = arrivalPrefix n omega := by
      unfold canonicalRenewalPastHistory
      rw [arrivalPrefix]
      apply Finset.sum_congr rfl
      intro r hr
      change (if h : r < canonicalRenewalCount s omega then interarrival r omega else 0) =
        interarrival r omega
      have hrlt : r < canonicalRenewalCount s omega := by
        rw [hncount]
        exact Finset.mem_range.mp hr
      simp [hrlt]
    have hprefixle : arrivalPrefix n omega ≤ s := by
      by_cases hnzero : n = 0
      · rw [hnzero]
        simp [arrivalPrefix, hs]
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hnzero
        have hpref : arrivalPrefix n omega = arrivalTime (n - 1) omega := by
          rw [show n = (n - 1) + 1 by omega]
          simp [arrivalPrefix, arrivalTime, Finset.sum_range_succ]
        rw [hpref]
        apply arrivalTime_le_of_lt_canonicalRenewalCount s omega hfuture
        rw [hncount]
        omega
    change 0 < reconstructed n
    simp only [reconstructed, reconstructCanonicalRenewalPath]
    rw [if_neg (by rw [hhistorycount]; exact hk), if_pos hhistorycount.symm]
    rw [hhistorycount, hhistorysum]
    have htailzero : 0 < tail 0 := htail 0
    linarith
  · have hgt : n < k := lt_of_le_of_ne (Nat.le_of_not_gt hk) (Ne.symm hkeq)
    change 0 < reconstructed k
    simp only [reconstructed, reconstructCanonicalRenewalPath]
    rw [if_neg (by rw [hhistorycount]; omega), if_neg (by rw [hhistorycount]; omega)]
    exact htail (k - n)

end

end AppliedModelingLib.Probability.PoissonProcess
