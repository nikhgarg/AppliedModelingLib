import AppliedModelingLib.Queueing.MulticlassPalmFutureFactors

/-!
# Finite representatives of marked renewal prefixes

This module gives Borel representatives for a finite prefix of an IID stream
of arrival-gap/work pairs.  A fixed positive tail keeps the representative a
valid renewal input when it is reconstructed through the full future-factor
section.
-/

namespace AppliedModelingLib.Queueing

open MeasureTheory

noncomputable section

variable {Class : Type*} [Fintype Class]

/-- Extend a finite marked-renewal prefix with a fixed positive
arrival-gap/work tail. -/
def futurePairPrefixUnitExtension (N : ℕ) (u : Finset.range N → ℝ × ℝ) :
    ℕ → ℝ × ℝ :=
  fun r => if hr : r < N then u ⟨r, Finset.mem_range.mpr hr⟩ else (1, 1)

/-- The fixed-tail extension of a finite marked-renewal prefix is Borel. -/
theorem measurable_futurePairPrefixUnitExtension (N : ℕ) :
    Measurable (futurePairPrefixUnitExtension N) := by
  apply measurable_pi_lambda
  intro r
  by_cases hr : r < N
  · simpa [futurePairPrefixUnitExtension, dif_pos hr] using
      (measurable_pi_apply (X := fun _ : Finset.range N => ℝ × ℝ)
        ⟨r, Finset.mem_range.mpr hr⟩)
  · simp [futurePairPrefixUnitExtension, dif_neg hr]

/-- A visible coordinate of the fixed-tail representative agrees with the
supplied finite prefix. -/
theorem futurePairPrefixUnitExtension_eq_of_lt
    (N : ℕ) (u : Finset.range N → ℝ × ℝ) (r : ℕ) (hr : r < N) :
    futurePairPrefixUnitExtension N u r = u ⟨r, Finset.mem_range.mpr hr⟩ := by
  simp [futurePairPrefixUnitExtension, hr]

/-- Extend a finite marked-renewal prefix by one specified arrival gap and a
fixed positive tail.  This is useful when a finite replay needs to postpone
the next unseen arrival while retaining the visible prefix exactly. -/
def futurePairPrefixDelayedExtension (N : ℕ) (u : Finset.range N → ℝ × ℝ)
    (gap : ℝ) : ℕ → ℝ × ℝ :=
  fun r => if hr : r < N then u ⟨r, Finset.mem_range.mpr hr⟩
    else if r = N then (gap, 1) else (1, 1)

/-- The delayed finite-prefix extension is Borel jointly in the visible
prefix and the inserted arrival gap. -/
theorem measurable_futurePairPrefixDelayedExtension (N : ℕ) :
    Measurable (fun x : (Finset.range N → ℝ × ℝ) × ℝ =>
      futurePairPrefixDelayedExtension N x.1 x.2) := by
  apply measurable_pi_lambda
  intro r
  by_cases hr : r < N
  · simpa [futurePairPrefixDelayedExtension, dif_pos hr] using
    ((measurable_pi_apply (X := fun _ : Finset.range N => ℝ × ℝ)
        ⟨r, Finset.mem_range.mpr hr⟩).comp measurable_fst)
  · by_cases hEq : r = N
    · subst r
      simp [futurePairPrefixDelayedExtension]
      exact measurable_snd.prodMk measurable_const
    · simp [futurePairPrefixDelayedExtension, dif_neg hr, hEq]

/-- A visible coordinate of the delayed representative agrees with the
supplied finite prefix. -/
theorem futurePairPrefixDelayedExtension_eq_of_lt
    (N : ℕ) (u : Finset.range N → ℝ × ℝ) (gap : ℝ) (r : ℕ) (hr : r < N) :
    futurePairPrefixDelayedExtension N u gap r = u ⟨r, Finset.mem_range.mpr hr⟩ := by
  simp [futurePairPrefixDelayedExtension, hr]

/-- The inserted coordinate of the delayed representative has the prescribed
arrival gap and a fixed positive work mark. -/
theorem futurePairPrefixDelayedExtension_apply_self
    (N : ℕ) (u : Finset.range N → ℝ × ℝ) (gap : ℝ) :
    futurePairPrefixDelayedExtension N u gap N = (gap, 1) := by
  simp [futurePairPrefixDelayedExtension]

/-- A labelled renewal epoch depends only on the arrival-gap components of
the pair stream through that label. -/
theorem arrivalTime_eq_of_pair_fst_eq_of_le
    (x y : ℕ → ℝ × ℝ) (n : ℕ)
    (hprefix : ∀ r ≤ n, (x r).1 = (y r).1) :
    Probability.PoissonProcess.arrivalTime n (fun r => (x r).1) =
      Probability.PoissonProcess.arrivalTime n (fun r => (y r).1) := by
  simp only [Probability.PoissonProcess.arrivalTime,
    Probability.PoissonProcess.interarrival]
  apply Finset.sum_congr rfl
  intro r hr
  exact hprefix r (Nat.le_of_lt_succ (Finset.mem_range.mp hr))

/-- Two valid full-future reconstructions have the same isolated passive
arrival at a positive label when their pair streams agree through that label. -/
theorem multiclassStationaryPoissonWorkClassTaggedArrival_fromFutureFactors_eq_of_pairPrefix
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Class) (j : {k : Class // k ≠ i})
    (x y : MulticlassPalmFutureFactorCarrier i j) (n : ℕ)
    (hprefix : ∀ r ≤ n, x.2 r = y.2 r)
    (hgoodx : Probability.PoissonProcess.equilibriumToSuspension
      ((MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ ℕ x.2).1, x.1.2.2.1.1) ∈
        {p : (ℤ → ℝ) × ℝ |
          p ∈ Probability.PoissonProcess.suspensionCarrier ∧
            Probability.PoissonProcess.suspensionGoodGapPath p.1})
    (hgoody : Probability.PoissonProcess.equilibriumToSuspension
      ((MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ ℕ y.2).1, y.1.2.2.1.1) ∈
        {p : (ℤ → ℝ) × ℝ |
          p ∈ Probability.PoissonProcess.suspensionCarrier ∧
            Probability.PoissonProcess.suspensionGoodGapPath p.1}) :
    multiclassStationaryPoissonWorkClassTaggedArrival i
      (multiclassStationaryPoissonWorkClassTaggedFromFutureFactors
        arrivalRate harrivalRate i j x)
      j.1 (Int.ofNat (n + 1)) =
      multiclassStationaryPoissonWorkClassTaggedArrival i
        (multiclassStationaryPoissonWorkClassTaggedFromFutureFactors
          arrivalRate harrivalRate i j y)
        j.1 (Int.ofNat (n + 1)) := by
  calc
    _ = Probability.PoissonProcess.arrivalTime n (fun r => (x.2 r).1) :=
      multiclassStationaryPoissonWorkClassTaggedArrival_fromFutureFactors_ofNat_succ
        arrivalRate harrivalRate i j x n hgoodx
    _ = Probability.PoissonProcess.arrivalTime n (fun r => (y.2 r).1) :=
      arrivalTime_eq_of_pair_fst_eq_of_le x.2 y.2 n
        (fun r hr => congrArg Prod.fst (hprefix r hr))
    _ = _ :=
      (multiclassStationaryPoissonWorkClassTaggedArrival_fromFutureFactors_ofNat_succ
        arrivalRate harrivalRate i j y n hgoody).symm

/-- The delayed representative has an explicit renewal-sum formula after the
visible prefix and inserted gap: every later gap is one. -/
theorem arrivalTime_futurePairPrefixDelayedExtension_add
    (N : ℕ) (u : Finset.range N → ℝ × ℝ) (gap : ℝ) (m : ℕ) :
    Probability.PoissonProcess.arrivalTime (N + m)
      (fun r => (futurePairPrefixDelayedExtension N u gap r).1) =
        (∑ r : Finset.range N, (u r).1) + gap + (m : ℝ) := by
  induction m with
  | zero =>
      simp only [Nat.add_zero, Probability.PoissonProcess.arrivalTime,
        Probability.PoissonProcess.interarrival, Finset.sum_range_succ]
      let f : ℕ → ℝ := fun r => if hr : r ∈ Finset.range N then (u ⟨r, hr⟩).1 else 0
      have hprefix :
          (∑ r ∈ Finset.range N, (futurePairPrefixDelayedExtension N u gap r).1) =
            ∑ r : Finset.range N, (u r).1 := by
        calc
          (∑ r ∈ Finset.range N,
              (futurePairPrefixDelayedExtension N u gap r).1) =
              ∑ r ∈ Finset.range N, f r := by
                apply Finset.sum_congr rfl
                intro r hr
                simp [f, futurePairPrefixDelayedExtension, Finset.mem_range.mp hr]
          _ = ∑ r : Finset.range N, f r.1 := (Finset.sum_attach _ _).symm
          _ = ∑ r : Finset.range N, (u r).1 := by
                apply Finset.sum_congr rfl
                intro r _
                change (if hr : (r : ℕ) ∈ Finset.range N then
                  (u ⟨r, hr⟩).1 else 0) = (u r).1
                rw [dif_pos r.2]
      rw [hprefix]
      simp [futurePairPrefixDelayedExtension]
  | succ m ih =>
      rw [show N + (m + 1) = (N + m) + 1 by omega]
      rw [show Probability.PoissonProcess.arrivalTime ((N + m) + 1)
          (fun r => (futurePairPrefixDelayedExtension N u gap r).1) =
          Probability.PoissonProcess.arrivalTime (N + m)
            (fun r => (futurePairPrefixDelayedExtension N u gap r).1) +
            (futurePairPrefixDelayedExtension N u gap (N + m + 1)).1 by
          simp [Probability.PoissonProcess.arrivalTime,
            Probability.PoissonProcess.interarrival, Finset.sum_range_succ]]
      rw [ih]
      have hlt : ¬ N + m + 1 < N := by omega
      have hne : N + m + 1 ≠ N := by omega
      simp [futurePairPrefixDelayedExtension, hlt, hne]
      ring

/-- The renewal epochs of a delayed finite-prefix representative diverge: its
tail has unit arrival gaps after one inserted coordinate. -/
theorem tendsto_arrivalTime_futurePairPrefixDelayedExtension
    (N : ℕ) (u : Finset.range N → ℝ × ℝ) (gap : ℝ) :
    Filter.Tendsto
      (fun n : ℕ => Probability.PoissonProcess.arrivalTime n
        (fun r => (futurePairPrefixDelayedExtension N u gap r).1))
      Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop.2 fun b => ?_
  let C : ℝ := (∑ r : Finset.range N, (u r).1) + gap
  obtain ⟨M, hM⟩ := exists_nat_ge (b - C)
  filter_upwards [Filter.eventually_ge_atTop (N + M)] with n hn
  have hnN : N ≤ n := by omega
  have hMN : M ≤ n - N := Nat.le_sub_of_add_le (by simpa [Nat.add_comm] using hn)
  have hMreal : (M : ℝ) ≤ ((n - N : ℕ) : ℝ) := by exact_mod_cast hMN
  rw [← Nat.add_sub_of_le hnN,
    arrivalTime_futurePairPrefixDelayedExtension_add]
  change b ≤ C + ((n - N : ℕ) : ℝ)
  linarith

/-- Positivity of the visible arrival gaps and inserted gap makes every gap
of the delayed representative strictly positive. -/
theorem futurePairPrefixDelayedExtension_fst_pos
    (N : ℕ) (u : Finset.range N → ℝ × ℝ) (gap : ℝ)
    (hprefix : ∀ r, 0 < (u r).1) (hgap : 0 < gap) :
    ∀ r, 0 < (futurePairPrefixDelayedExtension N u gap r).1 := by
  intro r
  by_cases hr : r < N
  · rw [futurePairPrefixDelayedExtension_eq_of_lt N u gap r hr]
    exact hprefix ⟨r, Finset.mem_range.mpr hr⟩
  · by_cases hEq : r = N
    · subst r
      simp [futurePairPrefixDelayedExtension, hgap]
    · simp [futurePairPrefixDelayedExtension, hr, hEq]

/-- A delayed finite-prefix representative reconstructs to a good suspension
whenever its retained equilibrium past is valid and its visible arrival gaps
are positive. -/
theorem equilibriumToSuspension_mem_good_of_futurePairPrefixDelayed
    (N : ℕ) (u : Finset.range N → ℝ × ℝ) (gap : ℝ) (past : ℕ → ℝ)
    (hprefix : ∀ r, 0 < (u r).1) (hgap : 0 < gap)
    (hpastPos : ∀ n, 0 < past (n + 1)) (hpastZero : 0 ≤ past 0)
    (hpast : Filter.Tendsto (fun n : ℕ => Probability.PoissonProcess.arrivalTime n past)
      Filter.atTop Filter.atTop) :
    Probability.PoissonProcess.equilibriumToSuspension
      ((MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ ℕ
        (futurePairPrefixDelayedExtension N u gap)).1, past) ∈
        {p : (ℤ → ℝ) × ℝ |
          p ∈ Probability.PoissonProcess.suspensionCarrier ∧
            Probability.PoissonProcess.suspensionGoodGapPath p.1} := by
  apply Probability.PoissonProcess.equilibriumToSuspension_mem_good_of_positive_of_future_past
  · simpa [MeasurableEquiv.arrowProdEquivProdArrow] using
      futurePairPrefixDelayedExtension_fst_pos N u gap hprefix hgap
  · exact hpastPos
  · exact hpastZero
  · simpa [MeasurableEquiv.arrowProdEquivProdArrow] using
      tendsto_arrivalTime_futurePairPrefixDelayedExtension N u gap
  · exact hpast

/-- Replacing the unseen tail of an already-good marked renewal input by a
delayed finite-prefix representative preserves the good suspension carrier.
The equilibrium past is retained literally. -/
theorem equilibriumToSuspension_mem_good_of_futurePairPrefixDelayed_of_mem_good
    (stream : ℕ → ℝ × ℝ) (past : ℕ → ℝ) (N : ℕ) (gap : ℝ)
    (hgood : Probability.PoissonProcess.equilibriumToSuspension
      ((MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ ℕ stream).1, past) ∈
        {p : (ℤ → ℝ) × ℝ |
          p ∈ Probability.PoissonProcess.suspensionCarrier ∧
            Probability.PoissonProcess.suspensionGoodGapPath p.1})
    (hgap : 0 < gap) :
    Probability.PoissonProcess.equilibriumToSuspension
      ((MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ ℕ
        (futurePairPrefixDelayedExtension N (fun r => stream r) gap)).1, past) ∈
        {p : (ℤ → ℝ) × ℝ |
          p ∈ Probability.PoissonProcess.suspensionCarrier ∧
            Probability.PoissonProcess.suspensionGoodGapPath p.1} := by
  have hfuturePos :=
    Probability.PoissonProcess.equilibriumToSuspension_future_pos_of_mem_good
      (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ ℕ stream).1 past hgood
  have hpastPos :=
    Probability.PoissonProcess.equilibriumToSuspension_past_pos_succ_of_mem_good
      (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ ℕ stream).1 past hgood
  have hpastZero :=
    Probability.PoissonProcess.equilibriumToSuspension_past_zero_nonneg_of_mem_good
      (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ ℕ stream).1 past hgood
  have hpast :=
    Probability.PoissonProcess.tendsto_arrivalTime_equilibriumToSuspension_past_of_mem_good
      (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ ℕ stream).1 past hgood
  apply equilibriumToSuspension_mem_good_of_futurePairPrefixDelayed
    N (fun r => stream r) gap past
  · intro r
    simpa [MeasurableEquiv.arrowProdEquivProdArrow] using hfuturePos r
  · exact hgap
  · exact hpastPos
  · exact hpastZero
  · exact hpast

/-- For any deterministic horizon, some positive integer inserted gap places
the next unseen renewal arrival strictly beyond that horizon. -/
theorem exists_nat_futurePairPrefixDelayed_arrivalTime_gt
    (N : ℕ) (u : Finset.range N → ℝ × ℝ) (t : ℝ) :
    ∃ M : ℕ, 0 < (M : ℝ) ∧ t <
      Probability.PoissonProcess.arrivalTime N
        (fun r => (futurePairPrefixDelayedExtension N u (M : ℝ) r).1) := by
  let C : ℝ := ∑ r : Finset.range N, (u r).1
  obtain ⟨M, hM⟩ := exists_nat_gt (max 0 (t - C))
  refine ⟨M, ?_, ?_⟩
  · exact lt_of_le_of_lt (le_max_left _ _) hM
  · have harrival :
        Probability.PoissonProcess.arrivalTime N
          (fun r => (futurePairPrefixDelayedExtension N u (M : ℝ) r).1) =
          C + (M : ℝ) := by
          simpa [C] using
            (arrivalTime_futurePairPrefixDelayedExtension_add N u (M : ℝ) 0)
    rw [harrival]
    have hbound : t - C < (M : ℝ) :=
      lt_of_le_of_lt (le_max_right _ _) hM
    linarith

/-- Reassemble the full selected-Palm future-factor carrier from its external
state and a visible finite IID arrival-gap/work prefix. -/
def multiclassPalmFuturePairPrefixRepresentative
    (i : Class) (j : {k : Class // k ≠ i}) (N : ℕ) :
    MulticlassPalmFutureExternalCarrier i j × (Finset.range N → ℝ × ℝ) →
      MulticlassPalmFutureFactorCarrier i j :=
  fun x => (x.1, futurePairPrefixUnitExtension N x.2)

/-- The full-factor finite-prefix representative is Borel. -/
theorem measurable_multiclassPalmFuturePairPrefixRepresentative
    (i : Class) (j : {k : Class // k ≠ i}) (N : ℕ) :
    Measurable (multiclassPalmFuturePairPrefixRepresentative i j N) := by
  exact measurable_fst.prodMk
    ((measurable_futurePairPrefixUnitExtension N).comp measurable_snd)

/-- Reassemble the full selected-Palm future-factor carrier after inserting a
specified next passive arrival gap beyond a visible finite prefix. -/
def multiclassPalmFuturePairPrefixDelayedRepresentative
    (i : Class) (j : {k : Class // k ≠ i}) (N : ℕ) :
    MulticlassPalmFutureExternalCarrier i j ×
      ((Finset.range N → ℝ × ℝ) × ℝ) →
      MulticlassPalmFutureFactorCarrier i j :=
  fun x => (x.1, futurePairPrefixDelayedExtension N x.2.1 x.2.2)

/-- The delayed full-factor finite-prefix representative is Borel. -/
theorem measurable_multiclassPalmFuturePairPrefixDelayedRepresentative
    (i : Class) (j : {k : Class // k ≠ i}) (N : ℕ) :
    Measurable (multiclassPalmFuturePairPrefixDelayedRepresentative i j N) := by
  exact measurable_fst.prodMk
    ((measurable_futurePairPrefixDelayedExtension N).comp measurable_snd)

/-- The delayed full-factor representative remains a good suspension input
whenever the original full pair factor is good and the inserted gap is
positive. -/
theorem multiclassPalmFuturePairPrefixDelayedRepresentative_mem_good
    (i : Class) (j : {k : Class // k ≠ i})
    (x : MulticlassPalmFutureFactorCarrier i j) (N : ℕ) (gap : ℝ)
    (hgood : Probability.PoissonProcess.equilibriumToSuspension
      ((MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ ℕ x.2).1, x.1.2.2.1.1) ∈
        {p : (ℤ → ℝ) × ℝ |
          p ∈ Probability.PoissonProcess.suspensionCarrier ∧
            Probability.PoissonProcess.suspensionGoodGapPath p.1})
    (hgap : 0 < gap) :
    Probability.PoissonProcess.equilibriumToSuspension
      ((MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ ℕ
        (multiclassPalmFuturePairPrefixDelayedRepresentative i j N
          (x.1, ((fun r : Finset.range N => x.2 r), gap))).2).1,
        (multiclassPalmFuturePairPrefixDelayedRepresentative i j N
          (x.1, ((fun r : Finset.range N => x.2 r), gap))).1.2.2.1.1) ∈
        {p : (ℤ → ℝ) × ℝ |
          p ∈ Probability.PoissonProcess.suspensionCarrier ∧
            Probability.PoissonProcess.suspensionGoodGapPath p.1} := by
  simpa [multiclassPalmFuturePairPrefixDelayedRepresentative] using
    (equilibriumToSuspension_mem_good_of_futurePairPrefixDelayed_of_mem_good
      x.2 x.1.2.2.1.1 N gap hgood hgap)

/-- A delayed full-factor representative retains every visible IID pair
coordinate of its original factor. -/
theorem multiclassPalmFuturePairPrefixDelayedRepresentative_apply_eq_of_lt
    (i : Class) (j : {k : Class // k ≠ i})
    (x : MulticlassPalmFutureFactorCarrier i j) (N : ℕ) (gap : ℝ)
    (r : ℕ) (hr : r < N) :
    (multiclassPalmFuturePairPrefixDelayedRepresentative i j N
      (x.1, ((fun s : Finset.range N => x.2 s), gap))).2 r = x.2 r := by
  simp [multiclassPalmFuturePairPrefixDelayedRepresentative,
    futurePairPrefixDelayedExtension, hr]

end

end AppliedModelingLib.Queueing
