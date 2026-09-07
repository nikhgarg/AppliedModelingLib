import AppliedModelingLib.Foundations.Probability.PoissonSuspensionCampbellBridge
import AppliedModelingLib.Foundations.Probability.PoissonSuspensionReindexNonexplosion

/-!
# A measurable section from equilibrium coordinates to the Poisson suspension

The stationary Poisson construction is often factored through origin-split
equilibrium coordinates.  This module gives an explicit inverse on the
image of that factor and a total measurable section into the good suspension
carrier.  The totalization only chooses a fixed good state away from the
valid image; on genuine equilibrium coordinates it is the literal inverse.
-/

namespace AppliedModelingLib.Probability.PoissonProcess

open MeasureTheory ProbabilityTheory Filter

noncomputable section

/-- Reassemble a two-sided Palm gap path and phase from its origin-split
equilibrium future and past coordinates. -/
def equilibriumToSuspension :
    ((ℕ → ℝ) × (ℕ → ℝ)) → ((ℤ → ℝ) × ℝ) :=
  fun x =>
    (fun i => match i with
      | .ofNat 0 => x.1 0 + x.2 0
      | .ofNat (n + 1) => x.1 (n + 1)
      | .negSucc n => x.2 (n + 1), x.2 0)

/-- Reassembling the equilibrium coordinates of a suspension point is exactly
the original two-sided gap path and phase. -/
theorem equilibriumToSuspension_apply_suspensionToEquilibrium
    (p : (ℤ → ℝ) × ℝ) :
    equilibriumToSuspension (suspensionToEquilibrium p) = p := by
  rcases p with ⟨g, u⟩
  apply Prod.ext
  · funext i
    cases i with
    | ofNat n =>
        cases n with
        | zero => simp [equilibriumToSuspension, suspensionToEquilibrium,
            twoSidedGap]
        | succ n =>
            change g (Int.ofNat (n + 1)) = g (Int.ofNat (n + 1))
            rfl
    | negSucc n => simp [equilibriumToSuspension, suspensionToEquilibrium,
        twoSidedGap]
  · simp [equilibriumToSuspension, suspensionToEquilibrium]

/-- Splitting the equilibrium coordinates of a reassembled gap path recovers
the original future residual and backward-age paths. -/
theorem suspensionToEquilibrium_equilibriumToSuspension
    (x : (ℕ → ℝ) × (ℕ → ℝ)) :
    suspensionToEquilibrium (equilibriumToSuspension x) = x := by
  apply Prod.ext <;> funext n
  · cases n with
    | zero => simp [suspensionToEquilibrium, equilibriumToSuspension, twoSidedGap]
    | succ n =>
        change (match (n : ℤ) + 1 with
          | .ofNat 0 => x.1 0 + x.2 0
          | .ofNat (m + 1) => x.1 (m + 1)
          | .negSucc m => x.2 (m + 1)) = x.1 (n + 1)
        rw [show (n : ℤ) + 1 = Int.ofNat (n + 1) by
          change (n : ℤ) + 1 = (n + 1 : ℤ)
          ring]
  · cases n with
    | zero => simp [suspensionToEquilibrium, equilibriumToSuspension]
    | succ n =>
        simp [suspensionToEquilibrium, equilibriumToSuspension, twoSidedGap]

/-- The forward renewal epochs of an equilibrium reconstruction are the
exposed future renewal sums, translated by the equilibrium phase. -/
theorem arrivalTime_suspensionFuturePath_equilibriumToSuspension
    (future past : ℕ → ℝ) (n : ℕ) :
    arrivalTime n (suspensionFuturePath (equilibriumToSuspension (future, past)).1) =
      past 0 + arrivalTime n future := by
  induction n with
  | zero =>
      simp [arrivalTime, equilibriumToSuspension, suspensionFuturePath,
        interarrival, twoSidedGap]
      ring
  | succ n ih =>
      rw [show arrivalTime (n + 1)
          (suspensionFuturePath (equilibriumToSuspension (future, past)).1) =
          arrivalTime n
            (suspensionFuturePath (equilibriumToSuspension (future, past)).1) +
            interarrival (n + 1)
              (suspensionFuturePath (equilibriumToSuspension (future, past)).1) by
        simp [arrivalTime, Finset.sum_range_succ], ih]
      have hgap : interarrival (n + 1)
          (suspensionFuturePath (equilibriumToSuspension (future, past)).1) =
          future (n + 1) := by
        simp [interarrival, suspensionFuturePath, equilibriumToSuspension,
          twoSidedGap]
        rw [show (n : ℤ) + 1 = Int.ofNat (n + 1) by
          change (n : ℤ) + 1 = (n + 1 : ℤ)
          ring]
      rw [hgap]
      rw [show arrivalTime (n + 1) future = arrivalTime n future +
          interarrival (n + 1) future by simp [arrivalTime, Finset.sum_range_succ]]
      change past 0 + arrivalTime n future + future (n + 1) =
        past 0 + (arrivalTime n future + future (n + 1))
      ring

/-- Positive physical epochs of an equilibrium reconstruction are exactly the
renewal sums of its exposed future gap stream. -/
theorem candidatePalmArrival_equilibriumToSuspension_ofNat_succ_sub_phase
    (future past : ℕ → ℝ) (n : ℕ) :
    candidatePalmArrival (equilibriumToSuspension (future, past)).1
      (Int.ofNat (n + 1)) - (equilibriumToSuspension (future, past)).2 =
        arrivalTime n future := by
  rw [candidatePalmArrival_ofNat,
    candidateFutureEpoch_succ_eq_arrivalTime_suspension,
    arrivalTime_suspensionFuturePath_equilibriumToSuspension]
  simp [equilibriumToSuspension]

/-- The backward renewal epochs of an equilibrium reconstruction are the
exposed backward renewal sums, with the origin phase removed. -/
theorem arrivalTime_suspensionPastPath_equilibriumToSuspension
    (future past : ℕ → ℝ) (n : ℕ) :
    arrivalTime n (suspensionPastPath (equilibriumToSuspension (future, past)).1) =
      arrivalTime (n + 1) past - past 0 := by
  induction n with
  | zero =>
      simp [arrivalTime, equilibriumToSuspension, suspensionPastPath,
        interarrival, twoSidedGap, Finset.sum_range_succ]
  | succ n ih =>
      rw [show arrivalTime (n + 1)
          (suspensionPastPath (equilibriumToSuspension (future, past)).1) =
          arrivalTime n
            (suspensionPastPath (equilibriumToSuspension (future, past)).1) +
            interarrival (n + 1)
              (suspensionPastPath (equilibriumToSuspension (future, past)).1) by
        simp [arrivalTime, Finset.sum_range_succ], ih]
      have hgap : interarrival (n + 1)
          (suspensionPastPath (equilibriumToSuspension (future, past)).1) =
          past (n + 2) := by
        simp [interarrival, suspensionPastPath, equilibriumToSuspension,
          twoSidedGap, Nat.add_assoc]
      rw [hgap]
      rw [show arrivalTime ((n + 1) + 1) past = arrivalTime (n + 1) past +
          interarrival ((n + 1) + 1) past by
        simp [arrivalTime, Finset.sum_range_succ]]
      change arrivalTime (n + 1) past - past 0 + past (n + 2) =
        arrivalTime (n + 1) past + past (n + 2) - past 0
      ring

/-- The equilibrium-to-suspension reconstruction is Borel. -/
theorem measurable_equilibriumToSuspension : Measurable equilibriumToSuspension := by
  apply Measurable.prodMk
  · apply measurable_pi_iff.2
    intro i
    cases i with
    | ofNat n =>
        cases n with
        | zero =>
            simpa [equilibriumToSuspension] using
              ((measurable_pi_apply 0).comp measurable_fst).add
                ((measurable_pi_apply 0).comp measurable_snd)
        | succ n =>
            simpa [equilibriumToSuspension] using
              (measurable_pi_apply (n + 1)).comp measurable_fst
    | negSucc n =>
        simpa [equilibriumToSuspension] using
          (measurable_pi_apply (n + 1)).comp measurable_snd
  · simpa [equilibriumToSuspension] using
      (measurable_pi_apply 0).comp measurable_snd

/-- A fixed good suspension state, used only to totalize measurable sections
outside the valid equilibrium-coordinate image. -/
noncomputable def defaultGoodSuspensionState
    (rate : ℝ) (hrate : 0 < rate) : GoodSuspensionState := by
  letI : IsProbabilityMeasure (goodSuspensionMeasure rate) :=
    isProbabilityMeasure_goodSuspensionMeasure hrate
  exact Classical.choice (nonempty_of_isProbabilityMeasure (goodSuspensionMeasure rate))

/-- The total measurable section from equilibrium coordinates to the literal
good suspension carrier.  It agrees with `equilibriumToSuspension` whenever
that reconstruction is a valid good suspension state. -/
noncomputable def equilibriumToGoodSuspension
    (rate : ℝ) (hrate : 0 < rate) :
    ((ℕ → ℝ) × (ℕ → ℝ)) → GoodSuspensionState := by
  classical
  exact fun x =>
    if h : equilibriumToSuspension x ∈
        {p : (ℤ → ℝ) × ℝ | p ∈ suspensionCarrier ∧ suspensionGoodGapPath p.1}
      then ⟨equilibriumToSuspension x, h⟩
      else defaultGoodSuspensionState rate hrate

/-- The total equilibrium section is Borel. -/
theorem measurable_equilibriumToGoodSuspension
    (rate : ℝ) (hrate : 0 < rate) :
    Measurable (equilibriumToGoodSuspension rate hrate) := by
  classical
  let S : Set ((ℤ → ℝ) × ℝ) :=
    {p | p ∈ suspensionCarrier ∧ suspensionGoodGapPath p.1}
  let d := defaultGoodSuspensionState rate hrate
  let raw := equilibriumToSuspension
  let f : (ℕ → ℝ) × (ℕ → ℝ) → ((ℤ → ℝ) × ℝ) :=
    fun x => if raw x ∈ S then raw x else d.1
  have hraw : Measurable raw := measurable_equilibriumToSuspension
  have hS : MeasurableSet S := measurableSet_goodSuspensionState
  have hf : Measurable f := hraw.ite (hS.preimage hraw) measurable_const
  have hsub : equilibriumToGoodSuspension rate hrate =
      fun x => ⟨f x, by
        change f x ∈ S
        by_cases hx : raw x ∈ S
        · simpa [f, hx] using hx
        · simpa [f, hx] using d.2⟩ := by
    funext x
    apply Subtype.ext
    by_cases hx : raw x ∈ S
    · simp only [equilibriumToGoodSuspension]
      rw [dif_pos (by simpa [raw, S] using hx)]
      simp [f, hx]
      rfl
    · simp only [equilibriumToGoodSuspension]
      rw [dif_neg (by simpa [raw, S] using hx)]
      simp [f, hx]
      rfl
  rw [hsub]
  exact hf.subtype_mk

/-- Whenever the reconstructed raw equilibrium coordinates satisfy the good
suspension conditions, the total section is the literal subtype inclusion. -/
theorem equilibriumToGoodSuspension_eq_mk_of_mem
    (rate : ℝ) (hrate : 0 < rate) (x : (ℕ → ℝ) × (ℕ → ℝ))
    (hx : equilibriumToSuspension x ∈
      {p : (ℤ → ℝ) × ℝ | p ∈ suspensionCarrier ∧ suspensionGoodGapPath p.1}) :
    equilibriumToGoodSuspension rate hrate x = ⟨equilibriumToSuspension x, hx⟩ := by
  classical
  rw [equilibriumToGoodSuspension, dif_pos hx]

/-- On the actual suspension image, the total equilibrium section is the
literal inverse and does not use its arbitrary fallback value. -/
theorem equilibriumToGoodSuspension_apply_suspensionToEquilibrium
    (rate : ℝ) (hrate : 0 < rate) (p : GoodSuspensionState) :
    equilibriumToGoodSuspension rate hrate (suspensionToEquilibrium p.1) = p := by
  classical
  have hp : equilibriumToSuspension (suspensionToEquilibrium p.1) ∈
      {q : (ℤ → ℝ) × ℝ | q ∈ suspensionCarrier ∧ suspensionGoodGapPath q.1} := by
    rw [equilibriumToSuspension_apply_suspensionToEquilibrium]
    exact p.2
  rw [equilibriumToGoodSuspension, dif_pos hp]
  apply Subtype.ext
  exact equilibriumToSuspension_apply_suspensionToEquilibrium p.1

/-- Reassembling positive equilibrium renewal halves yields a literal good
suspension state whenever both ordinary halves are nonexplosive. -/
theorem equilibriumToSuspension_mem_good_of_positive_of_future_past
    (future past : ℕ → ℝ)
    (hfuturePos : ∀ n, 0 < future n)
    (hpastPos : ∀ n, 0 < past (n + 1))
    (hpastZero : 0 ≤ past 0)
    (hfuture : Tendsto (fun n : ℕ => arrivalTime n future) atTop atTop)
    (hpast : Tendsto (fun n : ℕ => arrivalTime n past) atTop atTop) :
    equilibriumToSuspension (future, past) ∈
      {p : (ℤ → ℝ) × ℝ | p ∈ suspensionCarrier ∧ suspensionGoodGapPath p.1} := by
  constructor
  · constructor
    · exact hpastZero
    · change past 0 < future 0 + past 0
      linarith [hfuturePos 0]
  · apply suspensionGoodGapPath_of_positive_of_future_past
    · intro i
      cases i with
      | ofNat n =>
          cases n with
          | zero =>
              change 0 < future 0 + past 0
              linarith [hfuturePos 0]
          | succ n =>
              simpa [equilibriumToSuspension, twoSidedGap] using hfuturePos (n + 1)
      | negSucc n =>
          simpa [equilibriumToSuspension, twoSidedGap] using hpastPos n
    · have hadd : Tendsto (fun n : ℕ => past 0 + arrivalTime n future) atTop atTop :=
        tendsto_atTop_add_const_left atTop (past 0) hfuture
      have heq := arrivalTime_suspensionFuturePath_equilibriumToSuspension future past
      apply hadd.congr'
      filter_upwards [] with n
      exact (heq n).symm
    · have htail : Tendsto (fun n : ℕ => arrivalTime (n + 1) past) atTop atTop := by
        simpa [Nat.succ_eq_add_one, add_comm] using hpast.comp (tendsto_add_atTop_nat 1)
      have hsub : Tendsto (fun n : ℕ => arrivalTime (n + 1) past - past 0) atTop atTop := by
        simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-past 0) htail
      have heq : ∀ n : ℕ,
          arrivalTime n (suspensionPastPath (equilibriumToSuspension (future, past)).1) =
            arrivalTime (n + 1) past - past 0 := by
        intro n
        induction n with
        | zero =>
            simp [arrivalTime, equilibriumToSuspension, suspensionPastPath,
              interarrival, twoSidedGap, Finset.sum_range_succ]
        | succ n ih =>
            rw [show arrivalTime (n + 1)
                (suspensionPastPath (equilibriumToSuspension (future, past)).1) =
                arrivalTime n
                  (suspensionPastPath (equilibriumToSuspension (future, past)).1) +
                  interarrival (n + 1)
                    (suspensionPastPath (equilibriumToSuspension (future, past)).1) by
              simp [arrivalTime, Finset.sum_range_succ], ih]
            have hgap : interarrival (n + 1)
                (suspensionPastPath (equilibriumToSuspension (future, past)).1) =
                past (n + 2) := by
              simp [interarrival, suspensionPastPath, equilibriumToSuspension,
                twoSidedGap, Nat.add_assoc]
            rw [hgap]
            rw [show arrivalTime ((n + 1) + 1) past = arrivalTime (n + 1) past +
                interarrival ((n + 1) + 1) past by
              simp [arrivalTime, Finset.sum_range_succ]]
            change arrivalTime (n + 1) past - past 0 + past (n + 2) =
              arrivalTime (n + 1) past + past (n + 2) - past 0
            ring
      apply hsub.congr'
      filter_upwards [] with n
      exact (heq n).symm

/-- A good equilibrium reconstruction has strictly positive exposed future
gaps, including its residual first gap. -/
theorem equilibriumToSuspension_future_pos_of_mem_good
    (future past : ℕ → ℝ)
    (hgood : equilibriumToSuspension (future, past) ∈
      {p : (ℤ → ℝ) × ℝ | p ∈ suspensionCarrier ∧ suspensionGoodGapPath p.1}) :
    ∀ n, 0 < future n := by
  intro n
  cases n with
  | zero =>
      have hcarrier := hgood.1
      change 0 ≤ past 0 ∧ past 0 < future 0 + past 0 at hcarrier
      linarith [hcarrier.2]
  | succ n =>
      simpa [equilibriumToSuspension, twoSidedGap] using
        hgood.2.1 (Int.ofNat (n + 1))

/-- A good equilibrium reconstruction has a nonnegative origin phase in its
exposed backward coordinate. -/
theorem equilibriumToSuspension_past_zero_nonneg_of_mem_good
    (future past : ℕ → ℝ)
    (hgood : equilibriumToSuspension (future, past) ∈
      {p : (ℤ → ℝ) × ℝ | p ∈ suspensionCarrier ∧ suspensionGoodGapPath p.1}) :
    0 ≤ past 0 := by
  exact hgood.1.1

/-- A good equilibrium reconstruction has strictly positive backward gaps
after its origin phase coordinate. -/
theorem equilibriumToSuspension_past_pos_succ_of_mem_good
    (future past : ℕ → ℝ)
    (hgood : equilibriumToSuspension (future, past) ∈
      {p : (ℤ → ℝ) × ℝ | p ∈ suspensionCarrier ∧ suspensionGoodGapPath p.1}) :
    ∀ n, 0 < past (n + 1) := by
  intro n
  simpa [equilibriumToSuspension, twoSidedGap] using hgood.2.1 (Int.negSucc n)

/-- The exposed future renewal sums of a good equilibrium reconstruction are
nonexplosive. -/
theorem tendsto_arrivalTime_equilibriumToSuspension_future_of_mem_good
    (future past : ℕ → ℝ)
    (hgood : equilibriumToSuspension (future, past) ∈
      {p : (ℤ → ℝ) × ℝ | p ∈ suspensionCarrier ∧ suspensionGoodGapPath p.1}) :
    Tendsto (fun n : ℕ => arrivalTime n future) atTop atTop := by
  have hsuspension := suspensionGoodGapPath_future
    (equilibriumToSuspension (future, past)).1 hgood.2
  have heq := arrivalTime_suspensionFuturePath_equilibriumToSuspension future past
  have htranslated : Tendsto (fun n : ℕ => past 0 + arrivalTime n future)
      atTop atTop := by
    apply hsuspension.congr'
    filter_upwards [] with n
    exact heq n
  apply (tendsto_atTop_add_const_left atTop (-past 0) htranslated).congr'
  filter_upwards [] with n
  ring

/-- The exposed backward renewal sums of a good equilibrium reconstruction are
nonexplosive. -/
theorem tendsto_arrivalTime_equilibriumToSuspension_past_of_mem_good
    (future past : ℕ → ℝ)
    (hgood : equilibriumToSuspension (future, past) ∈
      {p : (ℤ → ℝ) × ℝ | p ∈ suspensionCarrier ∧ suspensionGoodGapPath p.1}) :
    Tendsto (fun n : ℕ => arrivalTime n past) atTop atTop := by
  have hsuspension := suspensionGoodGapPath_past
    (equilibriumToSuspension (future, past)).1 hgood.2
  have htailSub : Tendsto (fun n : ℕ => arrivalTime (n + 1) past - past 0)
      atTop atTop := by
    apply hsuspension.congr'
    filter_upwards [] with n
    exact arrivalTime_suspensionPastPath_equilibriumToSuspension future past n
  have htail : Tendsto (fun n : ℕ => arrivalTime (n + 1) past) atTop atTop := by
    apply (tendsto_atTop_add_const_right atTop (past 0) htailSub).congr'
    filter_upwards [] with n
    ring
  exact (tendsto_add_atTop_iff_nat 1).mp (by
    simpa [Nat.succ_eq_add_one] using htail)

end

end AppliedModelingLib.Probability.PoissonProcess
