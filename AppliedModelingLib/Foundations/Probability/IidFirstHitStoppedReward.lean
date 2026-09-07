import AppliedModelingLib.Foundations.Probability.IidFirstHitCapped

/-!
# Integrable rewards through an IID first hit

This module passes from bounded IID first-hit rewards to an unbounded stopped
sum.  Positive hit probability gives a geometric continuation tail, whose
summability supplies the required interchange of the integral and infinite
sum.  The reward at the terminal hit may depend on the hit coordinate itself.
-/

namespace AppliedModelingLib.Probability.IIDStream

open MeasureTheory ProbabilityTheory

noncomputable section

variable {α : Type*} [MeasurableSpace α]

/-- The event that an IID first-hit reward has not stopped before coordinate
`n`.  It is represented by the continuation event of the capped first-hit
index at the same cap, so it is visibly prefix measurable. -/
def firstHitContinuationEvent
    (hit : Set α) (hhit : MeasurableSet hit) (n : Nat) : Set (Nat -> α) :=
  (firstHitCappedStoppingIndex hit hhit n).continuationEvent n

/-- The reward sum through the first IID hit.  On the null no-hit event it is
the infinite continuation sum; integrability below is derived from the
geometric tail rather than imposed by this definition. -/
noncomputable def firstHitStoppedReward
    (hit : Set α) (hhit : MeasurableSet hit) (reward : α -> Real) :
    (Nat -> α) -> Real := fun omega =>
  ∑' n, (firstHitContinuationEvent hit hhit n).indicator
    (fun omega => reward (coordinate n omega)) omega

/-- A positive-probability IID hit gives the exact geometric probability that
the stopped reward still includes coordinate `n`. -/
theorem measureReal_firstHitContinuationEvent
    (mu : Measure α) [IsProbabilityMeasure mu]
    (hit : Set α) (hhit : MeasurableSet hit) (n : Nat) :
    (measure mu).real (firstHitContinuationEvent hit hhit n) =
      (mu hitᶜ).toReal ^ n := by
  change (measure mu ((firstHitCappedStoppingIndex hit hhit n).continuationEvent n)).toReal = _
  rw [measure_continuationEvent_firstHitCappedStoppingIndex mu hit hhit n n,
    if_pos le_rfl]
  exact ENNReal.toReal_pow (mu hitᶜ) n

/-- The geometric continuation multiplier of a positive-probability IID first
hit is the reciprocal hit probability. -/
theorem tsum_firstHitContinuation_eq_inv_measureReal
    (mu : Measure α) [IsProbabilityMeasure mu]
    (hit : Set α) (hhit : MeasurableSet hit) (hpos : 0 < mu hit) :
    (∑' n : Nat, (mu hitᶜ).toReal ^ n) = ((mu hit).toReal)⁻¹ := by
  rw [tsum_geometric_of_lt_one ENNReal.toReal_nonneg
    (measureReal_compl_lt_one_of_pos mu hit hhit hpos)]
  have hcompl : (mu hitᶜ).toReal = 1 - (mu hit).toReal := by
    change mu.real hitᶜ = _
    rw [MeasureTheory.measureReal_compl hhit, probReal_univ]
    rfl
  rw [hcompl]
  ring

/-- The continuation/reward factorization also includes coordinate zero. -/
theorem PrefixStoppingIndex.integral_continuationEvent_indicator_mul_coordinate
    (mu : Measure α) [IsProbabilityMeasure mu]
    (tau : PrefixStoppingIndex (α := α)) (n : Nat)
    (reward : α -> Real) (hreward : Integrable reward mu) :
    (∫ omega, (tau.continuationEvent n).indicator (fun _ => (1 : Real)) omega *
        reward (coordinate n omega) ∂measure mu) =
      (measure mu).real (tau.continuationEvent n) * ∫ x, reward x ∂mu := by
  letI : IsProbabilityMeasure (measure mu) := by
    dsimp [measure]
    infer_instance
  cases n with
  | zero =>
      rw [tau.continuationEvent_zero]
      calc
        (∫ omega, Set.univ.indicator (fun _ => (1 : Real)) omega *
            reward (coordinate 0 omega) ∂measure mu) =
            ∫ omega, reward (coordinate 0 omega) ∂measure mu := by simp
        _ = ∫ x, reward x ∂mu :=
          (coordinate_hasLaw mu 0).integral_comp hreward.aestronglyMeasurable
        _ = (measure mu).real Set.univ * ∫ x, reward x ∂mu := by
          rw [MeasureTheory.measureReal_def, measure_univ]
          simp
  | succ n =>
      exact integral_continuationEvent_succ_indicator_mul_coordinate
        mu tau n reward hreward

/-- An absolutely summable family in `L¹` has an integrable pointwise series.
The conclusion concerns the literal `tsum`; the proof first controls the
nonnegative pointwise norm series by Tonelli, then identifies the almost
everywhere limit of its finite partial sums. -/
theorem integrable_tsum_of_summable_integral_norm
    {β : Type*} [MeasurableSpace β] {mu : Measure β}
    (F : Nat -> β -> Real) (hF : ∀ n, Integrable (F n) mu)
    (hsum : Summable fun n => ∫ x, ‖F n x‖ ∂mu) :
    Integrable (fun x => ∑' n, F n x) mu := by
  have hnorm_lintegral (n : Nat) :
      (∫⁻ x, ‖F n x‖ₑ ∂mu) = ENNReal.ofReal (∫ x, ‖F n x‖ ∂mu) := by
    dsimp [enorm]
    rw [lintegral_coe_eq_integral _ (hF n).norm]
    have hcoe : (fun x : β => (↑‖F n x‖₊ : Real)) = fun x => ‖F n x‖ := by
      funext x
      simp
    rw [hcoe]
    simp only [Real.norm_eq_abs]
  have hsum_enorm_lintegral :
      (∫⁻ x, ∑' n, ‖F n x‖ₑ ∂mu) < ⊤ := by
    rw [lintegral_tsum fun n => (hF n).aestronglyMeasurable.enorm]
    rw [show (fun n => ∫⁻ x, ‖F n x‖ₑ ∂mu) =
        fun n => ENNReal.ofReal (∫ x, ‖F n x‖ ∂mu) by
      funext n
      exact hnorm_lintegral n]
    rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun n => integral_nonneg fun _ => norm_nonneg _) hsum]
    exact ENNReal.ofReal_lt_top
  have hpoint_abs : ∀ᵐ x ∂mu, Summable fun n => ‖F n x‖ := by
    refine (ae_lt_top'
      (AEMeasurable.ennreal_tsum fun n => (hF n).aestronglyMeasurable.enorm)
      hsum_enorm_lintegral.ne).mono fun x hx => ?_
    have hx' : (∑' n, (↑‖F n x‖₊ : ENNReal)) ≠ ⊤ := by
      simpa only [enorm_eq_nnnorm] using hx.ne
    have hxnorm : Summable fun n => (↑‖F n x‖₊ : Real) :=
      NNReal.summable_coe.mpr
        (ENNReal.tsum_coe_ne_top_iff_summable.mp hx')
    simpa using hxnorm
  have hpoint : ∀ᵐ x ∂mu, Summable fun n => F n x := by
    exact hpoint_abs.mono fun _ hx => hx.of_norm
  let partialSum : Nat -> β -> Real := fun k x => ∑ n ∈ Finset.range k, F n x
  have hpartial_meas (k : Nat) : AEStronglyMeasurable (partialSum k) mu := by
    exact (Finset.range k).aestronglyMeasurable_fun_sum fun n _ =>
      (hF n).aestronglyMeasurable
  have hpartial_limit : ∀ᵐ x ∂mu, ∃ l,
      Filter.Tendsto (fun k => partialSum k x) Filter.atTop (nhds l) := by
    refine hpoint.mono fun x hx => ⟨∑' n, F n x, ?_⟩
    simpa [partialSum] using hx.hasSum.tendsto_sum_nat
  obtain ⟨limit, hlimit_meas, hlimit_tendsto⟩ :=
    exists_stronglyMeasurable_limit_of_tendsto_ae hpartial_meas hpartial_limit
  have hlimit_eq : limit =ᵐ[mu] fun x => ∑' n, F n x := by
    filter_upwards [hlimit_tendsto, hpoint] with x hlimit hx
    exact tendsto_nhds_unique hlimit (by simpa [partialSum] using hx.hasSum.tendsto_sum_nat)
  have hsum_meas : AEStronglyMeasurable (fun x => ∑' n, F n x) mu :=
    hlimit_meas.aestronglyMeasurable.congr hlimit_eq
  refine ⟨hsum_meas, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  refine lt_of_le_of_lt ?_ hsum_enorm_lintegral
  refine lintegral_mono_ae ?_
  filter_upwards [hpoint_abs] with x hx
  calc
    ENNReal.ofReal ‖∑' n, F n x‖ ≤ ENNReal.ofReal (∑' n, ‖F n x‖) :=
      ENNReal.ofReal_le_ofReal (norm_tsum_le_tsum_norm hx)
    _ = ∑' n, ENNReal.ofReal ‖F n x‖ :=
      ENNReal.ofReal_tsum_of_nonneg (fun n => norm_nonneg _) hx
    _ = ∑' n, ‖F n x‖ₑ := by simp only [ofReal_norm_eq_enorm]

/-- The reward sum through a positive-probability IID first hit is integrable.
The terminal reward may depend on whether that terminal coordinate hits, so
the proof uses prefix continuation events rather than reward/hit independence. -/
theorem integrable_firstHitStoppedReward
    (mu : Measure α) [IsProbabilityMeasure mu]
    (hit : Set α) (hhit : MeasurableSet hit) (hpos : 0 < mu hit)
    (reward : α -> Real) (hintegrable : Integrable reward mu) :
    Integrable (firstHitStoppedReward hit hhit reward) (measure mu) := by
  let q : Real := (mu hitᶜ).toReal
  let F : Nat -> (Nat -> α) -> Real := fun n =>
    (firstHitContinuationEvent hit hhit n).indicator
      (fun omega => reward (coordinate n omega))
  have hq : Summable fun n : Nat => q ^ n := by
    apply summable_geometric_of_lt_one ENNReal.toReal_nonneg
    exact measureReal_compl_lt_one_of_pos mu hit hhit hpos
  have hF_integrable (n : Nat) : Integrable (F n) (measure mu) := by
    let τ := firstHitCappedStoppingIndex hit hhit n
    have h := PrefixStoppingIndex.integrable_continuationEvent_indicator_mul_coordinate
      mu τ n reward hintegrable
    simpa [F, firstHitContinuationEvent, τ, Set.indicator] using h
  have hF_norm_integral (n : Nat) :
      (∫ omega, ‖F n omega‖ ∂measure mu) = q ^ n * ∫ x, ‖reward x‖ ∂mu := by
    let τ := firstHitCappedStoppingIndex hit hhit n
    have h := PrefixStoppingIndex.integral_continuationEvent_indicator_mul_coordinate
      mu τ n (fun x => ‖reward x‖) hintegrable.norm
    have hnorm : (fun omega => ‖F n omega‖) =
        fun omega => (τ.continuationEvent n).indicator (fun _ => (1 : Real)) omega *
          ‖reward (coordinate n omega)‖ := by
      funext omega
      by_cases hmem : omega ∈ τ.continuationEvent n <;>
        simp [F, firstHitContinuationEvent, τ, Set.indicator, hmem]
    calc
      (∫ omega, ‖F n omega‖ ∂measure mu) =
          ∫ omega, (τ.continuationEvent n).indicator (fun _ => (1 : Real)) omega *
            ‖reward (coordinate n omega)‖ ∂measure mu := by rw [hnorm]
      _ = (measure mu).real (τ.continuationEvent n) * ∫ x, ‖reward x‖ ∂mu := h
      _ = q ^ n * ∫ x, ‖reward x‖ ∂mu := by
        change (measure mu).real (firstHitContinuationEvent hit hhit n) *
          ∫ x, ‖reward x‖ ∂mu = _
        rw [measureReal_firstHitContinuationEvent mu hit hhit n]
  have hsum_norm : Summable fun n : Nat => ∫ omega, ‖F n omega‖ ∂measure mu := by
    exact (hq.mul_right (∫ x, ‖reward x‖ ∂mu)).congr fun n =>
      (hF_norm_integral n).symm
  simpa [firstHitStoppedReward, F] using
    (integrable_tsum_of_summable_integral_norm F hF_integrable hsum_norm)

/-- The complete reward through a positive-probability IID first hit is
integrable, with its exact Wald/geometric expectation. -/
theorem integral_firstHitStoppedReward
    (mu : Measure α) [IsProbabilityMeasure mu]
    (hit : Set α) (hhit : MeasurableSet hit) (hpos : 0 < mu hit)
    (reward : α -> Real) (hintegrable : Integrable reward mu) :
    (∫ omega, firstHitStoppedReward hit hhit reward omega ∂measure mu) =
      (∑' n : Nat, (mu hitᶜ).toReal ^ n) * ∫ x, reward x ∂mu := by
  let q : Real := (mu hitᶜ).toReal
  let F : Nat -> (Nat -> α) -> Real := fun n =>
    (firstHitContinuationEvent hit hhit n).indicator
      (fun omega => reward (coordinate n omega))
  have hq : Summable fun n : Nat => q ^ n := by
    apply summable_geometric_of_lt_one ENNReal.toReal_nonneg
    exact measureReal_compl_lt_one_of_pos mu hit hhit hpos
  have hF_integrable (n : Nat) : Integrable (F n) (measure mu) := by
    let τ := firstHitCappedStoppingIndex hit hhit n
    have h := PrefixStoppingIndex.integrable_continuationEvent_indicator_mul_coordinate
      mu τ n reward hintegrable
    simpa [F, firstHitContinuationEvent, τ, Set.indicator] using h
  have hF_integral (n : Nat) :
      (∫ omega, F n omega ∂measure mu) = q ^ n * ∫ x, reward x ∂mu := by
    let τ := firstHitCappedStoppingIndex hit hhit n
    have h := PrefixStoppingIndex.integral_continuationEvent_indicator_mul_coordinate
      mu τ n reward hintegrable
    calc
      (∫ omega, F n omega ∂measure mu) =
          (measure mu).real (τ.continuationEvent n) * ∫ x, reward x ∂mu := by
            simpa [F, firstHitContinuationEvent, τ, Set.indicator] using h
      _ = q ^ n * ∫ x, reward x ∂mu := by
        change (measure mu).real (firstHitContinuationEvent hit hhit n) *
          ∫ x, reward x ∂mu = _
        rw [measureReal_firstHitContinuationEvent mu hit hhit n]
  have hF_norm_integral (n : Nat) :
      (∫ omega, ‖F n omega‖ ∂measure mu) = q ^ n * ∫ x, ‖reward x‖ ∂mu := by
    let τ := firstHitCappedStoppingIndex hit hhit n
    have h := PrefixStoppingIndex.integral_continuationEvent_indicator_mul_coordinate
      mu τ n (fun x => ‖reward x‖) hintegrable.norm
    have hnorm : (fun omega => ‖F n omega‖) =
        fun omega => (τ.continuationEvent n).indicator (fun _ => (1 : Real)) omega *
          ‖reward (coordinate n omega)‖ := by
      funext omega
      by_cases hmem : omega ∈ τ.continuationEvent n <;>
        simp [F, firstHitContinuationEvent, τ, Set.indicator, hmem]
    calc
      (∫ omega, ‖F n omega‖ ∂measure mu) =
          ∫ omega, (τ.continuationEvent n).indicator (fun _ => (1 : Real)) omega *
            ‖reward (coordinate n omega)‖ ∂measure mu := by rw [hnorm]
      _ = (measure mu).real (τ.continuationEvent n) * ∫ x, ‖reward x‖ ∂mu := h
      _ = q ^ n * ∫ x, ‖reward x‖ ∂mu := by
        change (measure mu).real (firstHitContinuationEvent hit hhit n) *
          ∫ x, ‖reward x‖ ∂mu = _
        rw [measureReal_firstHitContinuationEvent mu hit hhit n]
  have hsum_norm : Summable fun n : Nat => ∫ omega, ‖F n omega‖ ∂measure mu := by
    exact (hq.mul_right (∫ x, ‖reward x‖ ∂mu)).congr fun n =>
      (hF_norm_integral n).symm
  calc
    (∫ omega, firstHitStoppedReward hit hhit reward omega ∂measure mu) =
        ∫ omega, ∑' n, F n omega ∂measure mu := by rfl
    _ = ∑' n, ∫ omega, F n omega ∂measure mu := by
      exact (MeasureTheory.integral_tsum_of_summable_integral_norm
        hF_integrable hsum_norm).symm
    _ = ∑' n : Nat, q ^ n * ∫ x, reward x ∂mu := by
      exact tsum_congr hF_integral
    _ = (∑' n : Nat, q ^ n) * ∫ x, reward x ∂mu := by
      rw [tsum_mul_right]
    _ = (∑' n : Nat, (mu hitᶜ).toReal ^ n) * ∫ x, reward x ∂mu := by rfl

end

end AppliedModelingLib.Probability.IIDStream
