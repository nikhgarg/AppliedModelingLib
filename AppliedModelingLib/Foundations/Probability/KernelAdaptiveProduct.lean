import AppliedModelingLib.Foundations.Probability.KernelAdaptiveSuccessTail

/-!
# Products of adaptive kernel multipliers

This module gives the reusable Ionescu--Tulcea supermartingale induction for
an arbitrary nonnegative, bounded, history-dependent one-round multiplier.
If every conditional multiplier has expectation at most one, the product
through every finite prefix also has expectation at most one.  Independence
between rounds is neither stated nor used.
-/

namespace AppliedModelingLib

open MeasureTheory ProbabilityTheory Preorder

noncomputable section

/-- Product of arbitrary adaptive round multipliers on a finite prefix. -/
noncomputable def kernelAdaptivePrefixProduct
    {Outcome : Type*}
    (multiplier : ∀ round, KernelAdaptiveRoundPair Outcome round → ℝ) :
    (rounds : ℕ) → ((i : Finset.Iic rounds) → Outcome) → ℝ
  | 0, _ => 1
  | rounds + 1, history =>
      kernelAdaptivePrefixProduct multiplier rounds
          (frestrictLe₂ (π := fun _ : ℕ ↦ Outcome) rounds.le_succ history) *
        multiplier rounds
          (frestrictLe₂ (π := fun _ : ℕ ↦ Outcome) rounds.le_succ history,
            history ⟨rounds + 1, Finset.mem_Iic.mpr le_rfl⟩)

/-- Infinite-trajectory view of the product through `rounds` rounds. -/
def kernelAdaptiveProduct
    {Outcome : Type*}
    (multiplier : ∀ round, KernelAdaptiveRoundPair Outcome round → ℝ)
    (rounds : ℕ) (trace : ℕ → Outcome) : ℝ :=
  kernelAdaptivePrefixProduct multiplier rounds (frestrictLe rounds trace)

theorem kernelAdaptiveProduct_succ
    {Outcome : Type*}
    (multiplier : ∀ round, KernelAdaptiveRoundPair Outcome round → ℝ)
    (rounds : ℕ) (trace : ℕ → Outcome) :
    kernelAdaptiveProduct multiplier (rounds + 1) trace =
      kernelAdaptiveProduct multiplier rounds trace *
        multiplier rounds (kernelAdaptiveRoundPair rounds trace) := by
  rfl

/-- Measurable equivalence that appends a fresh outcome to a finite prefix. -/
def kernelAdaptiveAppendEquiv
    {Outcome : Type*} [MeasurableSpace Outcome] (round : ℕ) :
    KernelAdaptiveRoundPair Outcome round ≃ᵐ
      ((i : Finset.Iic (round + 1)) → Outcome) :=
  (MeasurableEquiv.prodCongr
      (MeasurableEquiv.refl ((i : Finset.Iic round) → Outcome))
      (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ Outcome) round)).trans
    (MeasurableEquiv.IicProdIoc
      (X := fun _ : ℕ ↦ Outcome) round.le_succ)

/-- Appending the history/fresh-coordinate pair read from an infinite trace
recovers its successor prefix. -/
theorem kernelAdaptiveAppendEquiv_apply_roundPair
    {Outcome : Type*} [MeasurableSpace Outcome]
    (round : ℕ) (trace : ℕ → Outcome) :
    kernelAdaptiveAppendEquiv round (kernelAdaptiveRoundPair round trace) =
      frestrictLe (round + 1) trace := by
  funext index
  by_cases hindex : index.1 ≤ round
  · simp [kernelAdaptiveAppendEquiv, MeasurableEquiv.IicProdIoc,
      MeasurableEquiv.prodCongr, Equiv.prodCongr, MeasurableEquiv.refl,
      kernelAdaptiveRoundPair, hindex, frestrictLe_apply]
  · have hupper : index.1 ≤ round + 1 := Finset.mem_Iic.mp index.2
    have hlast : index.1 = round + 1 := by omega
    have hindexEq : index =
        ⟨round + 1, Finset.mem_Iic.mpr le_rfl⟩ := Subtype.ext hlast
    rw [hindexEq]
    simp [kernelAdaptiveAppendEquiv, MeasurableEquiv.IicProdIoc,
      MeasurableEquiv.prodCongr, Equiv.prodCongr, MeasurableEquiv.refl,
      MeasurableEquiv.piSingleton,
      kernelAdaptiveRoundPair, frestrictLe_apply]

/-- The successor prefix law is the previous prefix law composed with the
fresh-output kernel and then transported through prefix append. -/
theorem map_frestrictLe_succ_trajMeasure_eq_map_compProd_append
    {Outcome : Type*} [MeasurableSpace Outcome]
    (initialLaw : Measure Outcome) [IsProbabilityMeasure initialLaw]
    (kernel : ∀ round : ℕ,
      Kernel ((i : Finset.Iic round) → Outcome) Outcome)
    [∀ round, IsMarkovKernel (kernel round)]
    (round : ℕ) :
    (Kernel.trajMeasure initialLaw kernel).map
        (frestrictLe (π := fun _ : ℕ ↦ Outcome) (round + 1)) =
      ((Kernel.trajMeasure initialLaw kernel).map
          (frestrictLe (π := fun _ : ℕ ↦ Outcome) round) ⊗ₘ
        kernel round).map
          (kernelAdaptiveAppendEquiv (Outcome := Outcome) round) := by
  let trajectory : Measure (ℕ → Outcome) :=
    Kernel.trajMeasure initialLaw kernel
  let pairMap : (ℕ → Outcome) → KernelAdaptiveRoundPair Outcome round :=
    kernelAdaptiveRoundPair round
  have hpair :
      trajectory.map (frestrictLe (π := fun _ : ℕ ↦ Outcome) round) ⊗ₘ
          kernel round =
        trajectory.map pairMap := by
    dsimp [trajectory, pairMap]
    exact Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
  calc
    trajectory.map
        (frestrictLe (π := fun _ : ℕ ↦ Outcome) (round + 1)) =
        trajectory.map (fun trace ↦
          kernelAdaptiveAppendEquiv (Outcome := Outcome) round (pairMap trace)) := by
      congr 1
      funext trace
      exact (kernelAdaptiveAppendEquiv_apply_roundPair
        (Outcome := Outcome) round trace).symm
    _ = (trajectory.map pairMap).map
        (kernelAdaptiveAppendEquiv (Outcome := Outcome) round) := by
      exact (Measure.map_map
        (kernelAdaptiveAppendEquiv (Outcome := Outcome) round).measurable
        (measurable_kernelAdaptiveRoundPair round)).symm
    _ = (trajectory.map
        (frestrictLe (π := fun _ : ℕ ↦ Outcome) round) ⊗ₘ
        kernel round).map
        (kernelAdaptiveAppendEquiv (Outcome := Outcome) round) := by rw [hpair]

/-- The zero prefix contains only the common initial coordinate and is
independent of all transition kernels. -/
theorem map_frestrictLe_zero_trajMeasure
    {Outcome : Type*} [MeasurableSpace Outcome]
    (initialLaw : Measure Outcome) [IsProbabilityMeasure initialLaw]
    (kernel : ∀ round : ℕ,
      Kernel ((i : Finset.Iic round) → Outcome) Outcome)
    [∀ round, IsMarkovKernel (kernel round)] :
    (Kernel.trajMeasure initialLaw kernel).map
        (frestrictLe (π := fun _ : ℕ ↦ Outcome) 0) =
      initialLaw.map
        (MeasurableEquiv.piUnique
          ((fun _ : Finset.Iic 0 ↦ Outcome))).symm := by
  rw [Kernel.trajMeasure,
    Measure.map_comp _ _ (measurable_frestrictLe 0),
    Kernel.traj_map_frestrictLe_of_le (a := 0) (b := 0) le_rfl]
  rw [Measure.deterministic_comp_eq_map]
  have hrestrict :
      frestrictLe₂ (π := fun _ : ℕ ↦ Outcome) (le_rfl : 0 ≤ 0) = id := by
    funext history
    funext index
    rfl
  rw [hrestrict, Measure.map_id]

/-- Prefix products are measurable when every round multiplier is. -/
theorem measurable_kernelAdaptivePrefixProduct
    {Outcome : Type*} [MeasurableSpace Outcome]
    (multiplier : ∀ round, KernelAdaptiveRoundPair Outcome round → ℝ)
    (hmeasurable : ∀ round, Measurable (multiplier round)) :
    ∀ rounds, Measurable (kernelAdaptivePrefixProduct multiplier rounds) := by
  intro rounds
  induction rounds with
  | zero => exact measurable_const
  | succ rounds ih =>
      change Measurable (fun history ↦
        kernelAdaptivePrefixProduct multiplier rounds
            (frestrictLe₂ (π := fun _ : ℕ ↦ Outcome) rounds.le_succ history) *
          multiplier rounds
            (frestrictLe₂ (π := fun _ : ℕ ↦ Outcome) rounds.le_succ history,
              history ⟨rounds + 1, Finset.mem_Iic.mpr le_rfl⟩))
      exact (ih.comp (measurable_frestrictLe₂
          (X := fun _ : ℕ ↦ Outcome) rounds.le_succ)).mul
        ((hmeasurable rounds).comp
          (measurable_kernelAdaptivePrefixLastPair rounds))

theorem measurable_kernelAdaptiveProduct
    {Outcome : Type*} [MeasurableSpace Outcome]
    (multiplier : ∀ round, KernelAdaptiveRoundPair Outcome round → ℝ)
    (hmeasurable : ∀ round, Measurable (multiplier round))
    (rounds : ℕ) :
    Measurable (kernelAdaptiveProduct multiplier rounds) :=
  (measurable_kernelAdaptivePrefixProduct multiplier hmeasurable rounds).comp
    (measurable_frestrictLe rounds)

/-- Nonnegativity propagates through finite prefix products. -/
theorem kernelAdaptivePrefixProduct_nonneg
    {Outcome : Type*}
    (multiplier : ∀ round, KernelAdaptiveRoundPair Outcome round → ℝ)
    (hnonneg : ∀ round pair, 0 ≤ multiplier round pair) :
    ∀ rounds (history : (i : Finset.Iic rounds) → Outcome),
      0 ≤ kernelAdaptivePrefixProduct multiplier rounds history := by
  intro rounds
  induction rounds with
  | zero => intro history; simp [kernelAdaptivePrefixProduct]
  | succ rounds ih =>
      intro history
      exact mul_nonneg (ih _) (hnonneg rounds _)

/-- A common deterministic one-round bound gives a power bound on the prefix
product. -/
theorem kernelAdaptivePrefixProduct_le_pow
    {Outcome : Type*}
    (multiplier : ∀ round, KernelAdaptiveRoundPair Outcome round → ℝ)
    (bound : ℝ) (hboundNonneg : 0 ≤ bound)
    (hnonneg : ∀ round pair, 0 ≤ multiplier round pair)
    (hbound : ∀ round pair, multiplier round pair ≤ bound) :
    ∀ rounds (history : (i : Finset.Iic rounds) → Outcome),
      kernelAdaptivePrefixProduct multiplier rounds history ≤ bound ^ rounds := by
  intro rounds
  induction rounds with
  | zero => intro history; simp [kernelAdaptivePrefixProduct]
  | succ rounds ih =>
      intro history
      change kernelAdaptivePrefixProduct multiplier rounds _ *
          multiplier rounds _ ≤ _
      rw [pow_succ]
      exact mul_le_mul (ih _) (hbound rounds _)
        (hnonneg rounds _) (pow_nonneg hboundNonneg _)

/-- A bounded measurable adaptive prefix product is integrable under every
probability law. -/
theorem integrable_kernelAdaptiveProduct
    {Outcome : Type*} [MeasurableSpace Outcome]
    (law : Measure (ℕ → Outcome)) [IsProbabilityMeasure law]
    (multiplier : ∀ round, KernelAdaptiveRoundPair Outcome round → ℝ)
    (hmeasurable : ∀ round, Measurable (multiplier round))
    (bound : ℝ) (hboundNonneg : 0 ≤ bound)
    (hnonneg : ∀ round pair, 0 ≤ multiplier round pair)
    (hbound : ∀ round pair, multiplier round pair ≤ bound)
    (rounds : ℕ) :
    Integrable (kernelAdaptiveProduct multiplier rounds) law := by
  apply Integrable.of_bound
    (measurable_kernelAdaptiveProduct multiplier hmeasurable rounds).aestronglyMeasurable
    (bound ^ rounds)
  filter_upwards [] with trace
  have hproductNonneg : 0 ≤ kernelAdaptiveProduct multiplier rounds trace :=
    kernelAdaptivePrefixProduct_nonneg multiplier hnonneg rounds _
  rw [Real.norm_eq_abs, abs_of_nonneg hproductNonneg]
  exact kernelAdaptivePrefixProduct_le_pow multiplier bound hboundNonneg
    hnonneg hbound rounds _

/-- General adaptive-product supermartingale theorem.  The round law may
depend measurably on the entire public prefix. -/
theorem integral_kernelAdaptiveProduct_le_one
    {Outcome : Type*} [MeasurableSpace Outcome]
    (initialLaw : Measure Outcome) [IsProbabilityMeasure initialLaw]
    (kernel : ∀ round,
      Kernel ((i : Finset.Iic round) → Outcome) Outcome)
    [∀ round, IsMarkovKernel (kernel round)]
    (multiplier : ∀ round, KernelAdaptiveRoundPair Outcome round → ℝ)
    (hmeasurable : ∀ round, Measurable (multiplier round))
    (bound : ℝ) (hboundNonneg : 0 ≤ bound)
    (hnonneg : ∀ round pair, 0 ≤ multiplier round pair)
    (hbound : ∀ round pair, multiplier round pair ≤ bound)
    (hconditional : ∀ round history,
      ∫ next, multiplier round (history, next) ∂kernel round history ≤ 1) :
    ∀ rounds,
      ∫ trace, kernelAdaptiveProduct multiplier rounds trace
          ∂Kernel.trajMeasure initialLaw kernel ≤ 1 := by
  intro rounds
  induction rounds with
  | zero => simp [kernelAdaptiveProduct, kernelAdaptivePrefixProduct]
  | succ rounds ih =>
      let trajectory : Measure (ℕ → Outcome) :=
        Kernel.trajMeasure initialLaw kernel
      let historyMeasure : Measure ((i : Finset.Iic rounds) → Outcome) :=
        trajectory.map (frestrictLe rounds)
      let pairMap : (ℕ → Outcome) → KernelAdaptiveRoundPair Outcome rounds :=
        kernelAdaptiveRoundPair rounds
      let integrand : KernelAdaptiveRoundPair Outcome rounds → ℝ :=
        fun pair ↦
          kernelAdaptivePrefixProduct multiplier rounds pair.1 *
            multiplier rounds pair
      letI : IsProbabilityMeasure trajectory := by
        dsimp [trajectory]
        infer_instance
      letI : IsProbabilityMeasure historyMeasure := by
        dsimp [historyMeasure]
        exact Measure.isProbabilityMeasure_map
          (measurable_frestrictLe rounds).aemeasurable
      have hintegrandMeasurable : Measurable integrand := by
        dsimp [integrand]
        exact ((measurable_kernelAdaptivePrefixProduct multiplier hmeasurable rounds).comp
          measurable_fst).mul (hmeasurable rounds)
      have hintegrandNonneg : ∀ pair, 0 ≤ integrand pair := by
        intro pair
        exact mul_nonneg
          (kernelAdaptivePrefixProduct_nonneg multiplier hnonneg rounds pair.1)
          (hnonneg rounds pair)
      have hintegrandBound : ∀ pair, integrand pair ≤ bound ^ (rounds + 1) := by
        intro pair
        rw [pow_succ]
        exact mul_le_mul
          (kernelAdaptivePrefixProduct_le_pow multiplier bound hboundNonneg
            hnonneg hbound rounds pair.1)
          (hbound rounds pair) (hnonneg rounds pair)
          (pow_nonneg hboundNonneg _)
      have hintegrand : Integrable integrand
          (historyMeasure ⊗ₘ kernel rounds) := by
        apply Integrable.of_bound hintegrandMeasurable.aestronglyMeasurable
          (bound ^ (rounds + 1))
        filter_upwards [] with pair
        rw [Real.norm_eq_abs, abs_of_nonneg (hintegrandNonneg pair)]
        exact hintegrandBound pair
      have hpairMap : Measurable pairMap :=
        measurable_kernelAdaptiveRoundPair rounds
      have hjoint : trajectory.map pairMap =
          historyMeasure ⊗ₘ kernel rounds := by
        dsimp [trajectory, historyMeasure, pairMap]
        exact Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure.symm
      have hprefixIntegrable : Integrable
          (kernelAdaptivePrefixProduct multiplier rounds) historyMeasure := by
        apply Integrable.of_bound
          (measurable_kernelAdaptivePrefixProduct multiplier hmeasurable rounds).aestronglyMeasurable
          (bound ^ rounds)
        filter_upwards [] with history
        rw [Real.norm_eq_abs, abs_of_nonneg
          (kernelAdaptivePrefixProduct_nonneg multiplier hnonneg rounds history)]
        exact kernelAdaptivePrefixProduct_le_pow multiplier bound hboundNonneg
          hnonneg hbound rounds history
      calc
        (∫ trace, kernelAdaptiveProduct multiplier (rounds + 1) trace ∂trajectory) =
            ∫ trace, integrand (pairMap trace) ∂trajectory := by
          apply integral_congr_ae
          filter_upwards [] with trace
          exact kernelAdaptiveProduct_succ multiplier rounds trace
        _ = ∫ pair, integrand pair ∂trajectory.map pairMap := by
          exact (integral_map hpairMap.aemeasurable
            hintegrandMeasurable.aestronglyMeasurable).symm
        _ = ∫ pair, integrand pair ∂(historyMeasure ⊗ₘ kernel rounds) := by
          rw [hjoint]
        _ = ∫ history, ∫ next, integrand (history, next)
              ∂kernel rounds history ∂historyMeasure := by
          exact Measure.integral_compProd hintegrand
        _ ≤ ∫ history,
              kernelAdaptivePrefixProduct multiplier rounds history
              ∂historyMeasure := by
          apply integral_mono_ae hintegrand.integral_compProd hprefixIntegrable
          filter_upwards [] with history
          dsimp [integrand]
          rw [integral_const_mul]
          exact mul_le_of_le_one_right
            (kernelAdaptivePrefixProduct_nonneg multiplier hnonneg rounds history)
            (hconditional rounds history)
        _ = ∫ trace, kernelAdaptiveProduct multiplier rounds trace
              ∂trajectory := by
          exact integral_map (measurable_frestrictLe rounds).aemeasurable
            (measurable_kernelAdaptivePrefixProduct multiplier hmeasurable rounds).aestronglyMeasurable
        _ ≤ 1 := ih

end

end AppliedModelingLib
