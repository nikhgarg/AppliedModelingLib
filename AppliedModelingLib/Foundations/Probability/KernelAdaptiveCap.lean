import AppliedModelingLib.Foundations.Probability.KernelAdaptiveProduct

/-!
# Deterministic release caps for adaptive kernels

This module turns a public cap on distinguished (non-bottom) outputs into an
adaptive Markov kernel.  Before the cap is reached it uses an arbitrary base
kernel; afterwards it emits the bottom symbol deterministically.  The induced
Ionescu--Tulcea trajectory therefore respects the cap almost surely.

The construction is independent of differential privacy.  It is intended for
sparse-release algorithms whose public transcript itself determines whether
the release budget has been exhausted.
-/

namespace AppliedModelingLib

open MeasureTheory ProbabilityTheory Set Preorder

noncomputable section

/-- Natural-valued indicator of an output distinct from `bottom`. -/
noncomputable def nonBottomNatIndicator
    {Outcome : Type*} (bottom outcome : Outcome) : ℕ := by
  classical
  exact if outcome = bottom then 0 else 1

theorem measurable_nonBottomNatIndicator
    {Outcome : Type*} [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome] (bottom : Outcome) :
    Measurable (nonBottomNatIndicator bottom) := by
  classical
  unfold nonBottomNatIndicator
  exact Measurable.ite
    (measurableSet_singleton bottom) measurable_const measurable_const

/-- Number of non-bottom outputs in a finite adaptive prefix.  Coordinate zero
is the common initial coordinate, and the successor clause counts the fresh
output at coordinate `round + 1`. -/
noncomputable def kernelAdaptivePrefixNonBottomCount
    {Outcome : Type*} (bottom : Outcome) :
    (rounds : ℕ) → ((i : Finset.Iic rounds) → Outcome) → ℕ
  | 0, _ => 0
  | rounds + 1, history =>
      kernelAdaptivePrefixNonBottomCount bottom rounds
          (frestrictLe₂ (π := fun _ : ℕ ↦ Outcome) rounds.le_succ history) +
        nonBottomNatIndicator bottom
          (history ⟨rounds + 1, Finset.mem_Iic.mpr le_rfl⟩)

/-- Infinite-trajectory view of the finite non-bottom count. -/
noncomputable def kernelAdaptiveNonBottomCount
    {Outcome : Type*} (bottom : Outcome)
    (rounds : ℕ) (trace : ℕ → Outcome) : ℕ :=
  kernelAdaptivePrefixNonBottomCount bottom rounds (frestrictLe rounds trace)

theorem kernelAdaptiveNonBottomCount_succ
    {Outcome : Type*} (bottom : Outcome)
    (rounds : ℕ) (trace : ℕ → Outcome) :
    kernelAdaptiveNonBottomCount bottom (rounds + 1) trace =
      kernelAdaptiveNonBottomCount bottom rounds trace +
        nonBottomNatIndicator bottom (trace (rounds + 1)) := by
  rfl

/-- The finite-prefix count is measurable on a singleton-measurable output
space. -/
theorem measurable_kernelAdaptivePrefixNonBottomCount
    {Outcome : Type*} [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome] (bottom : Outcome) :
    ∀ rounds, Measurable
      (kernelAdaptivePrefixNonBottomCount bottom rounds) := by
  intro rounds
  induction rounds with
  | zero => exact measurable_const
  | succ rounds ih =>
      apply Measurable.add
      · exact ih.comp
          (measurable_frestrictLe₂
            (X := fun _ : ℕ ↦ Outcome) rounds.le_succ)
      · exact (measurable_nonBottomNatIndicator bottom).comp
          (measurable_pi_apply
            (⟨rounds + 1, Finset.mem_Iic.mpr le_rfl⟩ :
              Finset.Iic (rounds + 1)))

theorem measurable_kernelAdaptiveNonBottomCount
    {Outcome : Type*} [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome] (bottom : Outcome) (rounds : ℕ) :
    Measurable (kernelAdaptiveNonBottomCount bottom rounds) :=
  (measurable_kernelAdaptivePrefixNonBottomCount bottom rounds).comp
    (measurable_frestrictLe rounds)

/-- Prefixes on which another non-bottom release is still allowed. -/
def kernelAdaptiveBelowCapSet
    {Outcome : Type*} (bottom : Outcome) (cap round : ℕ) :
    Set ((i : Finset.Iic round) → Outcome) :=
  {history | kernelAdaptivePrefixNonBottomCount bottom round history < cap}

theorem measurableSet_kernelAdaptiveBelowCapSet
    {Outcome : Type*} [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome]
    (bottom : Outcome) (cap round : ℕ) :
    MeasurableSet (kernelAdaptiveBelowCapSet bottom cap round) :=
  measurableSet_lt
    (measurable_kernelAdaptivePrefixNonBottomCount bottom round)
    measurable_const

/-- Cap an adaptive kernel by emitting `bottom` deterministically once the
public prefix already contains `cap` non-bottom outputs. -/
noncomputable def cappedAdaptiveKernel
    {Outcome : Type*} [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome]
    (cap : ℕ) (bottom : Outcome)
    (base : ∀ round : ℕ,
      Kernel ((i : Finset.Iic round) → Outcome) Outcome)
    (round : ℕ) : Kernel ((i : Finset.Iic round) → Outcome) Outcome := by
  classical
  exact Kernel.piecewise
    (measurableSet_kernelAdaptiveBelowCapSet bottom cap round)
    (base round) (Kernel.const _ (Measure.dirac bottom))

instance cappedAdaptiveKernel_isMarkov
    {Outcome : Type*} [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome]
    (cap : ℕ) (bottom : Outcome)
    (base : ∀ round : ℕ,
      Kernel ((i : Finset.Iic round) → Outcome) Outcome)
    [∀ round, IsMarkovKernel (base round)] (round : ℕ) :
    IsMarkovKernel (cappedAdaptiveKernel cap bottom base round) := by
  unfold cappedAdaptiveKernel
  infer_instance

theorem cappedAdaptiveKernel_apply_of_lt
    {Outcome : Type*} [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome]
    (cap : ℕ) (bottom : Outcome)
    (base : ∀ round : ℕ,
      Kernel ((i : Finset.Iic round) → Outcome) Outcome)
    (round : ℕ) (history : (i : Finset.Iic round) → Outcome)
    (hcount : kernelAdaptivePrefixNonBottomCount bottom round history < cap) :
    cappedAdaptiveKernel cap bottom base round history = base round history := by
  classical
  rw [cappedAdaptiveKernel, Kernel.piecewise_apply]
  simp [kernelAdaptiveBelowCapSet, hcount]

theorem cappedAdaptiveKernel_apply_of_not_lt
    {Outcome : Type*} [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome]
    (cap : ℕ) (bottom : Outcome)
    (base : ∀ round : ℕ,
      Kernel ((i : Finset.Iic round) → Outcome) Outcome)
    (round : ℕ) (history : (i : Finset.Iic round) → Outcome)
    (hcount : ¬ kernelAdaptivePrefixNonBottomCount bottom round history < cap) :
    cappedAdaptiveKernel cap bottom base round history = Measure.dirac bottom := by
  classical
  rw [cappedAdaptiveKernel, Kernel.piecewise_apply]
  simp [kernelAdaptiveBelowCapSet, hcount]

/-- Appending a history/outcome pair adds exactly the indicator of a
non-bottom fresh output. -/
theorem kernelAdaptivePrefixNonBottomCount_append
    {Outcome : Type*} [MeasurableSpace Outcome]
    (bottom : Outcome) (round : ℕ)
    (pair : KernelAdaptiveRoundPair Outcome round) :
    kernelAdaptivePrefixNonBottomCount bottom (round + 1)
        (kernelAdaptiveAppendEquiv round pair) =
      kernelAdaptivePrefixNonBottomCount bottom round pair.1 +
        nonBottomNatIndicator bottom pair.2 := by
  have hprefix :
      frestrictLe₂ (π := fun _ : ℕ ↦ Outcome) round.le_succ
          (kernelAdaptiveAppendEquiv round pair) = pair.1 := by
    funext index
    simp [kernelAdaptiveAppendEquiv,
      MeasurableEquiv.IicProdIoc, MeasurableEquiv.prodCongr,
      Equiv.prodCongr, MeasurableEquiv.refl, MeasurableEquiv.piSingleton,
      frestrictLe₂, Finset.mem_Iic.mp index.2]
  rw [kernelAdaptivePrefixNonBottomCount, hprefix]
  simp [kernelAdaptiveAppendEquiv,
    MeasurableEquiv.IicProdIoc, MeasurableEquiv.prodCongr,
    Equiv.prodCongr, MeasurableEquiv.refl, MeasurableEquiv.piSingleton]

/-- Every finite prefix generated by the capped kernel contains at most the
publicly specified number of non-bottom outputs. -/
theorem cappedAdaptiveKernel_prefix_count_le
    {Outcome : Type*} [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome]
    (initialLaw : Measure Outcome) [IsProbabilityMeasure initialLaw]
    (cap : ℕ) (bottom : Outcome)
    (base : ∀ round : ℕ,
      Kernel ((i : Finset.Iic round) → Outcome) Outcome)
    [∀ round, IsMarkovKernel (base round)] :
    ∀ rounds,
      ∀ᵐ history ∂(Kernel.trajMeasure initialLaw
          (cappedAdaptiveKernel cap bottom base)).map
            (frestrictLe (π := fun _ : ℕ ↦ Outcome) rounds),
        kernelAdaptivePrefixNonBottomCount bottom rounds history ≤ cap := by
  intro rounds
  induction rounds with
  | zero =>
      filter_upwards [] with history
      simp [kernelAdaptivePrefixNonBottomCount]
  | succ rounds ih =>
      let kernel := cappedAdaptiveKernel cap bottom base
      let prefixLaw := (Kernel.trajMeasure initialLaw kernel).map
        (frestrictLe (π := fun _ : ℕ ↦ Outcome) rounds)
      let append := kernelAdaptiveAppendEquiv (Outcome := Outcome) rounds
      have hproperty : MeasurableSet {history |
          kernelAdaptivePrefixNonBottomCount bottom (rounds + 1) history ≤ cap} :=
        measurableSet_le
          (measurable_kernelAdaptivePrefixNonBottomCount bottom (rounds + 1))
          measurable_const
      rw [map_frestrictLe_succ_trajMeasure_eq_map_compProd_append
        initialLaw kernel rounds]
      rw [MeasureTheory.ae_map_iff append.measurable.aemeasurable hproperty]
      apply Measure.ae_compProd_of_ae_ae
      · exact hproperty.preimage append.measurable
      · filter_upwards [ih] with history hhistory
        by_cases hbelow :
            kernelAdaptivePrefixNonBottomCount bottom rounds history < cap
        · filter_upwards [] with outcome
          rw [kernelAdaptivePrefixNonBottomCount_append]
          change kernelAdaptivePrefixNonBottomCount bottom rounds history +
            nonBottomNatIndicator bottom outcome ≤ cap
          have hindicator : nonBottomNatIndicator bottom outcome ≤ 1 := by
            classical
            by_cases houtcome : outcome = bottom <;>
              simp [nonBottomNatIndicator, houtcome]
          omega
        · have hequal :
              kernelAdaptivePrefixNonBottomCount bottom rounds history = cap := by
            omega
          rw [show kernel rounds history = Measure.dirac bottom by
            exact cappedAdaptiveKernel_apply_of_not_lt
              cap bottom base rounds history hbelow]
          filter_upwards [ae_eq_dirac (fun outcome : Outcome ↦ outcome)]
            with outcome houtcome
          have houtcome' : outcome = bottom := by simpa using houtcome
          subst outcome
          rw [kernelAdaptivePrefixNonBottomCount_append]
          change kernelAdaptivePrefixNonBottomCount bottom rounds history +
            nonBottomNatIndicator bottom bottom ≤ cap
          simp [nonBottomNatIndicator, hequal]

/-- Infinite-trajectory form of the cap invariant. -/
theorem cappedAdaptiveKernel_nonBottomCount_le
    {Outcome : Type*} [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome]
    (initialLaw : Measure Outcome) [IsProbabilityMeasure initialLaw]
    (cap : ℕ) (bottom : Outcome)
    (base : ∀ round : ℕ,
      Kernel ((i : Finset.Iic round) → Outcome) Outcome)
    [∀ round, IsMarkovKernel (base round)] (rounds : ℕ) :
    ∀ᵐ trace ∂Kernel.trajMeasure initialLaw
        (cappedAdaptiveKernel cap bottom base),
      kernelAdaptiveNonBottomCount bottom rounds trace ≤ cap := by
  have hprefix := cappedAdaptiveKernel_prefix_count_le
    initialLaw cap bottom base rounds
  simpa [kernelAdaptiveNonBottomCount] using
    (MeasureTheory.ae_of_ae_map
      (measurable_frestrictLe rounds).aemeasurable hprefix)

end

end AppliedModelingLib
