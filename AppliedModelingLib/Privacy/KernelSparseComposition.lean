import AppliedModelingLib.Foundations.Probability.KernelAdaptiveCap
import AppliedModelingLib.Privacy.SparsePrivacyComposition
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.Kernel.Composition.RadonNikodym
import Mathlib.Probability.Kernel.RadonNikodym

/-!
# Adaptive sparse privacy composition for measurable kernels

This module lifts the one-round sparse privacy accountant to arbitrary
history-dependent Markov kernels.  The kernel Radon--Nikodym derivative is
jointly measurable in the public history and fresh output.  We clip its log
to the pure-privacy interval only to obtain a pointwise bounded representative;
under the first round law the clipping agrees almost surely with the genuine
measure-theoretic log-likelihood ratio.
-/

open MeasureTheory ProbabilityTheory Set Preorder

namespace AppliedModelingLib.Privacy

noncomputable section

/-- Jointly measurable log-likelihood representative for two kernels. -/
noncomputable def kernelPrivacyLoss
    {History Outcome : Type*} [MeasurableSpace History] [MeasurableSpace Outcome]
    [MeasurableSpace.CountableOrCountablyGenerated History Outcome]
    (first second : Kernel History Outcome) (pair : History × Outcome) : ℝ :=
  Real.log (Kernel.rnDeriv first second pair.1 pair.2).toReal

theorem measurable_kernelPrivacyLoss
    {History Outcome : Type*} [MeasurableSpace History] [MeasurableSpace Outcome]
    [MeasurableSpace.CountableOrCountablyGenerated History Outcome]
    (first second : Kernel History Outcome) :
    Measurable (kernelPrivacyLoss first second) := by
  exact Real.measurable_log.comp
    (Kernel.measurable_rnDeriv first second).ennreal_toReal

/-- Pointwise-bounded representative of the kernel privacy loss. -/
noncomputable def clippedKernelPrivacyLoss
    {History Outcome : Type*} [MeasurableSpace History] [MeasurableSpace Outcome]
    [MeasurableSpace.CountableOrCountablyGenerated History Outcome]
    (epsilon : ℝ) (first second : Kernel History Outcome)
    (pair : History × Outcome) : ℝ :=
  max (-epsilon) (min epsilon (kernelPrivacyLoss first second pair))

theorem measurable_clippedKernelPrivacyLoss
    {History Outcome : Type*} [MeasurableSpace History] [MeasurableSpace Outcome]
    [MeasurableSpace.CountableOrCountablyGenerated History Outcome]
    (epsilon : ℝ) (first second : Kernel History Outcome) :
    Measurable (clippedKernelPrivacyLoss epsilon first second) := by
  exact Measurable.max measurable_const
    (Measurable.min measurable_const (measurable_kernelPrivacyLoss first second))

theorem neg_le_clippedKernelPrivacyLoss
    {History Outcome : Type*} [MeasurableSpace History] [MeasurableSpace Outcome]
    [MeasurableSpace.CountableOrCountablyGenerated History Outcome]
    (epsilon : ℝ) (first second : Kernel History Outcome)
    (pair : History × Outcome) :
    -epsilon ≤ clippedKernelPrivacyLoss epsilon first second pair :=
  le_max_left _ _

theorem clippedKernelPrivacyLoss_le
    {History Outcome : Type*} [MeasurableSpace History] [MeasurableSpace Outcome]
    [MeasurableSpace.CountableOrCountablyGenerated History Outcome]
    {epsilon : ℝ} (hepsilonNonneg : 0 ≤ epsilon)
    (first second : Kernel History Outcome) (pair : History × Outcome) :
    clippedKernelPrivacyLoss epsilon first second pair ≤ epsilon := by
  unfold clippedKernelPrivacyLoss
  exact max_le (by linarith) (min_le_left _ _)

theorem max_neg_min_eq_self_of_abs_le
    {epsilon value : ℝ} (hbound : |value| ≤ epsilon) :
    max (-epsilon) (min epsilon value) = value := by
  have hbounds := abs_le.mp hbound
  rw [min_eq_right hbounds.2, max_eq_right hbounds.1]

/-- The kernel representative agrees almost surely with the ordinary
measure log-likelihood ratio under the first law. -/
theorem kernelPrivacyLoss_ae_eq_llr
    {History Outcome : Type*} [MeasurableSpace History] [MeasurableSpace Outcome]
    [MeasurableSpace.CountableOrCountablyGenerated History Outcome]
    (first second : Kernel History Outcome)
    [IsFiniteKernel first] [IsFiniteKernel second]
    (history : History) (hforward : first history ≪ second history) :
    (fun outcome ↦ kernelPrivacyLoss first second (history, outcome)) =ᵐ[first history]
      llr (first history) (second history) := by
  have hrnSecond := Kernel.rnDeriv_eq_rnDeriv_measure
    (κ := first) (η := second) (a := history)
  have hrnFirst := hforward.ae_eq hrnSecond
  filter_upwards [hrnFirst] with outcome houtcome
  simp only [kernelPrivacyLoss, llr]
  rw [houtcome]

/-- Under pure max-KL closeness, clipping changes the kernel privacy loss only
on a first-law null set. -/
theorem clippedKernelPrivacyLoss_ae_eq_llr
    {History Outcome : Type*} [MeasurableSpace History] [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome]
    [MeasurableSpace.CountableOrCountablyGenerated History Outcome]
    {epsilon : ℝ} (first second : Kernel History Outcome)
    [IsMarkovKernel first] [IsMarkovKernel second]
    (history : History)
    (hclose : MeasureMaxKLClose epsilon 0 (first history) (second history)) :
    (fun outcome ↦ clippedKernelPrivacyLoss epsilon first second
      (history, outcome)) =ᵐ[first history]
      llr (first history) (second history) := by
  have hloss := kernelPrivacyLoss_ae_eq_llr first second history
    hclose.1.absolutelyContinuous
  filter_upwards [hloss, hclose.abs_llr_le] with outcome heq hbound
  rw [clippedKernelPrivacyLoss, heq]
  exact max_neg_min_eq_self_of_abs_le hbound

/-- Pointwise chain rule for the log-likelihood ratio of a composition
product.  The conditional term uses the jointly measurable kernel RN
representative. -/
theorem llr_compProd_ae_eq_add_kernelPrivacyLoss
    {History Outcome : Type*} [MeasurableSpace History] [MeasurableSpace Outcome]
    [MeasurableSpace.CountableOrCountablyGenerated History Outcome]
    (firstHistory secondHistory : Measure History)
    [IsProbabilityMeasure firstHistory] [IsProbabilityMeasure secondHistory]
    (firstRound secondRound : Kernel History Outcome)
    [IsMarkovKernel firstRound] [IsMarkovKernel secondRound]
    (hhistory : firstHistory ≪ secondHistory)
    (hround : ∀ history, firstRound history ≪ secondRound history) :
    llr (firstHistory ⊗ₘ firstRound) (secondHistory ⊗ₘ secondRound) =ᵐ[
        firstHistory ⊗ₘ firstRound]
      fun pair ↦ llr firstHistory secondHistory pair.1 +
        kernelPrivacyLoss firstRound secondRound pair := by
  let firstJoint := firstHistory ⊗ₘ firstRound
  let sameHistorySecondRound := firstHistory ⊗ₘ secondRound
  let secondJoint := secondHistory ⊗ₘ secondRound
  have hconditionalAC : firstJoint ≪ sameHistorySecondRound := by
    dsimp [firstJoint, sameHistorySecondRound]
    exact Measure.AbsolutelyContinuous.compProd_right
      (ae_of_all _ hround)
  have hjointAC : firstJoint ≪ secondJoint := by
    dsimp [firstJoint, secondJoint]
    exact hhistory.compProd (ae_of_all _ hround)
  have hrnChainSecond :
      firstJoint.rnDeriv secondJoint =ᵐ[secondJoint]
        fun pair ↦ firstHistory.rnDeriv secondHistory pair.1 *
          firstJoint.rnDeriv sameHistorySecondRound pair := by
    dsimp [firstJoint, sameHistorySecondRound, secondJoint]
    exact rnDeriv_compProd
      (Measure.AbsolutelyContinuous.compProd_right (ae_of_all _ hround))
      secondHistory
  have hrnChainFirst := hjointAC.ae_eq hrnChainSecond
  have hkernelDensity : firstRound =
      secondRound.withDensity (Kernel.rnDeriv firstRound secondRound) := by
    apply Kernel.ext
    intro history
    exact (Kernel.withDensity_rnDeriv_eq (hround history)).symm
  have hjointDensity : firstJoint = sameHistorySecondRound.withDensity
      (fun pair ↦ Kernel.rnDeriv firstRound secondRound pair.1 pair.2) := by
    dsimp [firstJoint, sameHistorySecondRound]
    calc
      firstHistory ⊗ₘ firstRound =
          firstHistory ⊗ₘ
            (secondRound.withDensity
              (Kernel.rnDeriv firstRound secondRound)) := by
        exact congrArg (fun kernel ↦ firstHistory ⊗ₘ kernel) hkernelDensity
      _ = (firstHistory ⊗ₘ secondRound).withDensity
          (fun pair ↦ Kernel.rnDeriv firstRound secondRound pair.1 pair.2) :=
        Measure.compProd_withDensity
          (Kernel.measurable_rnDeriv firstRound secondRound)
  have hconditionalRNSecond :
      firstJoint.rnDeriv sameHistorySecondRound =ᵐ[sameHistorySecondRound]
        fun pair ↦ Kernel.rnDeriv firstRound secondRound pair.1 pair.2 := by
    rw [hjointDensity]
    exact Measure.rnDeriv_withDensity sameHistorySecondRound
      (Kernel.measurable_rnDeriv firstRound secondRound)
  have hconditionalRNFirst := hconditionalAC.ae_eq hconditionalRNSecond
  have hhistoryToRealPos : ∀ᵐ history ∂firstHistory,
      0 < (firstHistory.rnDeriv secondHistory history).toReal := by
    have hpos := Measure.rnDeriv_pos hhistory
    have hfinite := hhistory.ae_le
      (Measure.rnDeriv_ne_top firstHistory secondHistory)
    filter_upwards [hpos, hfinite] with history hpositive htop
    exact ENNReal.toReal_pos hpositive.ne' htop
  have hhistoryToRealPosJoint : ∀ᵐ pair ∂firstJoint,
      0 < (firstHistory.rnDeriv secondHistory pair.1).toReal := by
    dsimp [firstJoint]
    exact Measure.ae_compProd_of_ae_fst firstRound
      (measurableSet_Ioi.preimage
        (Measure.measurable_rnDeriv firstHistory secondHistory).ennreal_toReal)
      hhistoryToRealPos
  have hconditionalToRealPos : ∀ᵐ pair ∂firstJoint,
      0 < (firstJoint.rnDeriv sameHistorySecondRound pair).toReal := by
    have hpos := Measure.rnDeriv_pos hconditionalAC
    have hfinite := hconditionalAC.ae_le
      (Measure.rnDeriv_ne_top firstJoint sameHistorySecondRound)
    filter_upwards [hpos, hfinite] with pair hpositive htop
    exact ENNReal.toReal_pos hpositive.ne' htop
  filter_upwards [hrnChainFirst, hconditionalRNFirst,
      hhistoryToRealPosJoint, hconditionalToRealPos]
    with pair hchain hconditional hhistoryPos hconditionalPos
  simp only [llr, kernelPrivacyLoss]
  rw [hchain, ENNReal.toReal_mul,
    Real.log_mul hhistoryPos.ne' hconditionalPos.ne', hconditional]

/-- A measurable equivalence preserves the log-likelihood ratio along its
forward map, almost surely under the first law. -/
theorem llr_map_measurableEquiv_ae_eq
    {Input Output : Type*} [MeasurableSpace Input] [MeasurableSpace Output]
    (equiv : Input ≃ᵐ Output)
    (first second : Measure Input)
    [IsProbabilityMeasure first] [IsProbabilityMeasure second]
    (hforward : first ≪ second) :
    (fun input ↦ llr (first.map equiv) (second.map equiv) (equiv input)) =ᵐ[first]
      llr first second := by
  have hrnSecond := equiv.measurableEmbedding.rnDeriv_map first second
  have hrnFirst := hforward.ae_eq hrnSecond
  filter_upwards [hrnFirst] with input hinput
  simp only [llr]
  rw [hinput]

/-- Absolute continuity of every one-round conditional law composes along
the finite public prefix. -/
theorem adaptivePrefixLaw_absolutelyContinuous
    {Outcome : Type*} [MeasurableSpace Outcome]
    (initialLaw : Measure Outcome) [IsProbabilityMeasure initialLaw]
    (first second : ∀ round : ℕ,
      Kernel ((i : Finset.Iic round) → Outcome) Outcome)
    [∀ round, IsMarkovKernel (first round)]
    [∀ round, IsMarkovKernel (second round)]
    (hround : ∀ round history,
      first round history ≪ second round history) :
    ∀ rounds,
      (Kernel.trajMeasure initialLaw first).map
          (frestrictLe (π := fun _ : ℕ ↦ Outcome) rounds) ≪
        (Kernel.trajMeasure initialLaw second).map
          (frestrictLe (π := fun _ : ℕ ↦ Outcome) rounds) := by
  intro rounds
  induction rounds with
  | zero =>
      rw [AppliedModelingLib.map_frestrictLe_zero_trajMeasure initialLaw first,
        AppliedModelingLib.map_frestrictLe_zero_trajMeasure initialLaw second]
  | succ rounds ih =>
      rw [AppliedModelingLib.map_frestrictLe_succ_trajMeasure_eq_map_compProd_append
          initialLaw first rounds,
        AppliedModelingLib.map_frestrictLe_succ_trajMeasure_eq_map_compProd_append
          initialLaw second rounds]
      apply (AppliedModelingLib.kernelAdaptiveAppendEquiv
        (Outcome := Outcome) rounds).measurableEmbedding.absolutelyContinuous_map
      exact ih.compProd (ae_of_all _ (hround rounds))

/-- One-round exponential multiplier for sparse privacy accounting. -/
noncomputable def kernelSparsePrivacyMultiplier
    {History Outcome : Type*} [MeasurableSpace History] [MeasurableSpace Outcome]
    [MeasurableSpace.CountableOrCountablyGenerated History Outcome]
    (epsilon lambda theta : ℝ) (bottom : Outcome)
    (first second : Kernel History Outcome) (pair : History × Outcome) : ℝ :=
  Real.exp (lambda * clippedKernelPrivacyLoss epsilon first second pair -
    theta * nonLazyIndicator bottom pair.2)

theorem measurable_kernelSparsePrivacyMultiplier
    {History Outcome : Type*} [MeasurableSpace History] [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome]
    [MeasurableSpace.CountableOrCountablyGenerated History Outcome]
    (epsilon lambda theta : ℝ) (bottom : Outcome)
    (first second : Kernel History Outcome) :
    Measurable
      (kernelSparsePrivacyMultiplier epsilon lambda theta bottom first second) := by
  exact ((measurable_const.mul
      (measurable_clippedKernelPrivacyLoss epsilon first second)).sub
    (measurable_const.mul
      ((measurable_nonLazyIndicator bottom).comp measurable_snd))).exp

theorem kernelSparsePrivacyMultiplier_pos
    {History Outcome : Type*} [MeasurableSpace History] [MeasurableSpace Outcome]
    [MeasurableSpace.CountableOrCountablyGenerated History Outcome]
    (epsilon lambda theta : ℝ) (bottom : Outcome)
    (first second : Kernel History Outcome) (pair : History × Outcome) :
    0 < kernelSparsePrivacyMultiplier epsilon lambda theta bottom first second pair := by
  exact Real.exp_pos _

theorem kernelSparsePrivacyMultiplier_le_exp
    {History Outcome : Type*} [MeasurableSpace History] [MeasurableSpace Outcome]
    [MeasurableSpace.CountableOrCountablyGenerated History Outcome]
    {epsilon lambda theta : ℝ} (hepsilonNonneg : 0 ≤ epsilon)
    (hlambdaNonneg : 0 ≤ lambda) (hthetaNonneg : 0 ≤ theta)
    (bottom : Outcome) (first second : Kernel History Outcome)
    (pair : History × Outcome) :
    kernelSparsePrivacyMultiplier epsilon lambda theta bottom first second pair ≤
      Real.exp (lambda * epsilon) := by
  apply Real.exp_le_exp.mpr
  have hloss := clippedKernelPrivacyLoss_le hepsilonNonneg first second pair
  have hindicator := nonLazyIndicator_nonneg bottom pair.2
  nlinarith

/-- Conditional form of the one-round sparse accountant, expressed using the
jointly measurable clipped kernel likelihood. -/
theorem integral_kernelSparsePrivacyMultiplier_le_one
    {History Outcome : Type*} [MeasurableSpace History] [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome]
    [MeasurableSpace.CountableOrCountablyGenerated History Outcome]
    {epsilon lambda theta : ℝ}
    (first second : Kernel History Outcome)
    [IsMarkovKernel first] [IsMarkovKernel second]
    (history : History)
    (hclose : MeasureMaxKLClose epsilon 0 (first history) (second history))
    (hepsilonNonneg : 0 ≤ epsilon) (hepsilonOne : epsilon ≤ 1)
    (hlambdaNonneg : 0 ≤ lambda) (hlambdaUnit : lambda * epsilon ≤ 1)
    (hthetaNonneg : 0 ≤ theta)
    (bottom : Outcome)
    (hfirstBottom : 0 < (first history).real {bottom})
    (hsecondBottom : 0 < (second history).real {bottom})
    (hcompensation :
      7 * lambda * (1 + lambda) * epsilon ^ 2 ≤
        (1 - Real.exp (-theta)) * (1 - lambda * epsilon)) :
    ∫ outcome, kernelSparsePrivacyMultiplier epsilon lambda theta bottom
        first second (history, outcome) ∂first history ≤ 1 := by
  have hbase := integral_exp_privacyLoss_sub_nonLazy_le_one hclose
    hepsilonNonneg hepsilonOne hlambdaNonneg hlambdaUnit hthetaNonneg
    bottom hfirstBottom hsecondBottom hcompensation
  have heq := clippedKernelPrivacyLoss_ae_eq_llr first second history hclose
  calc
    ∫ outcome, kernelSparsePrivacyMultiplier epsilon lambda theta bottom
        first second (history, outcome) ∂first history =
        ∫ outcome, Real.exp
          (lambda * llr (first history) (second history) outcome -
            theta * nonLazyIndicator bottom outcome) ∂first history := by
      apply integral_congr_ae
      filter_upwards [heq] with outcome houtcome
      simp only [kernelSparsePrivacyMultiplier]
      rw [houtcome]
    _ ≤ 1 := hbase

/-- Adaptive sparse composition: the compensated likelihood-product has
expectation at most one at every finite horizon. -/
theorem integral_adaptiveSparsePrivacyProduct_le_one
    {Outcome : Type*} [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome]
    [MeasurableSpace.CountablyGenerated Outcome]
    (initialLaw : Measure Outcome) [IsProbabilityMeasure initialLaw]
    (first second : ∀ round : ℕ,
      Kernel ((i : Finset.Iic round) → Outcome) Outcome)
    [∀ round, IsMarkovKernel (first round)]
    [∀ round, IsMarkovKernel (second round)]
    {epsilon lambda theta : ℝ}
    (hepsilonNonneg : 0 ≤ epsilon) (hepsilonOne : epsilon ≤ 1)
    (hlambdaNonneg : 0 ≤ lambda) (hlambdaUnit : lambda * epsilon ≤ 1)
    (hthetaNonneg : 0 ≤ theta)
    (bottom : Outcome)
    (hclose : ∀ round history,
      MeasureMaxKLClose epsilon 0
        (first round history) (second round history))
    (hfirstBottom : ∀ round history,
      0 < (first round history).real {bottom})
    (hsecondBottom : ∀ round history,
      0 < (second round history).real {bottom})
    (hcompensation :
      7 * lambda * (1 + lambda) * epsilon ^ 2 ≤
        (1 - Real.exp (-theta)) * (1 - lambda * epsilon)) :
    ∀ rounds,
      ∫ trace, AppliedModelingLib.kernelAdaptiveProduct
          (fun round ↦ kernelSparsePrivacyMultiplier epsilon lambda theta bottom
            (first round) (second round)) rounds trace
        ∂Kernel.trajMeasure initialLaw first ≤ 1 := by
  apply AppliedModelingLib.integral_kernelAdaptiveProduct_le_one
    initialLaw first
    (fun round ↦ kernelSparsePrivacyMultiplier epsilon lambda theta bottom
      (first round) (second round))
    (fun round ↦ measurable_kernelSparsePrivacyMultiplier
      epsilon lambda theta bottom (first round) (second round))
    (Real.exp (lambda * epsilon)) (Real.exp_pos _).le
    (fun round pair ↦
      (kernelSparsePrivacyMultiplier_pos epsilon lambda theta bottom
        (first round) (second round) pair).le)
    (fun round pair ↦ kernelSparsePrivacyMultiplier_le_exp
      hepsilonNonneg hlambdaNonneg hthetaNonneg bottom
        (first round) (second round) pair)
  intro round history
  exact integral_kernelSparsePrivacyMultiplier_le_one
    (first round) (second round) history (hclose round history)
    hepsilonNonneg hepsilonOne hlambdaNonneg hlambdaUnit hthetaNonneg
    bottom (hfirstBottom round history) (hsecondBottom round history)
    hcompensation

/-- Sum of clipped conditional privacy losses through a finite horizon. -/
noncomputable def adaptiveClippedPrivacyLossSum
    {Outcome : Type*} [MeasurableSpace Outcome]
    [MeasurableSpace.CountablyGenerated Outcome]
    (epsilon : ℝ)
    (first second : ∀ round : ℕ,
      Kernel ((i : Finset.Iic round) → Outcome) Outcome)
    (rounds : ℕ) (trace : ℕ → Outcome) : ℝ :=
  ∑ round ∈ Finset.range rounds,
    clippedKernelPrivacyLoss epsilon (first round) (second round)
      (AppliedModelingLib.kernelAdaptiveRoundPair round trace)

/-- Real-valued count of non-lazy outputs through a finite horizon.  Every
summand is zero or one. -/
noncomputable def adaptiveNonLazyCount
    {Outcome : Type*} (bottom : Outcome)
    (rounds : ℕ) (trace : ℕ → Outcome) : ℝ :=
  ∑ round ∈ Finset.range rounds,
    nonLazyIndicator bottom (trace (round + 1))

theorem adaptiveClippedPrivacyLossSum_succ
    {Outcome : Type*} [MeasurableSpace Outcome]
    [MeasurableSpace.CountablyGenerated Outcome]
    (epsilon : ℝ)
    (first second : ∀ round : ℕ,
      Kernel ((i : Finset.Iic round) → Outcome) Outcome)
    (rounds : ℕ) (trace : ℕ → Outcome) :
    adaptiveClippedPrivacyLossSum epsilon first second (rounds + 1) trace =
      adaptiveClippedPrivacyLossSum epsilon first second rounds trace +
        clippedKernelPrivacyLoss epsilon (first rounds) (second rounds)
          (AppliedModelingLib.kernelAdaptiveRoundPair rounds trace) := by
  simp [adaptiveClippedPrivacyLossSum, Finset.sum_range_succ]

theorem adaptiveNonLazyCount_succ
    {Outcome : Type*} (bottom : Outcome)
    (rounds : ℕ) (trace : ℕ → Outcome) :
    adaptiveNonLazyCount bottom (rounds + 1) trace =
      adaptiveNonLazyCount bottom rounds trace +
        nonLazyIndicator bottom (trace (rounds + 1)) := by
  simp [adaptiveNonLazyCount, Finset.sum_range_succ]

theorem measurable_adaptiveClippedPrivacyLossSum
    {Outcome : Type*} [MeasurableSpace Outcome]
    [MeasurableSpace.CountablyGenerated Outcome]
    (epsilon : ℝ)
    (first second : ∀ round : ℕ,
      Kernel ((i : Finset.Iic round) → Outcome) Outcome)
    (rounds : ℕ) :
    Measurable (adaptiveClippedPrivacyLossSum epsilon first second rounds) := by
  exact Finset.measurable_sum (Finset.range rounds) fun round _ ↦
    (measurable_clippedKernelPrivacyLoss epsilon
      (first round) (second round)).comp
        (AppliedModelingLib.measurable_kernelAdaptiveRoundPair round)

theorem measurable_adaptiveNonLazyCount
    {Outcome : Type*} [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome]
    (bottom : Outcome) (rounds : ℕ) :
    Measurable (adaptiveNonLazyCount bottom rounds) := by
  exact Finset.measurable_sum (Finset.range rounds) fun round _ ↦
    (measurable_nonLazyIndicator bottom).comp (measurable_pi_apply (round + 1))

/-- The real-valued privacy charge is the cast of the reusable natural-valued
non-bottom count. -/
theorem adaptiveNonLazyCount_eq_natCast
    {Outcome : Type*} (bottom : Outcome)
    (rounds : ℕ) (trace : ℕ → Outcome) :
    adaptiveNonLazyCount bottom rounds trace =
      (AppliedModelingLib.kernelAdaptiveNonBottomCount bottom rounds trace : ℝ) := by
  induction rounds with
  | zero =>
      simp [adaptiveNonLazyCount,
        AppliedModelingLib.kernelAdaptiveNonBottomCount,
        AppliedModelingLib.kernelAdaptivePrefixNonBottomCount]
  | succ rounds ih =>
      rw [adaptiveNonLazyCount_succ,
        AppliedModelingLib.kernelAdaptiveNonBottomCount_succ, Nat.cast_add, ← ih]
      congr 1
      classical
      by_cases houtcome : trace (rounds + 1) = bottom <;>
        simp [nonLazyIndicator, AppliedModelingLib.nonBottomNatIndicator, houtcome]

/-- A publicly capped adaptive kernel satisfies the real-valued release cap
required by sparse privacy composition. -/
theorem cappedAdaptiveKernel_adaptiveNonLazyCount_le
    {Outcome : Type*} [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome]
    (initialLaw : Measure Outcome) [IsProbabilityMeasure initialLaw]
    (cap : ℕ) (bottom : Outcome)
    (base : ∀ round : ℕ,
      Kernel ((i : Finset.Iic round) → Outcome) Outcome)
    [∀ round, IsMarkovKernel (base round)] (rounds : ℕ) :
    ∀ᵐ trace ∂Kernel.trajMeasure initialLaw
        (AppliedModelingLib.cappedAdaptiveKernel cap bottom base),
      adaptiveNonLazyCount bottom rounds trace ≤ (cap : ℝ) := by
  filter_upwards [AppliedModelingLib.cappedAdaptiveKernel_nonBottomCount_le
    initialLaw cap bottom base rounds] with trace htrace
  rw [adaptiveNonLazyCount_eq_natCast]
  exact_mod_cast htrace

/-- Capping two base kernels according to the same public prefix preserves
their pointwise pure-privacy relation. -/
theorem cappedAdaptiveKernel_measureMaxKLClose
    {Outcome : Type*} [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome]
    (cap : ℕ) (bottom : Outcome)
    (first second : ∀ round : ℕ,
      Kernel ((i : Finset.Iic round) → Outcome) Outcome)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (hclose : ∀ round history,
      MeasureMaxKLClose epsilon 0
        (first round history) (second round history))
    (round : ℕ) (history : (i : Finset.Iic round) → Outcome) :
    MeasureMaxKLClose epsilon 0
      (AppliedModelingLib.cappedAdaptiveKernel cap bottom first round history)
      (AppliedModelingLib.cappedAdaptiveKernel cap bottom second round history) := by
  by_cases hcount :
      AppliedModelingLib.kernelAdaptivePrefixNonBottomCount bottom round history < cap
  · rw [AppliedModelingLib.cappedAdaptiveKernel_apply_of_lt
        cap bottom first round history hcount,
      AppliedModelingLib.cappedAdaptiveKernel_apply_of_lt
        cap bottom second round history hcount]
    exact hclose round history
  · rw [AppliedModelingLib.cappedAdaptiveKernel_apply_of_not_lt
        cap bottom first round history hcount,
      AppliedModelingLib.cappedAdaptiveKernel_apply_of_not_lt
        cap bottom second round history hcount]
    exact MeasureMaxKLClose.refl (Measure.dirac bottom) hepsilon le_rfl

/-- The distinguished bottom atom remains positive after public capping. -/
theorem cappedAdaptiveKernel_bottom_real_pos
    {Outcome : Type*} [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome]
    (cap : ℕ) (bottom : Outcome)
    (base : ∀ round : ℕ,
      Kernel ((i : Finset.Iic round) → Outcome) Outcome)
    (hbottom : ∀ round history,
      0 < (base round history).real {bottom})
    (round : ℕ) (history : (i : Finset.Iic round) → Outcome) :
    0 < (AppliedModelingLib.cappedAdaptiveKernel cap bottom base round history).real
      {bottom} := by
  by_cases hcount :
      AppliedModelingLib.kernelAdaptivePrefixNonBottomCount bottom round history < cap
  · rw [AppliedModelingLib.cappedAdaptiveKernel_apply_of_lt
        cap bottom base round history hcount]
    exact hbottom round history
  · rw [AppliedModelingLib.cappedAdaptiveKernel_apply_of_not_lt
        cap bottom base round history hcount]
    rw [Measure.real_def,
      Measure.dirac_apply' _ (measurableSet_singleton bottom)]
    simp

/-- Cumulative clipped privacy loss as a function of the finite prefix itself.
The append equivalence makes the successor recursion canonical. -/
noncomputable def adaptivePrefixClippedPrivacyLoss
    {Outcome : Type*} [MeasurableSpace Outcome]
    [MeasurableSpace.CountablyGenerated Outcome]
    (epsilon : ℝ)
    (first second : ∀ round : ℕ,
      Kernel ((i : Finset.Iic round) → Outcome) Outcome) :
    ∀ rounds : ℕ, ((i : Finset.Iic rounds) → Outcome) → ℝ
  | 0, _ => 0
  | rounds + 1, history =>
      let pair := (AppliedModelingLib.kernelAdaptiveAppendEquiv
        (Outcome := Outcome) rounds).symm history
      adaptivePrefixClippedPrivacyLoss epsilon first second rounds pair.1 +
        clippedKernelPrivacyLoss epsilon (first rounds) (second rounds) pair

theorem measurable_adaptivePrefixClippedPrivacyLoss
    {Outcome : Type*} [MeasurableSpace Outcome]
    [MeasurableSpace.CountablyGenerated Outcome]
    (epsilon : ℝ)
    (first second : ∀ round : ℕ,
      Kernel ((i : Finset.Iic round) → Outcome) Outcome) :
    ∀ rounds, Measurable
      (adaptivePrefixClippedPrivacyLoss epsilon first second rounds) := by
  intro rounds
  induction rounds with
  | zero => exact measurable_const
  | succ rounds ih =>
      let split := (AppliedModelingLib.kernelAdaptiveAppendEquiv
        (Outcome := Outcome) rounds).symm
      change Measurable (fun history ↦
        adaptivePrefixClippedPrivacyLoss epsilon first second rounds
            (split history).1 +
          clippedKernelPrivacyLoss epsilon (first rounds) (second rounds)
            (split history))
      exact (ih.comp (measurable_fst.comp split.measurable)).add
        ((measurable_clippedKernelPrivacyLoss epsilon
          (first rounds) (second rounds)).comp split.measurable)

/-- The finite-prefix recursion agrees with the explicit sum read from an
infinite trajectory. -/
theorem adaptivePrefixClippedPrivacyLoss_frestrictLe
    {Outcome : Type*} [MeasurableSpace Outcome]
    [MeasurableSpace.CountablyGenerated Outcome]
    (epsilon : ℝ)
    (first second : ∀ round : ℕ,
      Kernel ((i : Finset.Iic round) → Outcome) Outcome) :
    ∀ rounds (trace : ℕ → Outcome),
      adaptivePrefixClippedPrivacyLoss epsilon first second rounds
          (frestrictLe rounds trace) =
        adaptiveClippedPrivacyLossSum epsilon first second rounds trace := by
  intro rounds
  induction rounds with
  | zero =>
      intro trace
      simp [adaptivePrefixClippedPrivacyLoss,
        adaptiveClippedPrivacyLossSum]
  | succ rounds ih =>
      intro trace
      let append := AppliedModelingLib.kernelAdaptiveAppendEquiv
        (Outcome := Outcome) rounds
      have hsplit : append.symm (frestrictLe (rounds + 1) trace) =
          AppliedModelingLib.kernelAdaptiveRoundPair rounds trace := by
        apply append.injective
        rw [append.apply_symm_apply]
        exact (AppliedModelingLib.kernelAdaptiveAppendEquiv_apply_roundPair
          rounds trace).symm
      change adaptivePrefixClippedPrivacyLoss epsilon first second rounds
          (append.symm (frestrictLe (rounds + 1) trace)).1 +
        clippedKernelPrivacyLoss epsilon (first rounds) (second rounds)
          (append.symm (frestrictLe (rounds + 1) trace)) = _
      rw [hsplit]
      change adaptivePrefixClippedPrivacyLoss epsilon first second rounds
          (frestrictLe rounds trace) +
        clippedKernelPrivacyLoss epsilon (first rounds) (second rounds)
          (AppliedModelingLib.kernelAdaptiveRoundPair rounds trace) = _
      rw [ih]
      exact (adaptiveClippedPrivacyLossSum_succ
        epsilon first second rounds trace).symm

/-- The cumulative clipped conditional loss is the actual log-likelihood
ratio of the two finite public-prefix laws, almost surely under the first law.
This is the finite-transcript chain rule needed to turn the exponential tail
into differential privacy. -/
theorem llr_adaptivePrefixLaw_ae_eq_clippedPrivacyLoss
    {Outcome : Type*} [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome]
    [MeasurableSpace.CountablyGenerated Outcome]
    (initialLaw : Measure Outcome) [IsProbabilityMeasure initialLaw]
    (first second : ∀ round : ℕ,
      Kernel ((i : Finset.Iic round) → Outcome) Outcome)
    [∀ round, IsMarkovKernel (first round)]
    [∀ round, IsMarkovKernel (second round)]
    {epsilon : ℝ}
    (hclose : ∀ round history,
      MeasureMaxKLClose epsilon 0
        (first round history) (second round history)) :
    ∀ rounds,
      llr
          ((Kernel.trajMeasure initialLaw first).map
            (frestrictLe (π := fun _ : ℕ ↦ Outcome) rounds))
          ((Kernel.trajMeasure initialLaw second).map
            (frestrictLe (π := fun _ : ℕ ↦ Outcome) rounds)) =ᵐ[
            (Kernel.trajMeasure initialLaw first).map
              (frestrictLe (π := fun _ : ℕ ↦ Outcome) rounds)]
        adaptivePrefixClippedPrivacyLoss epsilon first second rounds := by
  intro rounds
  induction rounds with
  | zero =>
      rw [AppliedModelingLib.map_frestrictLe_zero_trajMeasure initialLaw first,
        AppliedModelingLib.map_frestrictLe_zero_trajMeasure initialLaw second]
      simpa [adaptivePrefixClippedPrivacyLoss] using
        llr_self (initialLaw.map
          (MeasurableEquiv.piUnique
            ((fun _ : Finset.Iic 0 ↦ Outcome))).symm)
  | succ rounds ih =>
      let firstPrefix : Measure ((i : Finset.Iic rounds) → Outcome) :=
        (Kernel.trajMeasure initialLaw first).map
          (frestrictLe (π := fun _ : ℕ ↦ Outcome) rounds)
      let secondPrefix : Measure ((i : Finset.Iic rounds) → Outcome) :=
        (Kernel.trajMeasure initialLaw second).map
          (frestrictLe (π := fun _ : ℕ ↦ Outcome) rounds)
      let firstJoint := firstPrefix ⊗ₘ first rounds
      let secondJoint := secondPrefix ⊗ₘ second rounds
      let append := AppliedModelingLib.kernelAdaptiveAppendEquiv
        (Outcome := Outcome) rounds
      letI : IsProbabilityMeasure firstPrefix := by
        dsimp [firstPrefix]
        exact Measure.isProbabilityMeasure_map
          (measurable_frestrictLe rounds).aemeasurable
      letI : IsProbabilityMeasure secondPrefix := by
        dsimp [secondPrefix]
        exact Measure.isProbabilityMeasure_map
          (measurable_frestrictLe rounds).aemeasurable
      have hprefixAC : firstPrefix ≪ secondPrefix := by
        dsimp [firstPrefix, secondPrefix]
        exact adaptivePrefixLaw_absolutelyContinuous initialLaw first second
          (fun round history ↦
            (hclose round history).1.absolutelyContinuous) rounds
      have hjointAC : firstJoint ≪ secondJoint := by
        dsimp [firstJoint, secondJoint]
        exact hprefixAC.compProd (ae_of_all _ fun history ↦
          (hclose rounds history).1.absolutelyContinuous)
      have hchain : llr firstJoint secondJoint =ᵐ[firstJoint]
          fun pair ↦ llr firstPrefix secondPrefix pair.1 +
            kernelPrivacyLoss (first rounds) (second rounds) pair := by
        dsimp [firstJoint, secondJoint]
        exact llr_compProd_ae_eq_add_kernelPrivacyLoss
          firstPrefix secondPrefix (first rounds) (second rounds)
          hprefixAC (fun history ↦
            (hclose rounds history).1.absolutelyContinuous)
      have hihJoint :
          (fun pair : AppliedModelingLib.KernelAdaptiveRoundPair Outcome rounds ↦
            llr firstPrefix secondPrefix pair.1) =ᵐ[firstJoint]
          fun pair ↦ adaptivePrefixClippedPrivacyLoss
            epsilon first second rounds pair.1 := by
        dsimp [firstJoint]
        exact Measure.ae_eq_compProd_of_ae_eq_fst (first rounds)
          (measurable_llr firstPrefix secondPrefix)
          (measurable_adaptivePrefixClippedPrivacyLoss
            epsilon first second rounds) ih
      have hkernelClip :
          (fun pair : AppliedModelingLib.KernelAdaptiveRoundPair Outcome rounds ↦
            kernelPrivacyLoss (first rounds) (second rounds) pair) =ᵐ[firstJoint]
          fun pair ↦ clippedKernelPrivacyLoss epsilon
            (first rounds) (second rounds) pair := by
        dsimp [firstJoint]
        apply Measure.ae_compProd_of_ae_ae
          (measurableSet_eq_fun
            (measurable_kernelPrivacyLoss (first rounds) (second rounds))
            (measurable_clippedKernelPrivacyLoss epsilon
              (first rounds) (second rounds)))
        filter_upwards [] with history
        exact (kernelPrivacyLoss_ae_eq_llr
            (first rounds) (second rounds) history
            (hclose rounds history).1.absolutelyContinuous).trans
          (clippedKernelPrivacyLoss_ae_eq_llr
            (first rounds) (second rounds) history
            (hclose rounds history)).symm
      have hmap :
          (fun pair : AppliedModelingLib.KernelAdaptiveRoundPair Outcome rounds ↦
            llr (firstJoint.map append) (secondJoint.map append)
              (append pair)) =ᵐ[firstJoint]
            llr firstJoint secondJoint := by
        exact llr_map_measurableEquiv_ae_eq append
          firstJoint secondJoint hjointAC
      have hpullback :
          (fun pair : AppliedModelingLib.KernelAdaptiveRoundPair Outcome rounds ↦
            llr (firstJoint.map append) (secondJoint.map append)
              (append pair)) =ᵐ[firstJoint]
          fun pair ↦ adaptivePrefixClippedPrivacyLoss epsilon first second
            (rounds + 1) (append pair) := by
        filter_upwards [hmap, hchain, hihJoint, hkernelClip]
          with pair hmapPair hchainPair hihPair hclipPair
        rw [hmapPair, hchainPair, hihPair, hclipPair]
        simp [adaptivePrefixClippedPrivacyLoss, append]
      have hpush :
          llr (firstJoint.map append) (secondJoint.map append) =ᵐ[
              firstJoint.map append]
            adaptivePrefixClippedPrivacyLoss epsilon first second (rounds + 1) := by
        rw [Filter.EventuallyEq, append.measurableEmbedding.ae_map_iff,
          ← Filter.EventuallyEq]
        exact hpullback
      rw [AppliedModelingLib.map_frestrictLe_succ_trajMeasure_eq_map_compProd_append
          initialLaw first rounds,
        AppliedModelingLib.map_frestrictLe_succ_trajMeasure_eq_map_compProd_append
          initialLaw second rounds]
      exact hpush

/-- The adaptive privacy product is exactly the exponential of cumulative
clipped loss minus the cumulative non-lazy charge. -/
theorem kernelAdaptiveProduct_sparsePrivacy_eq_exp
    {Outcome : Type*} [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome]
    [MeasurableSpace.CountablyGenerated Outcome]
    (first second : ∀ round : ℕ,
      Kernel ((i : Finset.Iic round) → Outcome) Outcome)
    (epsilon lambda theta : ℝ) (bottom : Outcome) :
    ∀ rounds trace,
      AppliedModelingLib.kernelAdaptiveProduct
          (fun round ↦ kernelSparsePrivacyMultiplier epsilon lambda theta bottom
            (first round) (second round)) rounds trace =
        Real.exp
          (lambda * adaptiveClippedPrivacyLossSum epsilon first second rounds trace -
            theta * adaptiveNonLazyCount bottom rounds trace) := by
  intro rounds
  induction rounds with
  | zero =>
      intro trace
      simp [AppliedModelingLib.kernelAdaptiveProduct,
        AppliedModelingLib.kernelAdaptivePrefixProduct,
        adaptiveClippedPrivacyLossSum, adaptiveNonLazyCount]
  | succ rounds ih =>
      intro trace
      rw [AppliedModelingLib.kernelAdaptiveProduct_succ, ih,
        adaptiveClippedPrivacyLossSum_succ, adaptiveNonLazyCount_succ]
      simp only [kernelSparsePrivacyMultiplier]
      rw [← Real.exp_add]
      congr 1
      simp only [AppliedModelingLib.kernelAdaptiveRoundPair]
      ring

/-- Finite-horizon privacy-loss tail from a deterministic cap on non-lazy
outputs.  This is the corrected sparse-composition replacement for an Azuma
argument over a random set of borderline rounds. -/
theorem adaptiveClippedPrivacyLoss_tail_le_exp
    {Outcome : Type*} [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome]
    [MeasurableSpace.CountablyGenerated Outcome]
    (initialLaw : Measure Outcome) [IsProbabilityMeasure initialLaw]
    (first second : ∀ round : ℕ,
      Kernel ((i : Finset.Iic round) → Outcome) Outcome)
    [∀ round, IsMarkovKernel (first round)]
    [∀ round, IsMarkovKernel (second round)]
    {epsilon lambda theta : ℝ}
    (hepsilonNonneg : 0 ≤ epsilon) (hepsilonOne : epsilon ≤ 1)
    (hlambdaPos : 0 < lambda) (hlambdaUnit : lambda * epsilon ≤ 1)
    (hthetaNonneg : 0 ≤ theta)
    (bottom : Outcome)
    (hclose : ∀ round history,
      MeasureMaxKLClose epsilon 0
        (first round history) (second round history))
    (hfirstBottom : ∀ round history,
      0 < (first round history).real {bottom})
    (hsecondBottom : ∀ round history,
      0 < (second round history).real {bottom})
    (hcompensation :
      7 * lambda * (1 + lambda) * epsilon ^ 2 ≤
        (1 - Real.exp (-theta)) * (1 - lambda * epsilon))
    (rounds : ℕ) (updateCap target : ℝ)
    (hupdateCap : ∀ᵐ trace ∂Kernel.trajMeasure initialLaw first,
      adaptiveNonLazyCount bottom rounds trace ≤ updateCap) :
    (Kernel.trajMeasure initialLaw first).real {trace |
      target < adaptiveClippedPrivacyLossSum epsilon first second rounds trace} ≤
        Real.exp (-lambda * target + theta * updateCap) := by
  let trajectory : Measure (ℕ → Outcome) :=
    Kernel.trajMeasure initialLaw first
  let multiplier := fun round ↦
    kernelSparsePrivacyMultiplier epsilon lambda theta bottom
      (first round) (second round)
  let weight : (ℕ → Outcome) → ℝ :=
    AppliedModelingLib.kernelAdaptiveProduct multiplier rounds
  let threshold := Real.exp (lambda * target - theta * updateCap)
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    infer_instance
  have hweightNonneg : 0 ≤ᵐ[trajectory] weight := by
    filter_upwards [] with trace
    dsimp [weight, multiplier]
    exact AppliedModelingLib.kernelAdaptivePrefixProduct_nonneg _
      (fun round pair ↦ (kernelSparsePrivacyMultiplier_pos
        epsilon lambda theta bottom (first round) (second round) pair).le)
      rounds _
  have hweightIntegrable : Integrable weight trajectory := by
    dsimp [weight, multiplier, trajectory]
    exact AppliedModelingLib.integrable_kernelAdaptiveProduct _ _
      (fun round ↦ measurable_kernelSparsePrivacyMultiplier
        epsilon lambda theta bottom (first round) (second round))
      (Real.exp (lambda * epsilon)) (Real.exp_pos _).le
      (fun round pair ↦ (kernelSparsePrivacyMultiplier_pos
        epsilon lambda theta bottom (first round) (second round) pair).le)
      (fun round pair ↦ kernelSparsePrivacyMultiplier_le_exp
        hepsilonNonneg hlambdaPos.le hthetaNonneg bottom
          (first round) (second round) pair) rounds
  have hexpectation : ∫ trace, weight trace ∂trajectory ≤ 1 := by
    dsimp [weight, multiplier, trajectory]
    exact integral_adaptiveSparsePrivacyProduct_le_one initialLaw first second
      hepsilonNonneg hepsilonOne hlambdaPos.le hlambdaUnit hthetaNonneg
      bottom hclose hfirstBottom hsecondBottom hcompensation rounds
  have hthresholdPos : 0 < threshold := Real.exp_pos _
  have hmarkov : threshold * trajectory.real {trace | threshold ≤ weight trace} ≤ 1 :=
    (mul_meas_ge_le_integral_of_nonneg hweightNonneg hweightIntegrable
      threshold).trans hexpectation
  have htail : trajectory.real {trace | threshold ≤ weight trace} ≤
      Real.exp (-lambda * target + theta * updateCap) := by
    have hdiv : trajectory.real {trace | threshold ≤ weight trace} ≤
        1 / threshold := by
      rw [le_div_iff₀ hthresholdPos]
      simpa [mul_comm] using hmarkov
    calc
      trajectory.real {trace | threshold ≤ weight trace} ≤
          1 / threshold := hdiv
      _ = Real.exp (-lambda * target + theta * updateCap) := by
        dsimp [threshold]
        rw [one_div, ← Real.exp_neg]
        congr 1
        ring
  have hinclusion : {trace |
      target < adaptiveClippedPrivacyLossSum epsilon first second rounds trace} ≤ᵐ[trajectory]
      {trace | threshold ≤ weight trace} := by
    filter_upwards [hupdateCap] with trace hcap
    intro htrace
    have hexponent :
        lambda * target - theta * updateCap <
          lambda * adaptiveClippedPrivacyLossSum epsilon first second rounds trace -
            theta * adaptiveNonLazyCount bottom rounds trace := by
      have hlossScaled := mul_lt_mul_of_pos_left htrace hlambdaPos
      have hcountScaled := mul_le_mul_of_nonneg_left hcap hthetaNonneg
      linarith
    have hexp := (Real.exp_lt_exp.mpr hexponent).le
    change threshold ≤ weight trace
    dsimp [threshold, weight, multiplier]
    rw [kernelAdaptiveProduct_sparsePrivacy_eq_exp]
    exact hexp
  have hmeasure : trajectory.real {trace |
      target < adaptiveClippedPrivacyLossSum epsilon first second rounds trace} ≤
      trajectory.real {trace | threshold ≤ weight trace} := by
    rw [Measure.real_def, Measure.real_def]
    exact ENNReal.toReal_mono (measure_ne_top trajectory _)
      (measure_mono_ae hinclusion)
  exact hmeasure.trans htail

/-- The same tail bound stated directly on the released finite-prefix law. -/
theorem adaptivePrefixClippedPrivacyLoss_tail_le_exp
    {Outcome : Type*} [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome]
    [MeasurableSpace.CountablyGenerated Outcome]
    (initialLaw : Measure Outcome) [IsProbabilityMeasure initialLaw]
    (first second : ∀ round : ℕ,
      Kernel ((i : Finset.Iic round) → Outcome) Outcome)
    [∀ round, IsMarkovKernel (first round)]
    [∀ round, IsMarkovKernel (second round)]
    {epsilon lambda theta : ℝ}
    (hepsilonNonneg : 0 ≤ epsilon) (hepsilonOne : epsilon ≤ 1)
    (hlambdaPos : 0 < lambda) (hlambdaUnit : lambda * epsilon ≤ 1)
    (hthetaNonneg : 0 ≤ theta)
    (bottom : Outcome)
    (hclose : ∀ round history,
      MeasureMaxKLClose epsilon 0
        (first round history) (second round history))
    (hfirstBottom : ∀ round history,
      0 < (first round history).real {bottom})
    (hsecondBottom : ∀ round history,
      0 < (second round history).real {bottom})
    (hcompensation :
      7 * lambda * (1 + lambda) * epsilon ^ 2 ≤
        (1 - Real.exp (-theta)) * (1 - lambda * epsilon))
    (rounds : ℕ) (updateCap target : ℝ)
    (hupdateCap : ∀ᵐ trace ∂Kernel.trajMeasure initialLaw first,
      adaptiveNonLazyCount bottom rounds trace ≤ updateCap) :
    ((Kernel.trajMeasure initialLaw first).map
      (frestrictLe (π := fun _ : ℕ ↦ Outcome) rounds)).real {history |
        target < adaptivePrefixClippedPrivacyLoss
          epsilon first second rounds history} ≤
      Real.exp (-lambda * target + theta * updateCap) := by
  have hbadMeasurable : MeasurableSet {history |
      target < adaptivePrefixClippedPrivacyLoss
        epsilon first second rounds history} :=
    measurableSet_Ioi.preimage
      (measurable_adaptivePrefixClippedPrivacyLoss
        epsilon first second rounds)
  rw [map_measureReal_apply (measurable_frestrictLe rounds) hbadMeasurable]
  have htail := adaptiveClippedPrivacyLoss_tail_le_exp
    initialLaw first second hepsilonNonneg hepsilonOne hlambdaPos
    hlambdaUnit hthetaNonneg bottom hclose hfirstBottom hsecondBottom
    hcompensation rounds updateCap target hupdateCap
  simpa only [Set.preimage_setOf_eq,
    adaptivePrefixClippedPrivacyLoss_frestrictLe] using htail

/-- The actual prefix log-likelihood ratio obeys the sparse privacy tail. -/
theorem adaptivePrefix_llr_tail_le_exp
    {Outcome : Type*} [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome]
    [MeasurableSpace.CountablyGenerated Outcome]
    (initialLaw : Measure Outcome) [IsProbabilityMeasure initialLaw]
    (first second : ∀ round : ℕ,
      Kernel ((i : Finset.Iic round) → Outcome) Outcome)
    [∀ round, IsMarkovKernel (first round)]
    [∀ round, IsMarkovKernel (second round)]
    {epsilon lambda theta : ℝ}
    (hepsilonNonneg : 0 ≤ epsilon) (hepsilonOne : epsilon ≤ 1)
    (hlambdaPos : 0 < lambda) (hlambdaUnit : lambda * epsilon ≤ 1)
    (hthetaNonneg : 0 ≤ theta)
    (bottom : Outcome)
    (hclose : ∀ round history,
      MeasureMaxKLClose epsilon 0
        (first round history) (second round history))
    (hfirstBottom : ∀ round history,
      0 < (first round history).real {bottom})
    (hsecondBottom : ∀ round history,
      0 < (second round history).real {bottom})
    (hcompensation :
      7 * lambda * (1 + lambda) * epsilon ^ 2 ≤
        (1 - Real.exp (-theta)) * (1 - lambda * epsilon))
    (rounds : ℕ) (updateCap target : ℝ)
    (hupdateCap : ∀ᵐ trace ∂Kernel.trajMeasure initialLaw first,
      adaptiveNonLazyCount bottom rounds trace ≤ updateCap) :
    let firstPrefix := (Kernel.trajMeasure initialLaw first).map
      (frestrictLe (π := fun _ : ℕ ↦ Outcome) rounds)
    let secondPrefix := (Kernel.trajMeasure initialLaw second).map
      (frestrictLe (π := fun _ : ℕ ↦ Outcome) rounds)
    firstPrefix.real {history |
      target < llr firstPrefix secondPrefix history} ≤
        Real.exp (-lambda * target + theta * updateCap) := by
  dsimp only
  let firstPrefix := (Kernel.trajMeasure initialLaw first).map
    (frestrictLe (π := fun _ : ℕ ↦ Outcome) rounds)
  let secondPrefix := (Kernel.trajMeasure initialLaw second).map
    (frestrictLe (π := fun _ : ℕ ↦ Outcome) rounds)
  have hscoreTail := adaptivePrefixClippedPrivacyLoss_tail_le_exp
    initialLaw first second hepsilonNonneg hepsilonOne hlambdaPos
    hlambdaUnit hthetaNonneg bottom hclose hfirstBottom hsecondBottom
    hcompensation rounds updateCap target hupdateCap
  have hllr := llr_adaptivePrefixLaw_ae_eq_clippedPrivacyLoss
    initialLaw first second hclose rounds
  have hbadEq : {history | target < llr firstPrefix secondPrefix history} =ᵐ[firstPrefix]
      {history | target < adaptivePrefixClippedPrivacyLoss
        epsilon first second rounds history} := by
    filter_upwards [hllr] with history hhistory
    simpa [firstPrefix, secondPrefix] using
      (congrArg (fun score : ℝ ↦ target < score) hhistory)
  have hrealEq : firstPrefix.real
      {history | target < llr firstPrefix secondPrefix history} =
      firstPrefix.real {history | target < adaptivePrefixClippedPrivacyLoss
        epsilon first second rounds history} :=
    congrArg ENNReal.toReal (measure_congr hbadEq)
  rw [hrealEq]
  simpa [firstPrefix] using hscoreTail

/-- Directed approximate privacy for a finite adaptive prefix under a
deterministic non-lazy-output cap. -/
theorem adaptivePrefix_measureApproxDomination
    {Outcome : Type*} [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome]
    [MeasurableSpace.CountablyGenerated Outcome]
    (initialLaw : Measure Outcome) [IsProbabilityMeasure initialLaw]
    (first second : ∀ round : ℕ,
      Kernel ((i : Finset.Iic round) → Outcome) Outcome)
    [∀ round, IsMarkovKernel (first round)]
    [∀ round, IsMarkovKernel (second round)]
    {epsilon lambda theta : ℝ}
    (hepsilonNonneg : 0 ≤ epsilon) (hepsilonOne : epsilon ≤ 1)
    (hlambdaPos : 0 < lambda) (hlambdaUnit : lambda * epsilon ≤ 1)
    (hthetaNonneg : 0 ≤ theta)
    (bottom : Outcome)
    (hclose : ∀ round history,
      MeasureMaxKLClose epsilon 0
        (first round history) (second round history))
    (hfirstBottom : ∀ round history,
      0 < (first round history).real {bottom})
    (hsecondBottom : ∀ round history,
      0 < (second round history).real {bottom})
    (hcompensation :
      7 * lambda * (1 + lambda) * epsilon ^ 2 ≤
        (1 - Real.exp (-theta)) * (1 - lambda * epsilon))
    (rounds : ℕ) (updateCap target : ℝ)
    (hupdateCap : ∀ᵐ trace ∂Kernel.trajMeasure initialLaw first,
      adaptiveNonLazyCount bottom rounds trace ≤ updateCap) :
    MeasureApproxDomination target
      (Real.exp (-lambda * target + theta * updateCap))
      ((Kernel.trajMeasure initialLaw first).map
        (frestrictLe (π := fun _ : ℕ ↦ Outcome) rounds))
      ((Kernel.trajMeasure initialLaw second).map
        (frestrictLe (π := fun _ : ℕ ↦ Outcome) rounds)) := by
  let firstPrefix := (Kernel.trajMeasure initialLaw first).map
    (frestrictLe (π := fun _ : ℕ ↦ Outcome) rounds)
  let secondPrefix := (Kernel.trajMeasure initialLaw second).map
    (frestrictLe (π := fun _ : ℕ ↦ Outcome) rounds)
  letI : IsProbabilityMeasure firstPrefix :=
    Measure.isProbabilityMeasure_map (measurable_frestrictLe rounds).aemeasurable
  letI : IsProbabilityMeasure secondPrefix :=
    Measure.isProbabilityMeasure_map (measurable_frestrictLe rounds).aemeasurable
  apply MeasureApproxDomination.of_llr_tail firstPrefix secondPrefix
  · exact adaptivePrefixLaw_absolutelyContinuous initialLaw first second
      (fun round history ↦
        (hclose round history).1.absolutelyContinuous) rounds
  · exact adaptivePrefix_llr_tail_le_exp initialLaw first second
      hepsilonNonneg hepsilonOne hlambdaPos hlambdaUnit hthetaNonneg
      bottom hclose hfirstBottom hsecondBottom hcompensation
      rounds updateCap target hupdateCap

/-- Two-sided approximate privacy when both adjacent executions obey the same
deterministic non-lazy-output cap. -/
theorem adaptivePrefix_measureMaxKLClose
    {Outcome : Type*} [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome]
    [MeasurableSpace.CountablyGenerated Outcome]
    (initialLaw : Measure Outcome) [IsProbabilityMeasure initialLaw]
    (first second : ∀ round : ℕ,
      Kernel ((i : Finset.Iic round) → Outcome) Outcome)
    [∀ round, IsMarkovKernel (first round)]
    [∀ round, IsMarkovKernel (second round)]
    {epsilon lambda theta : ℝ}
    (hepsilonNonneg : 0 ≤ epsilon) (hepsilonOne : epsilon ≤ 1)
    (hlambdaPos : 0 < lambda) (hlambdaUnit : lambda * epsilon ≤ 1)
    (hthetaNonneg : 0 ≤ theta)
    (bottom : Outcome)
    (hclose : ∀ round history,
      MeasureMaxKLClose epsilon 0
        (first round history) (second round history))
    (hfirstBottom : ∀ round history,
      0 < (first round history).real {bottom})
    (hsecondBottom : ∀ round history,
      0 < (second round history).real {bottom})
    (hcompensation :
      7 * lambda * (1 + lambda) * epsilon ^ 2 ≤
        (1 - Real.exp (-theta)) * (1 - lambda * epsilon))
    (rounds : ℕ) (updateCap target : ℝ)
    (hupdateCapFirst : ∀ᵐ trace ∂Kernel.trajMeasure initialLaw first,
      adaptiveNonLazyCount bottom rounds trace ≤ updateCap)
    (hupdateCapSecond : ∀ᵐ trace ∂Kernel.trajMeasure initialLaw second,
      adaptiveNonLazyCount bottom rounds trace ≤ updateCap) :
    MeasureMaxKLClose target
      (Real.exp (-lambda * target + theta * updateCap))
      ((Kernel.trajMeasure initialLaw first).map
        (frestrictLe (π := fun _ : ℕ ↦ Outcome) rounds))
      ((Kernel.trajMeasure initialLaw second).map
        (frestrictLe (π := fun _ : ℕ ↦ Outcome) rounds)) := by
  constructor
  · exact adaptivePrefix_measureApproxDomination initialLaw first second
      hepsilonNonneg hepsilonOne hlambdaPos hlambdaUnit hthetaNonneg
      bottom hclose hfirstBottom hsecondBottom hcompensation
      rounds updateCap target hupdateCapFirst
  · exact adaptivePrefix_measureApproxDomination initialLaw second first
      hepsilonNonneg hepsilonOne hlambdaPos hlambdaUnit hthetaNonneg
      bottom (fun round history ↦
        ⟨(hclose round history).2, (hclose round history).1⟩)
      hsecondBottom hfirstBottom hcompensation
      rounds updateCap target hupdateCapSecond

/-- Reusable sparse-privacy theorem for two adaptive kernel families after a
common public non-bottom cap.  Callers provide only the uncapped pointwise
pure-privacy and positive-bottom facts; the cap construction supplies both
trajectory count bounds automatically. -/
theorem cappedAdaptiveKernel_prefix_measureMaxKLClose
    {Outcome : Type*} [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome]
    [MeasurableSpace.CountablyGenerated Outcome]
    (initialLaw : Measure Outcome) [IsProbabilityMeasure initialLaw]
    (cap : ℕ) (bottom : Outcome)
    (firstBase secondBase : ∀ round : ℕ,
      Kernel ((i : Finset.Iic round) → Outcome) Outcome)
    [∀ round, IsMarkovKernel (firstBase round)]
    [∀ round, IsMarkovKernel (secondBase round)]
    {epsilon lambda theta target : ℝ}
    (hepsilonNonneg : 0 ≤ epsilon) (hepsilonOne : epsilon ≤ 1)
    (hlambdaPos : 0 < lambda) (hlambdaUnit : lambda * epsilon ≤ 1)
    (hthetaNonneg : 0 ≤ theta)
    (hclose : ∀ round history,
      MeasureMaxKLClose epsilon 0
        (firstBase round history) (secondBase round history))
    (hfirstBottom : ∀ round history,
      0 < (firstBase round history).real {bottom})
    (hsecondBottom : ∀ round history,
      0 < (secondBase round history).real {bottom})
    (hcompensation :
      7 * lambda * (1 + lambda) * epsilon ^ 2 ≤
        (1 - Real.exp (-theta)) * (1 - lambda * epsilon))
    (rounds : ℕ) :
    MeasureMaxKLClose target
      (Real.exp (-lambda * target + theta * (cap : ℝ)))
      ((Kernel.trajMeasure initialLaw
          (AppliedModelingLib.cappedAdaptiveKernel cap bottom firstBase)).map
        (frestrictLe (π := fun _ : ℕ ↦ Outcome) rounds))
      ((Kernel.trajMeasure initialLaw
          (AppliedModelingLib.cappedAdaptiveKernel cap bottom secondBase)).map
        (frestrictLe (π := fun _ : ℕ ↦ Outcome) rounds)) := by
  let first := AppliedModelingLib.cappedAdaptiveKernel cap bottom firstBase
  let second := AppliedModelingLib.cappedAdaptiveKernel cap bottom secondBase
  letI : ∀ round, IsMarkovKernel (first round) := fun round ↦ by
    dsimp [first]
    infer_instance
  letI : ∀ round, IsMarkovKernel (second round) := fun round ↦ by
    dsimp [second]
    infer_instance
  have hcappedClose : ∀ round history,
      MeasureMaxKLClose epsilon 0
        (first round history) (second round history) := by
    intro round history
    exact cappedAdaptiveKernel_measureMaxKLClose cap bottom
      firstBase secondBase hepsilonNonneg hclose round history
  have hcappedFirstBottom : ∀ round history,
      0 < (first round history).real {bottom} :=
    fun round history ↦ cappedAdaptiveKernel_bottom_real_pos
      cap bottom firstBase hfirstBottom round history
  have hcappedSecondBottom : ∀ round history,
      0 < (second round history).real {bottom} :=
    fun round history ↦ cappedAdaptiveKernel_bottom_real_pos
      cap bottom secondBase hsecondBottom round history
  have hfirstCap : ∀ᵐ trace ∂Kernel.trajMeasure initialLaw first,
      adaptiveNonLazyCount bottom rounds trace ≤ (cap : ℝ) := by
    exact cappedAdaptiveKernel_adaptiveNonLazyCount_le
      initialLaw cap bottom firstBase rounds
  have hsecondCap : ∀ᵐ trace ∂Kernel.trajMeasure initialLaw second,
      adaptiveNonLazyCount bottom rounds trace ≤ (cap : ℝ) := by
    exact cappedAdaptiveKernel_adaptiveNonLazyCount_le
      initialLaw cap bottom secondBase rounds
  exact adaptivePrefix_measureMaxKLClose initialLaw first second
    hepsilonNonneg hepsilonOne hlambdaPos hlambdaUnit hthetaNonneg
    bottom hcappedClose hcappedFirstBottom hcappedSecondBottom
    hcompensation rounds (cap : ℝ) target hfirstCap hsecondCap

end

end AppliedModelingLib.Privacy
