import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.Invariance
import Mathlib.Probability.Process.Filtration

/-!
# Stationary discrete-time trajectories for invariant Markov kernels

This module constructs the Ionescu--Tulcea trajectory of a homogeneous Markov
kernel started from an invariant probability measure and proves that every
coordinate has the original invariant marginal.
-/

open scoped ENNReal NNReal

open MeasureTheory ProbabilityTheory
open Preorder
open Filtration

namespace AppliedModelingLib.Probability.Queueing

variable {α : Type*} [MeasurableSpace α]

noncomputable def homogeneousTrajKernel (K : Kernel α α) (n : ℕ) :
    Kernel ((i : Finset.Iic n) → α) α :=
  K ∘ₖ Kernel.deterministic (fun x => x ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
    (measurable_pi_apply _)

instance homogeneousTrajKernel.isMarkovKernel (K : Kernel α α) [IsMarkovKernel K]
    (n : ℕ) : IsMarkovKernel (homogeneousTrajKernel K n) := by
  unfold homogeneousTrajKernel
  infer_instance

noncomputable def stationaryTrajMeasure (π : Measure α) (K : Kernel α α)
    [IsMarkovKernel K] : Measure (ℕ → α) :=
  Kernel.trajMeasure (X := fun _ : ℕ => α) π (homogeneousTrajKernel K)

theorem stationaryTrajMeasure_succ_marginal
    {π : Measure α} [IsProbabilityMeasure π] {K : Kernel α α} [IsMarkovKernel K]
    (a : ℕ) :
    (stationaryTrajMeasure π K).map (fun x => x (a + 1)) =
      K ∘ₘ (stationaryTrajMeasure π K).map (fun x => x a) := by
  have h := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (X := fun _ : ℕ => α) (μ₀ := π) (κ := homogeneousTrajKernel K) (a := a)
  have hsnd := congrArg Measure.snd h
  rw [Measure.snd_compProd] at hsnd
  change (K ∘ₖ Kernel.deterministic
      (fun x : (i : Finset.Iic a) → α => x ⟨a, Finset.mem_Iic.mpr le_rfl⟩)
      (measurable_pi_apply _)) ∘ₘ
      (stationaryTrajMeasure π K).map (Preorder.frestrictLe a) = _ at hsnd
  change (K ∘ₖ Kernel.deterministic
      (fun x : (i : Finset.Iic a) → α => x ⟨a, Finset.mem_Iic.mpr le_rfl⟩)
      (measurable_pi_apply _)) ∘ₘ
      (stationaryTrajMeasure π K).map (Preorder.frestrictLe a) =
      Measure.map Prod.snd
        (Measure.map (fun x : ℕ → α => (Preorder.frestrictLe a x, x (a + 1)))
          (stationaryTrajMeasure π K)) at hsnd
  rw [← Measure.comp_assoc, Measure.deterministic_comp_eq_map] at hsnd
  have hlast : Measurable (fun x : (i : Finset.Iic a) → α =>
      x ⟨a, Finset.mem_Iic.mpr le_rfl⟩) := measurable_pi_apply _
  rw [Measure.map_map hlast (measurable_frestrictLe a)] at hsnd
  have hpair : Measurable (fun x : ℕ → α => (Preorder.frestrictLe a x, x (a + 1))) :=
    (measurable_frestrictLe a).prodMk (measurable_pi_apply _)
  rw [Measure.map_map measurable_snd hpair] at hsnd
  simpa only [Function.comp_apply, Preorder.frestrictLe_apply] using hsnd.symm

/-- Mapping the retained input coordinate of a composition product through a
measurable function commutes with applying the transition kernel to that
coordinate. -/
theorem Measure.compProd_map_input
    {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    (ν : Measure β) [SFinite ν] (K : Kernel α γ) [IsSFiniteKernel K]
    (f : β → α) (hf : Measurable f) :
    (ν ⊗ₘ (K ∘ₖ Kernel.deterministic f hf)).map
        (fun p : β × γ => (f p.1, p.2)) =
      (ν.map f) ⊗ₘ K := by
  ext s hs
  have hmap : Measurable (fun p : β × γ => (f p.1, p.2)) :=
    hf.comp measurable_fst |>.prodMk measurable_snd
  have hpre : MeasurableSet ((fun p : β × γ => (f p.1, p.2)) ⁻¹' s) :=
    hs.preimage hmap
  rw [Measure.map_apply hmap hs, Measure.compProd_apply hpre,
    Kernel.comp_deterministic_eq_comap, Measure.compProd_apply hs]
  have hfun : (fun a : β =>
      Kernel.comap K f hf a
        (Prod.mk a ⁻¹' ((fun p : β × γ => (f p.1, p.2)) ⁻¹' s))) =
      (fun a : β => K (f a) (Prod.mk (f a) ⁻¹' s)) := by
    funext a
    rw [Kernel.comap_apply]
    congr 1
  rw [hfun]
  rw [← MeasureTheory.lintegral_map
    (Kernel.measurable_kernel_prodMk_left hs) hf]

/-- The Ionescu--Tulcea law of a homogeneous Markov chain has the exact
finite-history-to-next-state recurrence.  This is stronger than equality of
one-coordinate marginals: it preserves the transition kernel after every
observed finite prefix. -/
theorem stationaryTrajMeasure_prefix_succ
    {π : Measure α} [IsProbabilityMeasure π] {K : Kernel α α} [IsMarkovKernel K]
    (n : ℕ) :
    (stationaryTrajMeasure π K).map
        (fun x => (Preorder.frestrictLe n x, x (n + 1))) =
      (stationaryTrajMeasure π K).map (Preorder.frestrictLe n) ⊗ₘ
        (K ∘ₖ Kernel.deterministic
          (fun x : (i : Finset.Iic n) → α =>
            x ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
          (measurable_pi_apply _)) := by
  have h := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (X := fun _ : ℕ => α) (μ₀ := π) (κ := homogeneousTrajKernel K) (a := n)
  simpa [homogeneousTrajKernel] using h.symm

/-- Every consecutive pair in an Ionescu--Tulcea trajectory has the current
coordinate law followed by one application of the transition kernel.  This
does not require invariance of the initial law. -/
theorem stationaryTrajMeasure_consecutivePair_recurrence
    {π : Measure α} [IsProbabilityMeasure π] {K : Kernel α α} [IsMarkovKernel K]
    (n : ℕ) :
    (stationaryTrajMeasure π K).map (fun x => (x n, x (n + 1))) =
      ((stationaryTrajMeasure π K).map (fun x => x n)) ⊗ₘ K := by
  letI (j : ℕ) : IsMarkovKernel (homogeneousTrajKernel K j) :=
    homogeneousTrajKernel.isMarkovKernel K j
  have hprob : IsProbabilityMeasure (stationaryTrajMeasure π K) := by
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsProbabilityMeasure (stationaryTrajMeasure π K) := hprob
  letI : IsFiniteMeasure (stationaryTrajMeasure π K) := ⟨by
    rw [IsProbabilityMeasure.measure_univ]
    exact ENNReal.one_lt_top⟩
  let hist : (ℕ → α) → (i : Finset.Iic n) → α := Preorder.frestrictLe n
  let lastState : ((i : Finset.Iic n) → α) → α :=
    fun x => x ⟨n, Finset.mem_Iic.mpr le_rfl⟩
  let historyNext : (ℕ → α) → ((i : Finset.Iic n) → α) × α :=
    fun x => (hist x, x (n + 1))
  let statePair : (ℕ → α) → α × α := fun x => (x n, x (n + 1))
  let pairFromHistory : ((i : Finset.Iic n) → α) × α → α × α :=
    fun pair => (lastState pair.1, pair.2)
  have hhist : Measurable hist := measurable_frestrictLe n
  have hlastState : Measurable lastState := measurable_pi_apply _
  have hhistoryNext : Measurable historyNext := hhist.prodMk (measurable_pi_apply _)
  have hpairFromHistory : Measurable pairFromHistory :=
    hlastState.comp measurable_fst |>.prodMk measurable_snd
  have hrec := stationaryTrajMeasure_prefix_succ (π := π) (K := K) n
  calc
    (stationaryTrajMeasure π K).map statePair =
        ((stationaryTrajMeasure π K).map historyNext).map pairFromHistory := by
          rw [Measure.map_map hpairFromHistory hhistoryNext]
          rfl
    _ = ((stationaryTrajMeasure π K).map hist ⊗ₘ
          (K ∘ₖ Kernel.deterministic lastState hlastState)).map pairFromHistory := by
          rw [hrec]
    _ = ((stationaryTrajMeasure π K).map hist).map lastState ⊗ₘ K := by
          exact Measure.compProd_map_input _ K lastState hlastState
    _ = ((stationaryTrajMeasure π K).map (fun x => x n)) ⊗ₘ K := by
          rw [Measure.map_map hlastState hhist]
          rfl

/-- An almost-sure one-step property of a Markov kernel holds for the
corresponding consecutive coordinate pair of every Ionescu--Tulcea
trajectory.  No invariance assumption is needed on the initial law. -/
theorem ae_stationaryTrajMeasure_consecutivePair_of_ae
    {π : Measure α} [IsProbabilityMeasure π] {K : Kernel α α} [IsMarkovKernel K]
    (property : α → α → Prop)
    (hproperty : MeasurableSet {statePair : α × α |
      property statePair.1 statePair.2})
    (hkernel : ∀ state : α, ∀ᵐ next ∂K state, property state next)
    (n : ℕ) :
    ∀ᵐ path ∂stationaryTrajMeasure π K, property (path n) (path (n + 1)) := by
  let trajectory : Measure (ℕ → α) := stationaryTrajMeasure π K
  let statePair : (ℕ → α) → α × α := fun path => (path n, path (n + 1))
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory, stationaryTrajMeasure]
    infer_instance
  have hpair : ∀ᵐ pair ∂((trajectory.map (fun path => path n)) ⊗ₘ K),
      property pair.1 pair.2 := by
    refine Measure.ae_compProd_of_ae_ae hproperty ?_
    exact Filter.Eventually.of_forall hkernel
  have hpairMap : Measure.map statePair trajectory =
      (trajectory.map (fun path => path n)) ⊗ₘ K := by
    exact stationaryTrajMeasure_consecutivePair_recurrence (π := π) (K := K) n
  refine ae_of_ae_map (μ := trajectory) (f := statePair)
    (p := fun pair : α × α => property pair.1 pair.2)
    ((measurable_pi_apply n).prodMk (measurable_pi_apply (n + 1))).aemeasurable ?_
  rw [hpairMap]
  exact hpair

/-- A uniform bound on the conditional norm integral of a one-step reward
lifts its statewise integrability to any coordinate transition of an
Ionescu--Tulcea trajectory. -/
theorem integrable_stationaryTrajMeasure_next_reward_of_uniform_integral_norm_le
    {π : Measure α} [IsProbabilityMeasure π] {K : Kernel α α} [IsMarkovKernel K]
    (n : ℕ) (reward : α → α → ℝ)
    (hreward : Measurable (fun statePair : α × α => reward statePair.1 statePair.2))
    (hkernelInt : ∀ state : α, Integrable (reward state) (K state))
    (bound : ℝ)
    (hbound : ∀ state : α, ∫ next, ‖reward state next‖ ∂K state ≤ bound) :
    Integrable (fun path : ℕ → α => reward (path n) (path (n + 1)))
      (stationaryTrajMeasure π K) := by
  let trajectory : Measure (ℕ → α) := stationaryTrajMeasure π K
  let currentMeasure : Measure α := trajectory.map (fun path => path n)
  let statePair : (ℕ → α) → α × α := fun path => (path n, path (n + 1))
  let increment : (ℕ → α) → ℝ := fun path => reward (path n) (path (n + 1))
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory, stationaryTrajMeasure]
    infer_instance
  letI : IsFiniteMeasure trajectory := by infer_instance
  letI : IsFiniteMeasure currentMeasure := by
    dsimp [currentMeasure]
    infer_instance
  have hstatePair : Measurable statePair :=
    (measurable_pi_apply n).prodMk (measurable_pi_apply (n + 1))
  have houterMeas : StronglyMeasurable (fun state : α =>
      ∫ next, ‖reward state next‖ ∂K state) := by
    exact hreward.norm.stronglyMeasurable.integral_kernel_prod_right
  have houterInt : Integrable (fun state : α =>
      ∫ next, ‖reward state next‖ ∂K state) currentMeasure := by
    apply Integrable.of_bound houterMeas.aestronglyMeasurable bound
    filter_upwards [] with state
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact hbound state
    · exact integral_nonneg_of_ae
        (Filter.Eventually.of_forall fun next => norm_nonneg _)
  have hpairInt : Integrable (fun statePair : α × α =>
      reward statePair.1 statePair.2) (currentMeasure ⊗ₘ K) := by
    refine (Measure.integrable_compProd_iff hreward.aestronglyMeasurable).mpr ?_
    exact ⟨Filter.Eventually.of_forall hkernelInt, houterInt⟩
  have hpairLaw : Measure.map statePair trajectory = currentMeasure ⊗ₘ K := by
    exact stationaryTrajMeasure_consecutivePair_recurrence (π := π) (K := K) n
  have hpairMap : Integrable (fun statePair : α × α =>
      reward statePair.1 statePair.2) (Measure.map statePair trajectory) := by
    rw [hpairLaw]
    exact hpairInt
  have htransport := (integrable_map_measure hreward.aestronglyMeasurable
    hstatePair.aemeasurable).mp hpairMap
  simpa [increment, statePair] using htransport

/-- Under the same uniform conditional norm bound, the statewise kernel mean
is integrable when evaluated along any fixed coordinate of the trajectory. -/
theorem integrable_stationaryTrajMeasure_kernelIntegral_of_uniform_integral_norm_le
    {π : Measure α} [IsProbabilityMeasure π] {K : Kernel α α} [IsMarkovKernel K]
    (n : ℕ) (reward : α → α → ℝ)
    (hreward : Measurable (fun statePair : α × α => reward statePair.1 statePair.2))
    (bound : ℝ)
    (hbound : ∀ state : α, ∫ next, ‖reward state next‖ ∂K state ≤ bound) :
    Integrable (fun path : ℕ → α => ∫ next, reward (path n) next ∂K (path n))
      (stationaryTrajMeasure π K) := by
  have hprob : IsProbabilityMeasure (stationaryTrajMeasure π K) := by
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsProbabilityMeasure (stationaryTrajMeasure π K) := hprob
  letI : IsFiniteMeasure (stationaryTrajMeasure π K) := ⟨by
    rw [IsProbabilityMeasure.measure_univ]
    exact ENNReal.one_lt_top⟩
  have hkernelMeanMeas : StronglyMeasurable (fun state : α =>
      ∫ next, reward state next ∂K state) := by
    exact hreward.stronglyMeasurable.integral_kernel_prod_right
  apply Integrable.of_bound
    (hkernelMeanMeas.comp_measurable (measurable_pi_apply n)).aestronglyMeasurable bound
  filter_upwards [] with path
  exact (norm_integral_le_integral_norm _).trans (hbound (path n))

/-- A nonnegative one-step reward whose conditional integral has a uniform
bound has the same bound after sampling any transition of an
Ionescu--Tulcea trajectory. -/
theorem integral_stationaryTrajMeasure_next_reward_le_of_uniform_kernelIntegral_le
    {π : Measure α} [IsProbabilityMeasure π] {K : Kernel α α} [IsMarkovKernel K]
    (n : ℕ) (reward : α → α → ℝ)
    (hreward : Measurable (fun statePair : α × α => reward statePair.1 statePair.2))
    (hkernelInt : ∀ state : α, Integrable (reward state) (K state))
    (hnonneg : ∀ state next, 0 ≤ reward state next)
    (bound : ℝ)
    (hbound : ∀ state : α, ∫ next, reward state next ∂K state ≤ bound) :
    (∫ path : ℕ → α, reward (path n) (path (n + 1)) ∂stationaryTrajMeasure π K) ≤ bound := by
  let trajectory : Measure (ℕ → α) := stationaryTrajMeasure π K
  let currentMeasure : Measure α := trajectory.map (fun path => path n)
  let statePair : (ℕ → α) → α × α := fun path => (path n, path (n + 1))
  let increment : (ℕ → α) → ℝ := fun path => reward (path n) (path (n + 1))
  let kernelMean : α → ℝ := fun state => ∫ next, reward state next ∂K state
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory, stationaryTrajMeasure]
    infer_instance
  letI : IsFiniteMeasure trajectory := by infer_instance
  letI : IsFiniteMeasure currentMeasure := by
    dsimp [currentMeasure]
    infer_instance
  letI : IsProbabilityMeasure currentMeasure := by
    dsimp [currentMeasure]
    exact Measure.isProbabilityMeasure_map (measurable_pi_apply n).aemeasurable
  have hstatePair : Measurable statePair :=
    (measurable_pi_apply n).prodMk (measurable_pi_apply (n + 1))
  have hkernelMeanMeas : StronglyMeasurable kernelMean := by
    exact hreward.stronglyMeasurable.integral_kernel_prod_right
  have hkernelMeanInt : Integrable kernelMean currentMeasure := by
    apply Integrable.of_bound hkernelMeanMeas.aestronglyMeasurable bound
    filter_upwards [] with state
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact hbound state
    · exact integral_nonneg (fun next => hnonneg state next)
  have hkernelNormMeanInt : Integrable (fun state : α =>
      ∫ next, ‖reward state next‖ ∂K state) currentMeasure := by
    apply hkernelMeanInt.congr
    filter_upwards [] with state
    apply integral_congr_ae
    filter_upwards [] with next
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg state next)]
  have hpairInt : Integrable (fun statePair : α × α =>
      reward statePair.1 statePair.2) (currentMeasure ⊗ₘ K) := by
    refine (Measure.integrable_compProd_iff hreward.aestronglyMeasurable).mpr ?_
    exact ⟨Filter.Eventually.of_forall hkernelInt, hkernelNormMeanInt⟩
  have hpairLaw : Measure.map statePair trajectory = currentMeasure ⊗ₘ K := by
    exact stationaryTrajMeasure_consecutivePair_recurrence (π := π) (K := K) n
  have hpairMap : Integrable (fun statePair : α × α =>
      reward statePair.1 statePair.2) (Measure.map statePair trajectory) := by
    rw [hpairLaw]
    exact hpairInt
  calc
    (∫ path : ℕ → α, reward (path n) (path (n + 1)) ∂stationaryTrajMeasure π K) =
        ∫ path, increment path ∂trajectory := by rfl
    _ = ∫ statePair, reward statePair.1 statePair.2 ∂Measure.map statePair trajectory := by
      symm
      exact integral_map hstatePair.aemeasurable hpairMap.aestronglyMeasurable
    _ = ∫ statePair, reward statePair.1 statePair.2 ∂currentMeasure ⊗ₘ K := by
      rw [hpairLaw]
    _ = ∫ state, kernelMean state ∂currentMeasure := by
      rw [Measure.integral_compProd hpairInt]
    _ ≤ ∫ _ : α, bound ∂currentMeasure := by
      apply integral_mono_ae hkernelMeanInt (integrable_const bound)
      filter_upwards [] with state
      exact hbound state
    _ = bound := by simp

/-- An integrable one-step reward has conditional mean given by its transition
kernel integral after any finite trajectory history.  The theorem deliberately
keeps the reward's trajectory integrability and the integrability of the
specified kernel mean as explicit hypotheses, so it can be used for
unbounded transition rewards without silently introducing a moment premise. -/
theorem stationaryTrajMeasure_next_condExp_eq_of_kernelIntegral
    {π : Measure α} [IsProbabilityMeasure π] {K : Kernel α α} [IsMarkovKernel K]
    (n : ℕ) (reward : α → α → ℝ) (mean : α → ℝ)
    (hreward : Measurable (fun statePair : α × α => reward statePair.1 statePair.2))
    (hmean : Measurable mean)
    (hincrement : Integrable (fun path : ℕ → α => reward (path n) (path (n + 1)))
      (stationaryTrajMeasure π K))
    (hmeanInt : Integrable (fun path : ℕ → α => mean (path n))
      (stationaryTrajMeasure π K))
    (hkernel : ∀ state : α, ∫ next, reward state next ∂K state = mean state) :
    (stationaryTrajMeasure π K)[(fun path => reward (path n) (path (n + 1))) |
      piLE n] =ᵐ[stationaryTrajMeasure π K]
      fun path => mean (path n) := by
  classical
  let trajectory : Measure (ℕ → α) := stationaryTrajMeasure π K
  let history : (ℕ → α) → ((i : Finset.Iic n) → α) := Preorder.frestrictLe n
  let last : ((i : Finset.Iic n) → α) → α :=
    fun past => past ⟨n, Finset.mem_Iic.mpr le_rfl⟩
  let historyKernel : Kernel ((i : Finset.Iic n) → α) α :=
    K ∘ₖ Kernel.deterministic last (measurable_pi_apply _)
  let historyMeasure : Measure ((i : Finset.Iic n) → α) := trajectory.map history
  let historyNext : (ℕ → α) → ((i : Finset.Iic n) → α) × α :=
    fun path => (history path, path (n + 1))
  let increment : (ℕ → α) → ℝ := fun path => reward (path n) (path (n + 1))
  let pairIncrement : ((i : Finset.Iic n) → α) × α → ℝ :=
    fun historyPair => reward (last historyPair.1) historyPair.2
  let right : (ℕ → α) → ℝ := fun path => mean (path n)
  let pastRight : ((i : Finset.Iic n) → α) → ℝ := fun past => mean (last past)
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory, stationaryTrajMeasure]
    infer_instance
  letI : IsFiniteMeasure trajectory := by infer_instance
  letI : IsFiniteMeasure historyMeasure := by
    dsimp [historyMeasure]
    infer_instance
  letI : IsFiniteMeasure (historyMeasure ⊗ₘ historyKernel) := by infer_instance
  have hhistory : Measurable history := Preorder.measurable_frestrictLe n
  have hlast : Measurable last := measurable_pi_apply _
  have hhistoryNext : Measurable historyNext :=
    hhistory.prodMk (measurable_pi_apply (n + 1))
  have hincrementInt : Integrable increment trajectory := by
    simpa [increment, trajectory] using hincrement
  have hrightInt : Integrable right trajectory := by
    simpa [right, trajectory] using hmeanInt
  have hpairIncrementMeas : Measurable pairIncrement := by
    exact hreward.comp ((hlast.comp measurable_fst).prodMk measurable_snd)
  have hhistoryLaw : Measure.map historyNext trajectory =
      historyMeasure ⊗ₘ historyKernel := by
    exact stationaryTrajMeasure_prefix_succ (π := π) (K := K) n
  have hpairIncrementInt : Integrable pairIncrement (historyMeasure ⊗ₘ historyKernel) := by
    rw [← hhistoryLaw]
    apply (integrable_map_measure hpairIncrementMeas.aestronglyMeasurable
      hhistoryNext.aemeasurable).mpr
    simpa [pairIncrement, historyNext, increment, history, last] using hincrementInt
  have hhistoryKernel_apply (past : (i : Finset.Iic n) → α) :
      historyKernel past = K (last past) := by
    dsimp [historyKernel]
    rw [Kernel.comp_deterministic_eq_comap, Kernel.comap_apply]
  have hhistoryIntegral : ∀ (historyEvent : Set ((i : Finset.Iic n) → α)),
      MeasurableSet historyEvent →
      (∫ path, historyEvent.indicator (fun _ => (1 : ℝ)) (history path) * increment path
        ∂trajectory) =
        ∫ path, historyEvent.indicator (fun _ => (1 : ℝ)) (history path) * right path
          ∂trajectory := by
    intro historyEvent hhistoryEvent
    let weight : ((i : Finset.Iic n) → α) → ℝ :=
      historyEvent.indicator (fun _ => (1 : ℝ))
    let weightedPairIncrement : ((i : Finset.Iic n) → α) × α → ℝ :=
      fun historyPair => weight historyPair.1 * pairIncrement historyPair
    have hweightedPairIncrementInt : Integrable weightedPairIncrement
        (historyMeasure ⊗ₘ historyKernel) := by
      apply (hpairIncrementInt.indicator (hhistoryEvent.prod MeasurableSet.univ)).congr
      filter_upwards [] with historyPair
      by_cases hmem : historyPair.1 ∈ historyEvent
      · simp [weightedPairIncrement, weight, hmem]
      · simp [weightedPairIncrement, weight, hmem]
    have hweightedPairIncrementMap : Integrable weightedPairIncrement
        (Measure.map historyNext trajectory) := by
      rw [hhistoryLaw]
      exact hweightedPairIncrementInt
    have hpastWeighted : Measurable (fun past : (i : Finset.Iic n) → α =>
        weight past * pastRight past) := by
      simpa [weight, pastRight] using
        (measurable_const.indicator hhistoryEvent).mul (hmean.comp hlast)
    change (∫ path, weightedPairIncrement (historyNext path) ∂trajectory) =
      ∫ path, weight (history path) * right path ∂trajectory
    calc
      (∫ path, weightedPairIncrement (historyNext path) ∂trajectory) =
          ∫ historyPair, weightedPairIncrement historyPair ∂Measure.map historyNext trajectory := by
            symm
            exact integral_map hhistoryNext.aemeasurable
              hweightedPairIncrementMap.aestronglyMeasurable
      _ = ∫ historyPair, weightedPairIncrement historyPair ∂
          (historyMeasure ⊗ₘ historyKernel) := by rw [hhistoryLaw]
      _ = ∫ past, ∫ next, weightedPairIncrement (past, next) ∂historyKernel past
          ∂historyMeasure := by
            rw [Measure.integral_compProd hweightedPairIncrementInt]
      _ = ∫ past, weight past * pastRight past ∂historyMeasure := by
            apply integral_congr_ae
            filter_upwards [] with past
            by_cases hmem : past ∈ historyEvent
            · simp [weightedPairIncrement, weight, pairIncrement, pastRight, hmem]
              rw [hhistoryKernel_apply]
              exact hkernel (last past)
            · simp [weightedPairIncrement, weight, hmem]
      _ = ∫ path, weight (history path) * pastRight (history path) ∂trajectory := by
            exact integral_map hhistory.aemeasurable hpastWeighted.aestronglyMeasurable
      _ = ∫ path, weight (history path) * right path ∂trajectory := by rfl
  have hright_eq : right = pastRight ∘ history := by
    funext path
    rfl
  have hrightMeas : AEStronglyMeasurable[piLE n] right trajectory := by
    rw [hright_eq, piLE_eq_comap_frestrictLe]
    apply StronglyMeasurable.aestronglyMeasurable
    apply Measurable.stronglyMeasurable
    apply Measurable.of_comap_le
    rw [← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (hmean.comp hlast).comap_le
  change trajectory[increment | piLE n] =ᵐ[trajectory] right
  symm
  refine ae_eq_condExp_of_forall_setIntegral_eq (piLE.le n) hincrementInt
    (fun s _ _ => hrightInt.integrableOn) ?_ hrightMeas
  rintro s hs _
  rw [piLE_eq_comap_frestrictLe] at hs
  rcases hs with ⟨historyEvent, hhistoryEvent, rfl⟩
  have hEvent : MeasurableSet (history ⁻¹' historyEvent) :=
    hhistoryEvent.preimage hhistory
  rw [← integral_indicator hEvent, ← integral_indicator hEvent]
  calc
    ∫ path, (history ⁻¹' historyEvent).indicator right path ∂trajectory =
        ∫ path, historyEvent.indicator (fun _ => (1 : ℝ)) (history path) * right path
          ∂trajectory := by
            apply integral_congr_ae
            filter_upwards [] with path
            by_cases hmem : history path ∈ historyEvent <;>
              simp [Set.indicator, hmem]
    _ = ∫ path, historyEvent.indicator (fun _ => (1 : ℝ)) (history path) * increment path
          ∂trajectory := (hhistoryIntegral historyEvent hhistoryEvent).symm
    _ = ∫ path, (history ⁻¹' historyEvent).indicator increment path ∂trajectory := by
            apply integral_congr_ae
            filter_upwards [] with path
            by_cases hmem : history path ∈ historyEvent <;>
              simp [Set.indicator, hmem]


theorem stationaryTrajMeasure_zero_marginal
    {π : Measure α} [IsProbabilityMeasure π] {K : Kernel α α} [IsMarkovKernel K] :
    (stationaryTrajMeasure π K).map (fun x => x 0) = π := by
  unfold stationaryTrajMeasure Kernel.trajMeasure
  rw [Measure.map_comp _ _ (measurable_pi_apply _)]
  have hlast0 : Measurable (fun x : (i : Finset.Iic 0) → α =>
      x ⟨0, Finset.mem_Iic.mpr le_rfl⟩) := measurable_pi_apply _
  have hcoord :
      (Kernel.traj (homogeneousTrajKernel K) 0).map (fun x : ℕ → α => x 0) =
        Kernel.deterministic (fun x : (i : Finset.Iic 0) → α =>
          x ⟨0, Finset.mem_Iic.mpr le_rfl⟩) hlast0 := by
    have hfun : (fun x : ℕ → α => x 0) =
        (fun y : (i : Finset.Iic 0) → α =>
          y ⟨0, Finset.mem_Iic.mpr le_rfl⟩) ∘ Preorder.frestrictLe 0 := by
      funext x
      rfl
    rw [hfun, Kernel.map_comp_right _ (measurable_frestrictLe 0) hlast0,
      Kernel.traj_map_frestrictLe_of_le (X := fun _ : ℕ => α)
        (κ := homogeneousTrajKernel K) (a := 0) (b := 0) le_rfl]
    rw [Kernel.deterministic_map
      (f := Preorder.frestrictLe₂ (π := fun _ : ℕ => α) le_rfl)
      (g := fun y : (i : Finset.Iic 0) → α =>
        y ⟨0, Finset.mem_Iic.mpr le_rfl⟩)
      (measurable_frestrictLe₂ le_rfl) hlast0]
    rfl
  rw [hcoord, Measure.deterministic_comp_eq_map,
    Measure.map_map (measurable_pi_apply _)
      (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => α)).symm.measurable]
  convert (Measure.map_id (μ := π)) using 1

theorem stationaryTrajMeasure_marginal
    {π : Measure α} [IsProbabilityMeasure π] {K : Kernel α α} [IsMarkovKernel K]
    (hstationary : Kernel.Invariant K π) (n : ℕ) :
    (stationaryTrajMeasure π K).map (fun x => x n) = π := by
  induction n with
  | zero => exact stationaryTrajMeasure_zero_marginal
  | succ n ih =>
      rw [stationaryTrajMeasure_succ_marginal, ih, hstationary.def]

end AppliedModelingLib.Probability.Queueing
