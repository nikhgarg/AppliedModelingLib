import AppliedModelingLib.Queueing.MM1.Trajectory
import Mathlib.Probability.HasLaw

/-!
# Transition laws of stationary embedded M/M/1 trajectories

This module strengthens the Ionescu--Tulcea stationary-trajectory construction
from one-coordinate marginals to its exact prefix-to-next recurrence,
stationary consecutive-pair law, and the initial/`n`-step pair law.  It remains
a discrete jump-index result: external-clock mixing lives in the time-change
module, and neither continuous-time semigroup identification nor a Palm
arrival construction is made here.
-/

open scoped ENNReal NNReal

open MeasureTheory ProbabilityTheory
open Preorder

namespace AppliedModelingLib.Probability.Queueing

variable {α : Type*} [MeasurableSpace α]

/-- Finite powers of an s-finite transition kernel remain s-finite. -/
theorem isSFiniteKernel_pow
    (K : Kernel α α) [IsSFiniteKernel K] (n : ℕ) :
    IsSFiniteKernel (K ^ n) := by
  induction n with
  | zero =>
      change IsSFiniteKernel Kernel.id
      infer_instance
  | succ n ih =>
      have hpow : K ^ (n + 1) = (K ^ n) ∘ₖ K := by
        simpa using Kernel.pow_add K n 1
      rw [show K ^ Nat.succ n = (K ^ n) ∘ₖ K by simpa using hpow]
      letI : IsSFiniteKernel (K ^ n) := ih
      infer_instance

/-- Map the retained first coordinate of a composition product through `f`,
while the next-state kernel reads `g (f x)`. -/
theorem Measure.compProd_map_through
    {β δ γ : Type*} [MeasurableSpace β] [MeasurableSpace δ]
    [MeasurableSpace γ]
    (ν : Measure β) [SFinite ν] (K : Kernel α γ) [IsSFiniteKernel K]
    (f : β → δ) (hf : Measurable f) (g : δ → α) (hg : Measurable g) :
    (ν ⊗ₘ (K ∘ₖ Kernel.deterministic (g ∘ f) (hg.comp hf))).map
        (fun p : β × γ => (f p.1, p.2)) =
      (ν.map f) ⊗ₘ (K ∘ₖ Kernel.deterministic g hg) := by
  simpa only [Kernel.comp_assoc, Kernel.deterministic_comp_deterministic] using
    (Measure.compProd_map_input (α := δ) ν
      (K ∘ₖ Kernel.deterministic g hg) f hf)

/-- The joint law of the initial state, the state at jump `n`, and its next
state satisfies the Markov recurrence with transition kernel acting on the
second coordinate. -/
theorem stationaryTrajMeasure_zero_pair_succ_recurrence
    {π : Measure α} [IsProbabilityMeasure π] {K : Kernel α α} [IsMarkovKernel K]
    (n : ℕ) :
    (stationaryTrajMeasure π K).map (fun x => ((x 0, x n), x (n + 1))) =
      (stationaryTrajMeasure π K).map (fun x => (x 0, x n)) ⊗ₘ
        (K ∘ₖ Kernel.deterministic Prod.snd measurable_snd) := by
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
    fun y => y ⟨n, Finset.mem_Iic.mpr le_rfl⟩
  let initialAndLast : ((i : Finset.Iic n) → α) → α × α :=
    fun y => (y ⟨0, Finset.mem_Iic.mpr (zero_le n)⟩,
      y ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
  let historyNext : (ℕ → α) → ((i : Finset.Iic n) → α) × α :=
    fun x => (hist x, x (n + 1))
  let pairNext : (ℕ → α) → (α × α) × α :=
    fun x => ((x 0, x n), x (n + 1))
  let mapHistoryNext : ((i : Finset.Iic n) → α) × α → (α × α) × α :=
    fun p => (initialAndLast p.1, p.2)
  have hhist : Measurable hist := measurable_frestrictLe n
  have hinitialAndLast : Measurable initialAndLast :=
    (measurable_pi_apply _).prodMk (measurable_pi_apply _)
  have hhistoryNext : Measurable historyNext := hhist.prodMk (measurable_pi_apply _)
  have hmapHistoryNext : Measurable mapHistoryNext :=
    hinitialAndLast.comp measurable_fst |>.prodMk measurable_snd
  have hrec := stationaryTrajMeasure_prefix_succ (π := π) (K := K) n
  calc
    (stationaryTrajMeasure π K).map pairNext =
        ((stationaryTrajMeasure π K).map historyNext).map mapHistoryNext := by
      rw [Measure.map_map hmapHistoryNext hhistoryNext]
      rfl
    _ =
        ((stationaryTrajMeasure π K).map hist ⊗ₘ
          (K ∘ₖ Kernel.deterministic lastState (measurable_pi_apply _))).map
            mapHistoryNext := by
      rw [hrec]
    _ = ((stationaryTrajMeasure π K).map hist).map initialAndLast ⊗ₘ
        (K ∘ₖ Kernel.deterministic Prod.snd measurable_snd) := by
      exact Measure.compProd_map_through _ K initialAndLast hinitialAndLast
        Prod.snd measurable_snd
    _ = (stationaryTrajMeasure π K).map (fun x => (x 0, x n)) ⊗ₘ
        (K ∘ₖ Kernel.deterministic Prod.snd measurable_snd) := by
      rw [Measure.map_map hinitialAndLast hhist]
      rfl

/-- The pair formed by two deterministic embedded jump indices and the state
at the successor of the second index has the one-step Markov recurrence at
the second index.  This is the reusable deterministic-index form needed when
an independent clock is subsequently introduced; it makes no random-index or
continuous-time Markov assertion. -/
theorem stationaryTrajMeasure_pair_succ_recurrence
    {π : Measure α} [IsProbabilityMeasure π] {K : Kernel α α} [IsMarkovKernel K]
    (i j : ℕ) (hij : i ≤ j) :
    (stationaryTrajMeasure π K).map (fun x => ((x i, x j), x (j + 1))) =
      (stationaryTrajMeasure π K).map (fun x => (x i, x j)) ⊗ₘ
        (K ∘ₖ Kernel.deterministic Prod.snd measurable_snd) := by
  letI (k : ℕ) : IsMarkovKernel (homogeneousTrajKernel K k) :=
    homogeneousTrajKernel.isMarkovKernel K k
  have hprob : IsProbabilityMeasure (stationaryTrajMeasure π K) := by
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsProbabilityMeasure (stationaryTrajMeasure π K) := hprob
  letI : IsFiniteMeasure (stationaryTrajMeasure π K) := ⟨by
    rw [IsProbabilityMeasure.measure_univ]
    exact ENNReal.one_lt_top⟩
  let hist : (ℕ → α) → (k : Finset.Iic j) → α := Preorder.frestrictLe j
  let lastState : ((k : Finset.Iic j) → α) → α :=
    fun y => y ⟨j, Finset.mem_Iic.mpr le_rfl⟩
  let firstAndLast : ((k : Finset.Iic j) → α) → α × α :=
    fun y => (y ⟨i, Finset.mem_Iic.mpr hij⟩,
      y ⟨j, Finset.mem_Iic.mpr le_rfl⟩)
  let historyNext : (ℕ → α) → ((k : Finset.Iic j) → α) × α :=
    fun x => (hist x, x (j + 1))
  let pairNext : (ℕ → α) → (α × α) × α :=
    fun x => ((x i, x j), x (j + 1))
  let mapHistoryNext : ((k : Finset.Iic j) → α) × α → (α × α) × α :=
    fun p => (firstAndLast p.1, p.2)
  have hhist : Measurable hist := measurable_frestrictLe j
  have hfirstAndLast : Measurable firstAndLast :=
    (measurable_pi_apply _).prodMk (measurable_pi_apply _)
  have hhistoryNext : Measurable historyNext := hhist.prodMk (measurable_pi_apply _)
  have hmapHistoryNext : Measurable mapHistoryNext :=
    hfirstAndLast.comp measurable_fst |>.prodMk measurable_snd
  have hrec := stationaryTrajMeasure_prefix_succ (π := π) (K := K) j
  calc
    (stationaryTrajMeasure π K).map pairNext =
        ((stationaryTrajMeasure π K).map historyNext).map mapHistoryNext := by
      rw [Measure.map_map hmapHistoryNext hhistoryNext]
      rfl
    _ =
        ((stationaryTrajMeasure π K).map hist ⊗ₘ
          (K ∘ₖ Kernel.deterministic lastState (measurable_pi_apply _))).map
            mapHistoryNext := by
      rw [hrec]
    _ = ((stationaryTrajMeasure π K).map hist).map firstAndLast ⊗ₘ
        (K ∘ₖ Kernel.deterministic Prod.snd measurable_snd) := by
      exact Measure.compProd_map_through _ K firstAndLast hfirstAndLast
        Prod.snd measurable_snd
    _ = (stationaryTrajMeasure π K).map (fun x => (x i, x j)) ⊗ₘ
        (K ∘ₖ Kernel.deterministic Prod.snd measurable_snd) := by
      rw [Measure.map_map hfirstAndLast hhist]
      rfl

/-- Advancing the second coordinate of a pair through one transition composes
the pair's transition kernel. -/
theorem Measure.compProd_pair_step
    (μ : Measure α) [SFinite μ] (L K : Kernel α α)
    [IsSFiniteKernel L] [IsSFiniteKernel K] :
    ((μ ⊗ₘ L) ⊗ₘ K.prodMkLeft α).map
        (fun p : (α × α) × α => (p.1.1, p.2)) =
      μ ⊗ₘ (K ∘ₖ L) := by
  let η : Kernel (α × α) α := K.prodMkLeft α
  let q : (α × α) × α → α × α := fun p => (p.1.1, p.2)
  have hq : Measurable q := measurable_fst.comp measurable_fst |>.prodMk measurable_snd
  calc
    ((μ ⊗ₘ L) ⊗ₘ η).map q =
        ((μ ⊗ₘ (L ⊗ₖ η)).map MeasurableEquiv.prodAssoc.symm).map q := by
      rw [Measure.compProd_assoc]
    _ = (μ ⊗ₘ (L ⊗ₖ η)).map (Prod.map id Prod.snd) := by
      rw [Measure.map_map hq MeasurableEquiv.prodAssoc.symm.measurable]
      rfl
    _ = μ ⊗ₘ ((L ⊗ₖ η).map Prod.snd) := by
      rw [← Measure.compProd_map (μ := μ) (κ := L ⊗ₖ η) measurable_snd]
    _ = μ ⊗ₘ (K ∘ₖ L) := by
      change μ ⊗ₘ ((L ⊗ₖ K.prodMkLeft α).map Prod.snd) = _
      rw [← Kernel.snd_eq, Kernel.snd_compProd_prodMkLeft]

/-- The initial state and the state after `n` embedded transitions have the
joint law obtained by starting at `π` and applying the `n`-fold kernel power.
No invariance hypothesis is needed: `π` is the initial law in this statement. -/
theorem stationaryTrajMeasure_zero_n_pair
    {π : Measure α} [IsProbabilityMeasure π] {K : Kernel α α} [IsMarkovKernel K]
    (n : ℕ) :
    (stationaryTrajMeasure π K).map (fun x => (x 0, x n)) = π ⊗ₘ (K ^ n) := by
  induction n with
  | zero =>
      let diagonal : α → α × α := fun a => (a, a)
      have hdiagonal : Measurable diagonal := measurable_id.prodMk measurable_id
      calc
        (stationaryTrajMeasure π K).map (fun x => (x 0, x 0)) =
            ((stationaryTrajMeasure π K).map (fun x => x 0)).map diagonal := by
          rw [Measure.map_map hdiagonal (measurable_pi_apply _)]
          rfl
        _ = π.map diagonal := by rw [stationaryTrajMeasure_zero_marginal]
        _ = π ⊗ₘ Kernel.id := by rw [Measure.compProd_id]
        _ = π ⊗ₘ (K ^ 0) := by
          rw [pow_zero]
          rfl
  | succ n ih =>
      letI : IsSFiniteKernel (K ^ n) := isSFiniteKernel_pow K n
      let q : (α × α) × α → α × α := fun p => (p.1.1, p.2)
      let triple : (ℕ → α) → (α × α) × α :=
        fun x => ((x 0, x n), x (n + 1))
      let pairSucc : (ℕ → α) → α × α := fun x => (x 0, x (n + 1))
      have hq : Measurable q := measurable_fst.comp measurable_fst |>.prodMk measurable_snd
      have htriple : Measurable triple :=
        ((measurable_pi_apply _).prodMk (measurable_pi_apply _)).prodMk
          (measurable_pi_apply _)
      have hKprod :
          K ∘ₖ Kernel.deterministic Prod.snd measurable_snd = K.prodMkLeft α := by
        rw [Kernel.comp_deterministic_eq_comap]
        rfl
      calc
        (stationaryTrajMeasure π K).map pairSucc =
            ((stationaryTrajMeasure π K).map triple).map q := by
          rw [Measure.map_map hq htriple]
          rfl
        _ = ((stationaryTrajMeasure π K).map (fun x => (x 0, x n)) ⊗ₘ
            (K ∘ₖ Kernel.deterministic Prod.snd measurable_snd)).map q := by
          rw [stationaryTrajMeasure_zero_pair_succ_recurrence]
        _ = ((stationaryTrajMeasure π K).map (fun x => (x 0, x n)) ⊗ₘ
            K.prodMkLeft α).map q := by rw [hKprod]
        _ = (π ⊗ₘ (K ^ n) ⊗ₘ K.prodMkLeft α).map q := by rw [ih]
        _ = π ⊗ₘ (K ∘ₖ (K ^ n)) := by
          simpa [q] using (Measure.compProd_pair_step π (K ^ n) K)
        _ = π ⊗ₘ (K ^ (n + 1)) := by
          simpa [Nat.add_comm] using congrArg (fun L : Kernel α α => π ⊗ₘ L)
            (Kernel.pow_add K 1 n).symm

/-- Law form of `stationaryTrajMeasure_zero_n_pair`.  This remains an
embedded-chain statement, rather than a continuous-time or Palm statement. -/
theorem stationaryTrajMeasure_zero_n_pair_hasLaw
    {π : Measure α} [IsProbabilityMeasure π] {K : Kernel α α} [IsMarkovKernel K]
    (n : ℕ) :
    HasLaw (fun x : ℕ → α => (x 0, x n)) (π ⊗ₘ (K ^ n))
      (stationaryTrajMeasure π K) := by
  refine ⟨?_, stationaryTrajMeasure_zero_n_pair n⟩
  exact ((measurable_pi_apply _).prodMk (measurable_pi_apply _)).aemeasurable

/-- Every consecutive pair in the Ionescu--Tulcea trajectory has the
stationary one-step law `π ⊗ₘ K`.  Thus invariance of the initial law is
propagated not only to individual coordinates, but to the state/next-state
coupling at every time. -/
theorem stationaryTrajMeasure_consecutivePair
    {π : Measure α} [IsProbabilityMeasure π] {K : Kernel α α} [IsMarkovKernel K]
    (hstationary : Kernel.Invariant K π) (n : ℕ) :
    (stationaryTrajMeasure π K).map (fun x => (x n, x (n + 1))) = (π ⊗ₘ K) := by
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
    fun p => (lastState p.1, p.2)
  have hhist : Measurable hist := measurable_frestrictLe n
  have hlastState : Measurable lastState := measurable_pi_apply _
  have hhistoryNext : Measurable historyNext := hhist.prodMk (measurable_pi_apply _)
  have hpairFromHistory : Measurable pairFromHistory :=
    hlastState.comp measurable_fst |>.prodMk measurable_snd
  have hrec := stationaryTrajMeasure_prefix_succ (π := π) (K := K) n
  have hlastMarginal :
      ((stationaryTrajMeasure π K).map hist).map lastState = π := by
    rw [Measure.map_map hlastState hhist]
    change (stationaryTrajMeasure π K).map (fun x => x n) = π
    exact stationaryTrajMeasure_marginal hstationary n
  calc
    (stationaryTrajMeasure π K).map statePair =
        ((stationaryTrajMeasure π K).map historyNext).map pairFromHistory := by
      rw [Measure.map_map hpairFromHistory hhistoryNext]
      rfl
    _ =
        ((stationaryTrajMeasure π K).map hist ⊗ₘ
          (K ∘ₖ Kernel.deterministic lastState hlastState)).map pairFromHistory := by
      rw [hrec]
    _ = (((stationaryTrajMeasure π K).map hist).map lastState ⊗ₘ K) := by
      exact Measure.compProd_map_input _ K lastState hlastState
    _ = (π ⊗ₘ K) := by rw [hlastMarginal]

/-- Under an invariant initial law, every deterministic pair of embedded
indices `n` and `n + m` has the stationary `m`-step transition law.  The
indices are deterministic in this theorem; random clock mixtures require a
separate independence argument. -/
theorem stationaryTrajMeasure_pair_add
    {π : Measure α} [IsProbabilityMeasure π] {K : Kernel α α} [IsMarkovKernel K]
    (hstationary : Kernel.Invariant K π) (n m : ℕ) :
    (stationaryTrajMeasure π K).map (fun x => (x n, x (n + m))) = π ⊗ₘ (K ^ m) := by
  induction m with
  | zero =>
      let diagonal : α → α × α := fun a => (a, a)
      have hdiagonal : Measurable diagonal := measurable_id.prodMk measurable_id
      calc
        (stationaryTrajMeasure π K).map (fun x => (x n, x (n + 0))) =
            ((stationaryTrajMeasure π K).map (fun x => x n)).map diagonal := by
          rw [Measure.map_map hdiagonal (measurable_pi_apply _)]
          rfl
        _ = π.map diagonal := by rw [stationaryTrajMeasure_marginal hstationary n]
        _ = π ⊗ₘ Kernel.id := by rw [Measure.compProd_id]
        _ = π ⊗ₘ (K ^ 0) := by
          rw [pow_zero]
          rfl
  | succ m ih =>
      letI : IsSFiniteKernel (K ^ m) := isSFiniteKernel_pow K m
      let q : (α × α) × α → α × α := fun p => (p.1.1, p.2)
      let triple : (ℕ → α) → (α × α) × α :=
        fun x => ((x n, x (n + m)), x (n + m + 1))
      let pairSucc : (ℕ → α) → α × α := fun x => (x n, x (n + (m + 1)))
      have hq : Measurable q := measurable_fst.comp measurable_fst |>.prodMk measurable_snd
      have htriple : Measurable triple :=
        ((measurable_pi_apply _).prodMk (measurable_pi_apply _)).prodMk
          (measurable_pi_apply _)
      have hKprod :
          K ∘ₖ Kernel.deterministic Prod.snd measurable_snd = K.prodMkLeft α := by
        rw [Kernel.comp_deterministic_eq_comap]
        rfl
      calc
        (stationaryTrajMeasure π K).map pairSucc =
            ((stationaryTrajMeasure π K).map triple).map q := by
          rw [Measure.map_map hq htriple]
          rfl
        _ = ((stationaryTrajMeasure π K).map (fun x => (x n, x (n + m))) ⊗ₘ
            (K ∘ₖ Kernel.deterministic Prod.snd measurable_snd)).map q := by
          rw [stationaryTrajMeasure_pair_succ_recurrence n (n + m) (Nat.le_add_right n m)]
        _ = ((stationaryTrajMeasure π K).map (fun x => (x n, x (n + m))) ⊗ₘ
            K.prodMkLeft α).map q := by rw [hKprod]
        _ = (π ⊗ₘ (K ^ m) ⊗ₘ K.prodMkLeft α).map q := by rw [ih]
        _ = π ⊗ₘ (K ∘ₖ (K ^ m)) := by
          simpa [q] using (Measure.compProd_pair_step π (K ^ m) K)
        _ = π ⊗ₘ (K ^ (m + 1)) := by
          simpa [Nat.add_comm] using congrArg (fun L : Kernel α α => π ⊗ₘ L)
            (Kernel.pow_add K 1 m).symm

/--
At three deterministic embedded indices, a stationary trajectory has the
ordinary Markov factorization: after the `m`-step transition from `n` to
`n + m`, one further transition reads only the second state.  This is a
finite-dimensional discrete-time statement and makes no random-index,
continuous-time, or stopping-time assertion.
-/
theorem stationaryTrajMeasure_pair_add_succ_factor
    {π : Measure α} [IsProbabilityMeasure π] {K : Kernel α α} [IsMarkovKernel K]
    (hstationary : Kernel.Invariant K π) (n m : ℕ) :
    (stationaryTrajMeasure π K).map
        (fun x => ((x n, x (n + m)), x (n + m + 1))) =
      (π ⊗ₘ (K ^ m)) ⊗ₘ K.prodMkLeft α := by
  have hKprod :
      K ∘ₖ Kernel.deterministic Prod.snd measurable_snd = K.prodMkLeft α := by
    rw [Kernel.comp_deterministic_eq_comap]
    rfl
  calc
    (stationaryTrajMeasure π K).map
        (fun x => ((x n, x (n + m)), x (n + m + 1))) =
        (stationaryTrajMeasure π K).map (fun x => (x n, x (n + m))) ⊗ₘ
          (K ∘ₖ Kernel.deterministic Prod.snd measurable_snd) := by
            exact stationaryTrajMeasure_pair_succ_recurrence n (n + m)
              (Nat.le_add_right n m)
    _ = (stationaryTrajMeasure π K).map (fun x => (x n, x (n + m))) ⊗ₘ
          K.prodMkLeft α := by rw [hKprod]
    _ = (π ⊗ₘ (K ^ m)) ⊗ₘ K.prodMkLeft α := by
          rw [stationaryTrajMeasure_pair_add hstationary n m]

/-- For the stable uniformized M/M/1 jump chain, every adjacent pair on the
constructed stationary embedded trajectory has the geometric-state / one-step
transition coupling, independently of the jump index. -/
theorem geoNNPMF_uniformized_stationaryTraj_consecutivePair
    (rho : ℝ≥0) (hrho : rho < 1) (n : ℕ) :
    (stationaryTrajMeasure
      (geoNNPMF rho hrho).toMeasure
      (countablePMFKernel
        (reflectedBirthDeathKernel
          (uniformizedBirthProbability rho)
          (uniformizedBirthProbability_le_one rho)))).map
        (fun x => (x n, x (n + 1))) =
      ((geoNNPMF rho hrho).toMeasure ⊗ₘ
        (countablePMFKernel
          (reflectedBirthDeathKernel
            (uniformizedBirthProbability rho)
            (uniformizedBirthProbability_le_one rho)))) := by
  exact stationaryTrajMeasure_consecutivePair
    (geoNNPMF_uniformized_kernelInvariant rho hrho) n

/-- Rate-specialized form of the exact stationary adjacent-pair law for the
uniformized stable M/M/1 embedded chain. -/
theorem mm1_uniformized_stationaryTraj_consecutivePair
    (arrivalRate serviceRate : ℝ≥0) (hstable : arrivalRate < serviceRate)
    (n : ℕ) :
    (stationaryTrajMeasure
      (geoNNPMF (mm1TrafficIntensityNN arrivalRate serviceRate)
        (mm1TrafficIntensityNN_lt_one hstable)).toMeasure
      (countablePMFKernel
        (reflectedBirthDeathKernel
          (arrivalRate / (arrivalRate + serviceRate))
          (rate_fraction_le_one arrivalRate serviceRate)))).map
        (fun x => (x n, x (n + 1))) =
      (geoNNPMF (mm1TrafficIntensityNN arrivalRate serviceRate)
        (mm1TrafficIntensityNN_lt_one hstable)).toMeasure ⊗ₘ
        countablePMFKernel
          (reflectedBirthDeathKernel
            (arrivalRate / (arrivalRate + serviceRate))
            (rate_fraction_le_one arrivalRate serviceRate)) := by
  exact stationaryTrajMeasure_consecutivePair
    (mm1_uniformized_geometric_stationary arrivalRate serviceRate hstable).kernelInvariant n

end AppliedModelingLib.Probability.Queueing
