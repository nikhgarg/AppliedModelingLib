import AppliedModelingLib.Queueing.MM1.Trajectory.Transition

/-!
# Finite-dimensional laws of homogeneous countable trajectories

This module extends the constructed Ionescu--Tulcea trajectory from adjacent
coordinates to a retained finite history and a later coordinate.  The results
are deterministic-index Markov laws.  In particular, they do not assert a
random time change, a stopping-time Markov property, or a path-space limit.
-/

namespace AppliedModelingLib.Probability.Queueing

open MeasureTheory ProbabilityTheory
open Preorder

noncomputable section

variable {α : Type*} [MeasurableSpace α]

/--
If a measure first samples a state from `L` and then one transition from `K`,
discarding the middle state gives the composition `K ∘ L` while retaining the
original input.  This is the heterogeneous-space form of the usual
two-transition composition law.
-/
theorem Measure.compProd_preserveFirst_step
    {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure β) [SFinite μ] (L : Kernel β α) (K : Kernel α γ)
    [IsSFiniteKernel L] [IsSFiniteKernel K] :
    ((μ ⊗ₘ L) ⊗ₘ K.prodMkLeft β).map
        (fun p : (β × α) × γ => (p.1.1, p.2)) =
      μ ⊗ₘ (K ∘ₖ L) := by
  let η : Kernel (β × α) γ := K.prodMkLeft β
  let q : (β × α) × γ → β × γ := fun p => (p.1.1, p.2)
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
          change μ ⊗ₘ ((L ⊗ₖ K.prodMkLeft β).map Prod.snd) = _
          rw [← Kernel.snd_eq, Kernel.snd_compProd_prodMkLeft]

/--
The law of a retained embedded history and a coordinate `m` transitions later
is obtained by applying the `m`-fold kernel power to the last state of that
history.  This is a deterministic-index finite-dimensional Markov law.
-/
theorem stationaryTrajMeasure_prefix_add
    {π : Measure α} [IsProbabilityMeasure π] {K : Kernel α α} [IsMarkovKernel K]
    (n m : ℕ) :
    let history : (ℕ → α) → (i : Finset.Iic n) → α := Preorder.frestrictLe n
    let terminal : ((i : Finset.Iic n) → α) → α :=
      fun y => y ⟨n, Finset.mem_Iic.mpr le_rfl⟩
    (stationaryTrajMeasure π K).map (fun x => (history x, x (n + m))) =
    (stationaryTrajMeasure π K).map history ⊗ₘ
        ((K ^ m) ∘ₖ Kernel.deterministic terminal (measurable_pi_apply _)) := by
  dsimp
  letI : IsProbabilityMeasure (stationaryTrajMeasure π K) := by
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsFiniteMeasure (stationaryTrajMeasure π K) := ⟨by
    rw [IsProbabilityMeasure.measure_univ]
    exact ENNReal.one_lt_top⟩
  induction m with
  | zero =>
      let history : (ℕ → α) → (i : Finset.Iic n) → α := Preorder.frestrictLe n
      let terminal : ((i : Finset.Iic n) → α) → α :=
        fun y => y ⟨n, Finset.mem_Iic.mpr le_rfl⟩
      let pair : ((i : Finset.Iic n) → α) → ((i : Finset.Iic n) → α) × α :=
        fun y => (y, terminal y)
      have hhistory : Measurable history := measurable_frestrictLe n
      have hterminal : Measurable terminal := measurable_pi_apply _
      have hpair : Measurable pair := measurable_id.prodMk hterminal
      calc
        (stationaryTrajMeasure π K).map (fun x => (history x, x (n + 0))) =
            ((stationaryTrajMeasure π K).map history).map pair := by
              rw [Measure.map_map hpair hhistory]
              rfl
        _ = (stationaryTrajMeasure π K).map history ⊗ₘ
            (Kernel.id ∘ₖ Kernel.deterministic terminal hterminal) := by
              rw [Kernel.id_comp, Measure.compProd_deterministic hterminal]
        _ = (stationaryTrajMeasure π K).map history ⊗ₘ
            ((K ^ 0) ∘ₖ Kernel.deterministic terminal hterminal) := by
              rfl
  | succ m ih =>
      let history : (ℕ → α) → (i : Finset.Iic n) → α := Preorder.frestrictLe n
      let terminal : ((i : Finset.Iic n) → α) → α :=
        fun y => y ⟨n, Finset.mem_Iic.mpr le_rfl⟩
      let extendedHistory : (ℕ → α) → (i : Finset.Iic (n + m)) → α :=
        Preorder.frestrictLe (n + m)
      let extendedTerminal : ((i : Finset.Iic (n + m)) → α) → α :=
        fun y => y ⟨n + m, Finset.mem_Iic.mpr le_rfl⟩
      let retainedPair : ((i : Finset.Iic (n + m)) → α) →
          ((i : Finset.Iic n) → α) × α :=
        fun y => ((fun i => y ⟨i.1, Finset.mem_Iic.mpr
          (show i.1 ≤ n + m from le_trans (Finset.mem_Iic.mp i.2) (Nat.le_add_right n m))⟩),
          extendedTerminal y)
      let retainedTriple : ((i : Finset.Iic (n + m)) → α) × α →
          (((i : Finset.Iic n) → α) × α) × α :=
        fun p => (retainedPair p.1, p.2)
      let discardMiddle : (((i : Finset.Iic n) → α) × α) × α →
          ((i : Finset.Iic n) → α) × α := fun p => (p.1.1, p.2)
      have hhistory : Measurable history := measurable_frestrictLe n
      have hterminal : Measurable terminal := measurable_pi_apply _
      have hextendedHistory : Measurable extendedHistory := measurable_frestrictLe (n + m)
      have hextendedTerminal : Measurable extendedTerminal := measurable_pi_apply _
      have hretainedPrefix : Measurable (fun y : (i : Finset.Iic (n + m)) → α =>
          fun i : Finset.Iic n => y ⟨i.1, Finset.mem_Iic.mpr
            (show i.1 ≤ n + m from le_trans (Finset.mem_Iic.mp i.2)
              (Nat.le_add_right n m))⟩) := by
        apply measurable_pi_lambda
        intro i
        exact measurable_pi_apply _
      have hretainedPair : Measurable retainedPair :=
        hretainedPrefix.prodMk hextendedTerminal
      have hretainedTriple : Measurable retainedTriple :=
        hretainedPair.comp measurable_fst |>.prodMk measurable_snd
      have hdiscardMiddle : Measurable discardMiddle :=
        measurable_fst.comp measurable_fst |>.prodMk measurable_snd
      have hrec := stationaryTrajMeasure_prefix_succ (π := π) (K := K) (n + m)
      have hkernel :
          K ∘ₖ Kernel.deterministic extendedTerminal hextendedTerminal =
            K ∘ₖ Kernel.deterministic (Prod.snd ∘ retainedPair)
              (measurable_snd.comp hretainedPair) := by
        apply Kernel.ext
        intro y
        rw [Kernel.comp_apply, Kernel.comp_apply]
        congr 1
      have hhistoryPair :
          ((stationaryTrajMeasure π K).map extendedHistory).map retainedPair =
            (stationaryTrajMeasure π K).map
              (fun x => (history x, x (n + m))) := by
        rw [Measure.map_map hretainedPair hextendedHistory]
        rfl
      have htripleLaw :
          (stationaryTrajMeasure π K).map
              (fun x => ((history x, x (n + m)), x (n + m + 1))) =
            ((stationaryTrajMeasure π K).map
              (fun x => (history x, x (n + m)))) ⊗ₘ K.prodMkLeft
                ((i : Finset.Iic n) → α) := by
        calc
          (stationaryTrajMeasure π K).map
              (fun x => ((history x, x (n + m)), x (n + m + 1))) =
              ((stationaryTrajMeasure π K).map
                (fun x => (extendedHistory x, x (n + m + 1)))).map retainedTriple := by
                  rw [Measure.map_map hretainedTriple
                    (hextendedHistory.prodMk (measurable_pi_apply _))]
                  rfl
          _ = ((stationaryTrajMeasure π K).map extendedHistory ⊗ₘ
              (K ∘ₖ Kernel.deterministic extendedTerminal hextendedTerminal)).map
                retainedTriple := by
                  rw [← hrec]
          _ = ((stationaryTrajMeasure π K).map extendedHistory ⊗ₘ
              (K ∘ₖ Kernel.deterministic (Prod.snd ∘ retainedPair)
                (measurable_snd.comp hretainedPair))).map retainedTriple := by
                  rw [hkernel]
          _ = ((stationaryTrajMeasure π K).map extendedHistory).map retainedPair ⊗ₘ
              (K ∘ₖ Kernel.deterministic Prod.snd measurable_snd) := by
                exact Measure.compProd_map_through _ K retainedPair hretainedPair
                  Prod.snd measurable_snd
          _ = ((stationaryTrajMeasure π K).map
              (fun x => (history x, x (n + m)))) ⊗ₘ K.prodMkLeft
                ((i : Finset.Iic n) → α) := by
                rw [hhistoryPair, Kernel.comp_deterministic_eq_comap]
                rfl
      calc
        (stationaryTrajMeasure π K).map (fun x => (history x, x (n + Nat.succ m))) =
            ((stationaryTrajMeasure π K).map
              (fun x => ((history x, x (n + m)), x (n + m + 1)))).map discardMiddle := by
                rw [Measure.map_map hdiscardMiddle
                  (((hhistory.prodMk (measurable_pi_apply _)).prodMk (measurable_pi_apply _)))]
                rfl
        _ = (((stationaryTrajMeasure π K).map
              (fun x => (history x, x (n + m)))) ⊗ₘ K.prodMkLeft
                ((i : Finset.Iic n) → α)).map discardMiddle := by
              rw [htripleLaw]
        _ = (((stationaryTrajMeasure π K).map history ⊗ₘ
              ((K ^ m) ∘ₖ Kernel.deterministic terminal hterminal)) ⊗ₘ
              K.prodMkLeft ((i : Finset.Iic n) → α)).map discardMiddle := by
              rw [ih]
        _ = (stationaryTrajMeasure π K).map history ⊗ₘ
              (K ∘ₖ ((K ^ m) ∘ₖ Kernel.deterministic terminal hterminal)) := by
              letI : IsSFiniteKernel (K ^ m) := isSFiniteKernel_pow K m
              exact Measure.compProd_preserveFirst_step _
                ((K ^ m) ∘ₖ Kernel.deterministic terminal hterminal) K
        _ = (stationaryTrajMeasure π K).map history ⊗ₘ
              ((K ^ Nat.succ m) ∘ₖ Kernel.deterministic terminal hterminal) := by
              have hpow : K ∘ₖ (K ^ m) = K ^ Nat.succ m := by
                simpa [Nat.add_comm] using (Kernel.pow_add K 1 m).symm
              rw [← Kernel.comp_assoc, hpow]

/--
At three deterministic embedded indices, a stationary homogeneous trajectory
factors into its `m`-step transition followed by its `l`-step transition.
The theorem is entirely discrete-time; independent clock mixing is a separate
operation.
-/
theorem stationaryTrajMeasure_triple_add_add
    {π : Measure α} [IsProbabilityMeasure π] {K : Kernel α α} [IsMarkovKernel K]
    (hstationary : Kernel.Invariant K π) (n m l : ℕ) :
    (stationaryTrajMeasure π K).map
        (fun x => ((x n, x (n + m)), x (n + m + l))) =
      (π ⊗ₘ (K ^ m)) ⊗ₘ (K ^ l).prodMkLeft α := by
  letI : IsProbabilityMeasure (stationaryTrajMeasure π K) := by
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsFiniteMeasure (stationaryTrajMeasure π K) := ⟨by
    rw [IsProbabilityMeasure.measure_univ]
    exact ENNReal.one_lt_top⟩
  letI : IsSFiniteKernel (K ^ l) := isSFiniteKernel_pow K l
  let history : (ℕ → α) → (i : Finset.Iic (n + m)) → α :=
    Preorder.frestrictLe (n + m)
  let terminal : ((i : Finset.Iic (n + m)) → α) → α :=
    fun y => y ⟨n + m, Finset.mem_Iic.mpr le_rfl⟩
  let retainedPair : ((i : Finset.Iic (n + m)) → α) → α × α :=
    fun y => (y ⟨n, Finset.mem_Iic.mpr (Nat.le_add_right n m)⟩, terminal y)
  let pairNext : ((i : Finset.Iic (n + m)) → α) × α → (α × α) × α :=
    fun p => (retainedPair p.1, p.2)
  have hhistory : Measurable history := measurable_frestrictLe (n + m)
  have hterminal : Measurable terminal := measurable_pi_apply _
  have hretainedPair : Measurable retainedPair :=
    (measurable_pi_apply _).prodMk hterminal
  have hpairNext : Measurable pairNext :=
    hretainedPair.comp measurable_fst |>.prodMk measurable_snd
  have hprefix := stationaryTrajMeasure_prefix_add (π := π) (K := K) (n + m) l
  have hkernel :
      (K ^ l) ∘ₖ Kernel.deterministic terminal hterminal =
        (K ^ l) ∘ₖ Kernel.deterministic (Prod.snd ∘ retainedPair)
          (measurable_snd.comp hretainedPair) := by
    apply Kernel.ext
    intro y
    rw [Kernel.comp_apply, Kernel.comp_apply]
    congr 1
  have hhistoryPair :
      ((stationaryTrajMeasure π K).map history).map retainedPair =
        (stationaryTrajMeasure π K).map (fun x => (x n, x (n + m))) := by
    rw [Measure.map_map hretainedPair hhistory]
    rfl
  calc
    (stationaryTrajMeasure π K).map
        (fun x => ((x n, x (n + m)), x (n + m + l))) =
        ((stationaryTrajMeasure π K).map
          (fun x => (history x, x (n + m + l)))).map pairNext := by
            rw [Measure.map_map hpairNext
              (hhistory.prodMk (measurable_pi_apply _))]
            rfl
    _ = ((stationaryTrajMeasure π K).map history ⊗ₘ
        ((K ^ l) ∘ₖ Kernel.deterministic terminal hterminal)).map pairNext := by
          rw [hprefix]
    _ = ((stationaryTrajMeasure π K).map history).map retainedPair ⊗ₘ
        ((K ^ l) ∘ₖ Kernel.deterministic Prod.snd measurable_snd) := by
          rw [hkernel]
          exact Measure.compProd_map_through _ (K ^ l) retainedPair hretainedPair
            Prod.snd measurable_snd
    _ = ((stationaryTrajMeasure π K).map
          (fun x => (x n, x (n + m)))) ⊗ₘ (K ^ l).prodMkLeft α := by
          rw [hhistoryPair, Kernel.comp_deterministic_eq_comap]
          rfl
    _ = (π ⊗ₘ (K ^ m)) ⊗ₘ (K ^ l).prodMkLeft α := by
          rw [stationaryTrajMeasure_pair_add hstationary n m]

/-- The initial coordinate and two later deterministic coordinates of a
homogeneous trajectory have the successive transition-kernel factorization.
Unlike the stationary-time version, this form needs no invariance assumption:
the first coordinate is the specified initial law. -/
theorem stationaryTrajMeasure_zero_add_add_triple
    {π : Measure α} [IsProbabilityMeasure π] {K : Kernel α α} [IsMarkovKernel K]
    (m l : ℕ) :
    (stationaryTrajMeasure π K).map
        (fun x => ((x 0, x m), x (m + l))) =
      (π ⊗ₘ (K ^ m)) ⊗ₘ (K ^ l).prodMkLeft α := by
  letI : IsProbabilityMeasure (stationaryTrajMeasure π K) := by
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsFiniteMeasure (stationaryTrajMeasure π K) := ⟨by
    rw [IsProbabilityMeasure.measure_univ]
    exact ENNReal.one_lt_top⟩
  letI : IsSFiniteKernel (K ^ l) := isSFiniteKernel_pow K l
  let history : (ℕ → α) → (i : Finset.Iic m) → α :=
    Preorder.frestrictLe m
  let terminal : ((i : Finset.Iic m) → α) → α :=
    fun y => y ⟨m, Finset.mem_Iic.mpr le_rfl⟩
  let retainedPair : ((i : Finset.Iic m) → α) → α × α :=
    fun y => (y ⟨0, Finset.mem_Iic.mpr (Nat.zero_le m)⟩, terminal y)
  let pairNext : ((i : Finset.Iic m) → α) × α → (α × α) × α :=
    fun p => (retainedPair p.1, p.2)
  have hhistory : Measurable history := measurable_frestrictLe m
  have hterminal : Measurable terminal := measurable_pi_apply _
  have hretainedPair : Measurable retainedPair :=
    (measurable_pi_apply _).prodMk hterminal
  have hpairNext : Measurable pairNext :=
    hretainedPair.comp measurable_fst |>.prodMk measurable_snd
  have hprefix := stationaryTrajMeasure_prefix_add (π := π) (K := K) m l
  have hkernel :
      (K ^ l) ∘ₖ Kernel.deterministic terminal hterminal =
        (K ^ l) ∘ₖ Kernel.deterministic (Prod.snd ∘ retainedPair)
          (measurable_snd.comp hretainedPair) := by
    apply Kernel.ext
    intro y
    rw [Kernel.comp_apply, Kernel.comp_apply]
    congr 1
  have hhistoryPair :
      ((stationaryTrajMeasure π K).map history).map retainedPair =
        (stationaryTrajMeasure π K).map (fun x => (x 0, x m)) := by
    rw [Measure.map_map hretainedPair hhistory]
    rfl
  calc
    (stationaryTrajMeasure π K).map
        (fun x => ((x 0, x m), x (m + l))) =
        ((stationaryTrajMeasure π K).map
          (fun x => (history x, x (m + l)))).map pairNext := by
            rw [Measure.map_map hpairNext
              (hhistory.prodMk (measurable_pi_apply _))]
            rfl
    _ = ((stationaryTrajMeasure π K).map history ⊗ₘ
        ((K ^ l) ∘ₖ Kernel.deterministic terminal hterminal)).map pairNext := by
          rw [hprefix]
    _ = ((stationaryTrajMeasure π K).map history).map retainedPair ⊗ₘ
        ((K ^ l) ∘ₖ Kernel.deterministic Prod.snd measurable_snd) := by
          rw [hkernel]
          exact Measure.compProd_map_through _ (K ^ l) retainedPair hretainedPair
            Prod.snd measurable_snd
    _ = ((stationaryTrajMeasure π K).map
          (fun x => (x 0, x m))) ⊗ₘ (K ^ l).prodMkLeft α := by
          rw [hhistoryPair, Kernel.comp_deterministic_eq_comap]
          rfl
    _ = (π ⊗ₘ (K ^ m)) ⊗ₘ (K ^ l).prodMkLeft α := by
          rw [stationaryTrajMeasure_zero_n_pair m]

end

end AppliedModelingLib.Probability.Queueing
