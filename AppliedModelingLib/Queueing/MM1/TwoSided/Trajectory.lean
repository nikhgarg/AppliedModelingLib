import AppliedModelingLib.Queueing.MM1.Trajectory.Transition
import Mathlib.Probability.Kernel.Invariance

/-!
# Two-sided reversible M/M/1 embedded trajectories

This module constructs a genuine integer-indexed *embedded discrete-time*
trajectory from a stationary state at zero and conditionally independent
Ionescu--Tulcea tails.  Under detailed balance, its negative/cross-zero pair
has the same law as a forward stationary transition pair.

## Deliberate scope boundary

This is not a stationary/Palm tagged-arrival construction.  In particular, it
does not introduce a continuous-time arrival process, Poisson clocks, or a
Palm conditioning law, and it does not prove PASTA or a response-tail theorem.
It also proves coordinate marginals and a cross-zero pair law only; it does
not prove full finite-dimensional invariance under every integer shift.
-/

namespace AppliedModelingLib.Probability.Queueing

open MeasureTheory ProbabilityTheory Preorder

noncomputable section

variable {α : Type*} [MeasurableSpace α]

/-- Constant past history used to initialize the one-sided Ionescu--Tulcea trajectory at a
specified state. -/
def zeroHistory (x : α) : (i : Finset.Iic 0) → α := fun _ => x

theorem measurable_zeroHistory : Measurable (zeroHistory (α := α)) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_id

/-- Kernel of a forward trajectory conditional on its time-zero state. -/
noncomputable def conditionalHomogeneousTrajKernel (K : Kernel α α)
    [IsMarkovKernel K] : Kernel α (ℕ → α) :=
  (Kernel.traj (homogeneousTrajKernel K) 0) ∘ₖ
    Kernel.deterministic zeroHistory (measurable_zeroHistory (α := α))

instance (K : Kernel α α) [IsMarkovKernel K] :
    IsMarkovKernel (conditionalHomogeneousTrajKernel K) := by
  unfold conditionalHomogeneousTrajKernel
  infer_instance

/-- Integrating the conditional trajectory kernel against `π` gives the existing stationary
one-sided trajectory measure. -/
theorem conditionalHomogeneousTrajKernel_comp_eq_stationaryTrajMeasure
    {π : Measure α} {K : Kernel α α} [IsMarkovKernel K] :
    conditionalHomogeneousTrajKernel K ∘ₘ π = stationaryTrajMeasure π K := by
  unfold conditionalHomogeneousTrajKernel stationaryTrajMeasure Kernel.trajMeasure
  rw [← Measure.comp_assoc, Measure.deterministic_comp_eq_map]
  have hhistory : zeroHistory (α := α) =
      (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => α)).symm := by
    funext x i
    simp [zeroHistory]
  rw [hhistory]

/-- Given the state at zero, generate independent positive-time and reverse-time tails. -/
noncomputable def conditionalIndependentTwoTailsKernel (K : Kernel α α)
    [IsMarkovKernel K] : Kernel α ((ℕ → α) × (ℕ → α)) :=
  conditionalHomogeneousTrajKernel K ×ₖ conditionalHomogeneousTrajKernel K

instance (K : Kernel α α) [IsMarkovKernel K] :
    IsMarkovKernel (conditionalIndependentTwoTailsKernel K) := by
  unfold conditionalIndependentTwoTailsKernel
  infer_instance

/-- The second tail advances by `K` after one reverse-time step. -/
theorem conditionalIndependentTwoTailsKernel_map_past_one
    {K : Kernel α α} [IsMarkovKernel K] :
    (conditionalIndependentTwoTailsKernel K).map (fun z => z.2 1) = K := by
  calc
    (conditionalIndependentTwoTailsKernel K).map (fun z => z.2 1) =
        ((conditionalIndependentTwoTailsKernel K).map Prod.snd).map
          (fun x => x 1) := by
      simpa [Function.comp_def] using
        (Kernel.map_comp_right (conditionalIndependentTwoTailsKernel K)
          measurable_snd (measurable_pi_apply 1))
    _ = ((conditionalIndependentTwoTailsKernel K).snd).map (fun x => x 1) := by
      rw [Kernel.snd_eq]
    _ = (conditionalHomogeneousTrajKernel K).map (fun x => x 1) := by
      unfold conditionalIndependentTwoTailsKernel
      rw [Kernel.snd_prod]
    _ = K := by
      unfold conditionalHomogeneousTrajKernel
      rw [Kernel.map_comp, Kernel.map_traj_succ_self]
      unfold homogeneousTrajKernel
      rw [Kernel.comp_assoc]
      rw [Kernel.deterministic_comp_deterministic
        (measurable_zeroHistory (α := α)) (measurable_pi_apply _)]
      simpa [zeroHistory, Function.comp_def, Kernel.id] using (Kernel.comp_id K)

theorem conditionalIndependentTwoTailsKernel_map_past_one_comp
    {K : Kernel α α} [IsMarkovKernel K] :
    (conditionalIndependentTwoTailsKernel K).map
      ((fun x : ℕ → α => x 1) ∘ Prod.snd) = K := by
  simpa [Function.comp_def] using conditionalIndependentTwoTailsKernel_map_past_one (K := K)

/-- The joint source law of time zero and its two conditional tails. -/
noncomputable def stateAndIndependentTailsMeasure (π : Measure α) (K : Kernel α α)
    [IsMarkovKernel K] : Measure (α × ((ℕ → α) × (ℕ → α))) :=
  π ⊗ₘ conditionalIndependentTwoTailsKernel K

/-- Splice a state at zero, a positive-time tail, and a reverse-time tail into an integer path. -/
def spliceStateAndTails (z : α × ((ℕ → α) × (ℕ → α))) : ℤ → α
  | Int.ofNat 0 => z.1
  | Int.ofNat (n + 1) => z.2.1 (n + 1)
  | Int.negSucc n => z.2.2 (n + 1)

theorem measurable_spliceStateAndTails : Measurable (spliceStateAndTails (α := α)) := by
  apply measurable_pi_lambda
  intro i
  cases i with
  | ofNat n =>
      cases n with
      | zero => exact measurable_fst
      | succ n =>
          exact (measurable_pi_apply (n + 1)).comp
            (measurable_fst.comp measurable_snd)
  | negSucc n =>
      exact (measurable_pi_apply (n + 1)).comp
        (measurable_snd.comp measurable_snd)

/-- A genuine state-anchored measure on integer-indexed embedded trajectories. -/
noncomputable def reversibleStateAnchoredTwoSidedTrajMeasure (π : Measure α) (K : Kernel α α)
    [IsMarkovKernel K] : Measure (ℤ → α) :=
  (stateAndIndependentTailsMeasure π K).map spliceStateAndTails

/-- Projecting the source construction onto its distinguished time-zero state recovers `π`. -/
theorem stateAndIndependentTailsMeasure_map_zero
    {π : Measure α} [IsProbabilityMeasure π] {K : Kernel α α} [IsMarkovKernel K] :
    (stateAndIndependentTailsMeasure π K).map Prod.fst = π := by
  unfold stateAndIndependentTailsMeasure
  rw [Measure.compProd_eq_comp_prod, Measure.map_comp π _ measurable_fst,
    ← Kernel.fst_eq, Kernel.fst_prod, Measure.id_comp]

/-- The positive-time tail, after integrating out time zero, is the stationary one-sided
trajectory law. -/
theorem stateAndIndependentTailsMeasure_map_futureTail
    {π : Measure α} [IsProbabilityMeasure π] {K : Kernel α α} [IsMarkovKernel K] :
    (stateAndIndependentTailsMeasure π K).map (fun z => z.2.1) = stationaryTrajMeasure π K := by
  calc
    (stateAndIndependentTailsMeasure π K).map (fun z => z.2.1) =
        ((stateAndIndependentTailsMeasure π K).map Prod.snd).map Prod.fst := by
      symm
      rw [Measure.map_map measurable_fst measurable_snd]
      rfl
    _ = (conditionalIndependentTwoTailsKernel K ∘ₘ π).map Prod.fst := by
      unfold stateAndIndependentTailsMeasure
      rw [Measure.compProd_eq_comp_prod, Measure.map_comp π _ measurable_snd,
        ← Kernel.snd_eq, Kernel.snd_prod]
    _ = stationaryTrajMeasure π K := by
      rw [Measure.map_comp π _ measurable_fst, ← Kernel.fst_eq]
      unfold conditionalIndependentTwoTailsKernel
      rw [Kernel.fst_prod]
      exact conditionalHomogeneousTrajKernel_comp_eq_stationaryTrajMeasure

/-- The reverse-time tail, after integrating out time zero, is the stationary one-sided
trajectory law. -/
theorem stateAndIndependentTailsMeasure_map_pastTail
    {π : Measure α} [IsProbabilityMeasure π] {K : Kernel α α} [IsMarkovKernel K] :
    (stateAndIndependentTailsMeasure π K).map (fun z => z.2.2) = stationaryTrajMeasure π K := by
  calc
    (stateAndIndependentTailsMeasure π K).map (fun z => z.2.2) =
        ((stateAndIndependentTailsMeasure π K).map Prod.snd).map Prod.snd := by
      symm
      rw [Measure.map_map measurable_snd measurable_snd]
      rfl
    _ = (conditionalIndependentTwoTailsKernel K ∘ₘ π).map Prod.snd := by
      unfold stateAndIndependentTailsMeasure
      rw [Measure.compProd_eq_comp_prod, Measure.map_comp π _ measurable_snd,
        ← Kernel.snd_eq, Kernel.snd_prod]
    _ = stationaryTrajMeasure π K := by
      rw [Measure.map_comp π _ measurable_snd, ← Kernel.snd_eq]
      unfold conditionalIndependentTwoTailsKernel
      rw [Kernel.snd_prod]
      exact conditionalHomogeneousTrajKernel_comp_eq_stationaryTrajMeasure

/-- Every integer coordinate of the state-anchored trajectory has the invariant marginal.
This does not assert full integer-shift invariance of the path law. -/
theorem reversibleStateAnchoredTwoSidedTrajMeasure_marginal
    {π : Measure α} [IsProbabilityMeasure π] {K : Kernel α α} [IsMarkovKernel K]
    (hstationary : Kernel.Invariant K π) (i : ℤ) :
    (reversibleStateAnchoredTwoSidedTrajMeasure π K).map (fun x => x i) = π := by
  cases i with
  | ofNat n =>
      cases n with
      | zero =>
          unfold reversibleStateAnchoredTwoSidedTrajMeasure
          change Measure.map (fun x : ℤ → α => x (0 : ℤ))
              (Measure.map spliceStateAndTails (stateAndIndependentTailsMeasure π K)) = π
          rw [Measure.map_map (measurable_pi_apply (0 : ℤ)) measurable_spliceStateAndTails]
          change (stateAndIndependentTailsMeasure π K).map Prod.fst = π
          exact stateAndIndependentTailsMeasure_map_zero
      | succ n =>
          unfold reversibleStateAnchoredTwoSidedTrajMeasure
          rw [Measure.map_map (measurable_pi_apply _) measurable_spliceStateAndTails]
          change (stateAndIndependentTailsMeasure π K).map (fun z => z.2.1 (n + 1)) = π
          calc
            (stateAndIndependentTailsMeasure π K).map (fun z => z.2.1 (n + 1)) =
                ((stateAndIndependentTailsMeasure π K).map (fun z => z.2.1)).map
                  (fun x => x (n + 1)) := by
              symm
              simpa [Function.comp_def] using
                (Measure.map_map (μ := stateAndIndependentTailsMeasure π K)
                  (measurable_pi_apply (n + 1))
                  (measurable_fst.comp measurable_snd))
            _ = (stationaryTrajMeasure π K).map (fun x => x (n + 1)) := by
              rw [stateAndIndependentTailsMeasure_map_futureTail]
            _ = π := stationaryTrajMeasure_marginal hstationary (n + 1)
  | negSucc n =>
      unfold reversibleStateAnchoredTwoSidedTrajMeasure
      rw [Measure.map_map (measurable_pi_apply _) measurable_spliceStateAndTails]
      change (stateAndIndependentTailsMeasure π K).map (fun z => z.2.2 (n + 1)) = π
      calc
        (stateAndIndependentTailsMeasure π K).map (fun z => z.2.2 (n + 1)) =
            ((stateAndIndependentTailsMeasure π K).map (fun z => z.2.2)).map
              (fun x => x (n + 1)) := by
          symm
          simpa [Function.comp_def] using
            (Measure.map_map (μ := stateAndIndependentTailsMeasure π K)
              (measurable_pi_apply (n + 1))
              (measurable_snd.comp measurable_snd))
        _ = (stationaryTrajMeasure π K).map (fun x => x (n + 1)) := by
          rw [stateAndIndependentTailsMeasure_map_pastTail]
        _ = π := stationaryTrajMeasure_marginal hstationary (n + 1)

/-- Under the source construction, `(X₀, X₋₁)` has the ordinary stationary one-step law. -/
theorem stateAndIndependentTailsMeasure_map_state_past_one
    {π : Measure α} [IsProbabilityMeasure π] {K : Kernel α α} [IsMarkovKernel K] :
    (stateAndIndependentTailsMeasure π K).map (fun z => (z.1, z.2.2 1)) = π ⊗ₘ K := by
  change (π ⊗ₘ conditionalIndependentTwoTailsKernel K).map
      (Prod.map id ((fun x : ℕ → α => x 1) ∘ Prod.snd)) = π ⊗ₘ K
  rw [← Measure.compProd_map ((measurable_pi_apply 1).comp measurable_snd)]
  rw [conditionalIndependentTwoTailsKernel_map_past_one_comp]

/-- Reversing the displayed pair turns `(X₀, X₋₁)` into `(X₋₁, X₀)`. -/
theorem stateAndIndependentTailsMeasure_map_past_one_state
    {π : Measure α} [IsProbabilityMeasure π] {K : Kernel α α} [IsMarkovKernel K] :
    (stateAndIndependentTailsMeasure π K).map (fun z => (z.2.2 1, z.1)) =
      (π ⊗ₘ K).map Prod.swap := by
  calc
    (stateAndIndependentTailsMeasure π K).map (fun z => (z.2.2 1, z.1)) =
        (stateAndIndependentTailsMeasure π K).map
          (Prod.swap ∘ fun z => (z.1, z.2.2 1)) := by
      rfl
    _ = ((stateAndIndependentTailsMeasure π K).map
          (fun z => (z.1, z.2.2 1))).map Prod.swap := by
      symm
      exact Measure.map_map measurable_swap
        (Measurable.prodMk measurable_fst
          (((measurable_pi_apply 1).comp measurable_snd).comp measurable_snd))
    _ = (π ⊗ₘ K).map Prod.swap := by
      rw [stateAndIndependentTailsMeasure_map_state_past_one]

/-- The negative/cross-zero pair of the state-anchored path is the swapped stationary
one-step law.  Detailed balance turns it into the forward stationary pair law below. -/
theorem reversibleStateAnchoredTwoSidedTrajMeasure_crossZeroPair
    {π : Measure α} [IsProbabilityMeasure π] {K : Kernel α α} [IsMarkovKernel K] :
    (reversibleStateAnchoredTwoSidedTrajMeasure π K).map
        (fun x => (x (-1 : ℤ), x 0)) = (π ⊗ₘ K).map Prod.swap := by
  unfold reversibleStateAnchoredTwoSidedTrajMeasure
  rw [Measure.map_map
    (Measurable.prodMk (measurable_pi_apply (-1 : ℤ)) (measurable_pi_apply 0))
    measurable_spliceStateAndTails]
  change (stateAndIndependentTailsMeasure π K).map (fun z => (z.2.2 1, z.1)) =
    (π ⊗ₘ K).map Prod.swap
  exact stateAndIndependentTailsMeasure_map_past_one_state

/-- The stationary one-step composition-product law has the expected PMF mass on a pair. -/
theorem countablePMFKernel_compProd_singleton
    (π : PMF ℕ) (K : CountableMarkovKernel ℕ) (x y : ℕ) :
    (π.toMeasure ⊗ₘ countablePMFKernel K) ({(x, y)} : Set (ℕ × ℕ)) = π x * K x y := by
  rw [← Set.singleton_prod_singleton, Measure.compProd_apply_prod
    (measurableSet_singleton x) (measurableSet_singleton y)]
  rw [lintegral_singleton]
  change (K x).toMeasure {y} * π.toMeasure {x} = π x * K x y
  rw [(K x).toMeasure_apply_singleton y (measurableSet_singleton y),
    π.toMeasure_apply_singleton x (measurableSet_singleton x)]
  exact mul_comm _ _

/-- PMF detailed balance makes the stationary one-step pair law invariant under swapping. -/
theorem PMFDetailedBalance.compProd_swap
    {K : CountableMarkovKernel ℕ} {π : PMF ℕ}
    (hbalance : PMFDetailedBalance K π) :
    (π.toMeasure ⊗ₘ countablePMFKernel K).map Prod.swap =
      π.toMeasure ⊗ₘ countablePMFKernel K := by
  apply Measure.ext_of_singleton
  rintro ⟨x, y⟩
  rw [Measure.map_apply measurable_swap (measurableSet_singleton (x, y))]
  have hpre : Prod.swap ⁻¹' ({(x, y)} : Set (ℕ × ℕ)) = {(y, x)} := by
    ext z
    rcases z with ⟨a, b⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.swap_prod_mk]
    constructor <;> intro h <;> cases h <;> rfl
  rw [hpre, countablePMFKernel_compProd_singleton,
    countablePMFKernel_compProd_singleton]
  exact (hbalance x y).symm

/-- For a countable detailed-balance kernel, the cross-zero pair is a forward stationary
transition pair. -/
theorem reversibleStateAnchoredTwoSidedTrajMeasure_crossZeroPair_eq_stationaryPair
    {K : CountableMarkovKernel ℕ} {π : PMF ℕ}
    (hbalance : PMFDetailedBalance K π) :
    (reversibleStateAnchoredTwoSidedTrajMeasure π.toMeasure (countablePMFKernel K)).map
        (fun x => (x (-1 : ℤ), x 0)) = π.toMeasure ⊗ₘ countablePMFKernel K := by
  rw [reversibleStateAnchoredTwoSidedTrajMeasure_crossZeroPair,
    hbalance.compProd_swap]

/-- Every integer coordinate of the stable uniformized M/M/1 construction has its geometric
stationary marginal. -/
theorem geoNNPMF_uniformized_twoSided_marginal
    (rho : NNReal) (hrho : rho < 1) (i : ℤ) :
    (reversibleStateAnchoredTwoSidedTrajMeasure
      (geoNNPMF rho hrho).toMeasure
      (countablePMFKernel
        (reflectedBirthDeathKernel (uniformizedBirthProbability rho)
          (uniformizedBirthProbability_le_one rho)))).map
        (fun x => x i) = (geoNNPMF rho hrho).toMeasure := by
  exact reversibleStateAnchoredTwoSidedTrajMeasure_marginal
    (geoNNPMF_uniformized_kernelInvariant rho hrho) i

/-- The stable uniformized M/M/1 embedded chain has its negative/cross-zero pair distributed
as a forward stationary transition pair. -/
theorem geoNNPMF_uniformized_twoSided_crossZeroPair
    (rho : NNReal) (hrho : rho < 1) :
    (reversibleStateAnchoredTwoSidedTrajMeasure
      (geoNNPMF rho hrho).toMeasure
      (countablePMFKernel
        (reflectedBirthDeathKernel (uniformizedBirthProbability rho)
          (uniformizedBirthProbability_le_one rho)))).map
        (fun x => (x (-1 : ℤ), x 0)) =
      (geoNNPMF rho hrho).toMeasure ⊗ₘ
        countablePMFKernel
          (reflectedBirthDeathKernel (uniformizedBirthProbability rho)
            (uniformizedBirthProbability_le_one rho)) := by
  exact reversibleStateAnchoredTwoSidedTrajMeasure_crossZeroPair_eq_stationaryPair
    (geoNNPMF_detailedBalance rho hrho)

end

end AppliedModelingLib.Probability.Queueing
