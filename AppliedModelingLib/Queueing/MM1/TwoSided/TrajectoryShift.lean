import AppliedModelingLib.Queueing.MM1.TwoSided.Trajectory

/-!
# One-edge shift consistency for the state-anchored two-sided trajectory

This proves only equality of the adjacent windows `(-1,0)` and `(0,1)` under
detailed balance.  It is not a claim of full path-law invariance under every
integer shift and does not construct a Palm law.
-/

namespace AppliedModelingLib.Probability.Queueing

open MeasureTheory ProbabilityTheory Preorder

noncomputable section

variable {α : Type*} [MeasurableSpace α]

/-- The first (positive-time) conditional tail advances by `K` after one step. -/
theorem conditionalIndependentTwoTailsKernel_map_future_one
    {K : Kernel α α} [IsMarkovKernel K] :
    (conditionalIndependentTwoTailsKernel K).map (fun z => z.1 1) = K := by
  calc
    (conditionalIndependentTwoTailsKernel K).map (fun z => z.1 1) =
        ((conditionalIndependentTwoTailsKernel K).map Prod.fst).map
          (fun x => x 1) := by
      simpa [Function.comp_def] using
        (Kernel.map_comp_right (conditionalIndependentTwoTailsKernel K)
          measurable_fst (measurable_pi_apply 1))
    _ = ((conditionalIndependentTwoTailsKernel K).fst).map (fun x => x 1) := by
      rw [Kernel.fst_eq]
    _ = (conditionalHomogeneousTrajKernel K).map (fun x => x 1) := by
      unfold conditionalIndependentTwoTailsKernel
      rw [Kernel.fst_prod]
    _ = K := by
      unfold conditionalHomogeneousTrajKernel
      rw [Kernel.map_comp, Kernel.map_traj_succ_self]
      unfold homogeneousTrajKernel
      rw [Kernel.comp_assoc]
      rw [Kernel.deterministic_comp_deterministic
        (measurable_zeroHistory (α := α)) (measurable_pi_apply _)]
      simpa [zeroHistory, Function.comp_def, Kernel.id] using (Kernel.comp_id K)

/-- Under the source construction, `(X₀,X₁)` has the ordinary stationary
one-step law. -/
theorem stateAndIndependentTailsMeasure_map_state_future_one
    {π : Measure α} [IsProbabilityMeasure π] {K : Kernel α α} [IsMarkovKernel K] :
    (stateAndIndependentTailsMeasure π K).map (fun z => (z.1, z.2.1 1)) = π ⊗ₘ K := by
  change (π ⊗ₘ conditionalIndependentTwoTailsKernel K).map
      (Prod.map id ((fun x : ℕ → α => x 1) ∘ Prod.fst)) = π ⊗ₘ K
  rw [← Measure.compProd_map ((measurable_pi_apply 1).comp measurable_fst)]
  change π ⊗ₘ (conditionalIndependentTwoTailsKernel K).map
    (fun z => z.1 1) = π ⊗ₘ K
  rw [conditionalIndependentTwoTailsKernel_map_future_one]

/-- The nonnegative adjacent window of the state-anchored two-sided path has
the forward stationary pair law. -/
theorem reversibleStateAnchoredTwoSidedTrajMeasure_zeroOnePair
    {π : Measure α} [IsProbabilityMeasure π] {K : Kernel α α} [IsMarkovKernel K] :
    (reversibleStateAnchoredTwoSidedTrajMeasure π K).map
        (fun x => (x 0, x (1 : ℤ))) = π ⊗ₘ K := by
  unfold reversibleStateAnchoredTwoSidedTrajMeasure
  rw [Measure.map_map
    (Measurable.prodMk (measurable_pi_apply 0) (measurable_pi_apply (1 : ℤ)))
    measurable_spliceStateAndTails]
  change (stateAndIndependentTailsMeasure π K).map (fun z => (z.1, z.2.1 1)) = π ⊗ₘ K
  exact stateAndIndependentTailsMeasure_map_state_future_one

/-- Detailed balance gives one-step integer-shift consistency of the adjacent
window: the law of `(X₋₁,X₀)` is the law of `(X₀,X₁)`.  This is only a
two-coordinate shift theorem, not full `ℤ`-path shift invariance. -/
theorem PMFDetailedBalance.reversibleStateAnchoredTwoSidedTrajMeasure_adjacent_shift
    {K : CountableMarkovKernel ℕ} {π : PMF ℕ}
    (hbalance : PMFDetailedBalance K π) :
    (reversibleStateAnchoredTwoSidedTrajMeasure π.toMeasure (countablePMFKernel K)).map
        (fun x => (x (-1 : ℤ), x 0)) =
      (reversibleStateAnchoredTwoSidedTrajMeasure π.toMeasure (countablePMFKernel K)).map
        (fun x => (x 0, x (1 : ℤ))) := by
  rw [reversibleStateAnchoredTwoSidedTrajMeasure_crossZeroPair_eq_stationaryPair hbalance,
    reversibleStateAnchoredTwoSidedTrajMeasure_zeroOnePair]

/-- Stable uniformized M/M/1 has the same adjacent-pair law across the first
integer shift of this two-sided embedded construction. -/
theorem geoNNPMF_uniformized_twoSided_adjacent_shift
    (rho : NNReal) (hrho : rho < 1) :
    (reversibleStateAnchoredTwoSidedTrajMeasure
      (geoNNPMF rho hrho).toMeasure
      (countablePMFKernel
        (reflectedBirthDeathKernel (uniformizedBirthProbability rho)
          (uniformizedBirthProbability_le_one rho)))).map
        (fun x => (x (-1 : ℤ), x 0)) =
      (reversibleStateAnchoredTwoSidedTrajMeasure
        (geoNNPMF rho hrho).toMeasure
        (countablePMFKernel
          (reflectedBirthDeathKernel (uniformizedBirthProbability rho)
            (uniformizedBirthProbability_le_one rho)))).map
        (fun x => (x 0, x (1 : ℤ))) := by
  exact PMFDetailedBalance.reversibleStateAnchoredTwoSidedTrajMeasure_adjacent_shift
    (geoNNPMF_detailedBalance rho hrho)

/-- Under detailed balance, every adjacent integer window of the independently
spliced two-sided embedded trajectory has the stationary transition law. This
is a finite-window two-coordinate stationarity theorem, not full path-law
shift invariance. -/
theorem PMFDetailedBalance.reversibleStateAnchoredTwoSidedTrajMeasure_consecutivePair
    {K : CountableMarkovKernel ℕ} {π : PMF ℕ}
    (hbalance : PMFDetailedBalance K π) (i : ℤ) :
    (reversibleStateAnchoredTwoSidedTrajMeasure π.toMeasure (countablePMFKernel K)).map
        (fun x => (x i, x (i + 1))) = π.toMeasure ⊗ₘ countablePMFKernel K := by
  let K' : Kernel ℕ ℕ := countablePMFKernel K
  have hstationary : Kernel.Invariant K' π.toMeasure := hbalance.stationary.kernelInvariant
  cases i with
  | ofNat n =>
      cases n with
      | zero =>
          simpa [K'] using
            (reversibleStateAnchoredTwoSidedTrajMeasure_zeroOnePair
              (π := π.toMeasure) (K := K'))
      | succ n =>
          let M : Measure (ℤ → ℕ) :=
            reversibleStateAnchoredTwoSidedTrajMeasure π.toMeasure K'
          let S : Measure (ℕ × ((ℕ → ℕ) × (ℕ → ℕ))) :=
            stateAndIndependentTailsMeasure π.toMeasure K'
          let f : (ℕ → ℕ) → ℕ × ℕ := fun x => (x (n + 1), x (n + 2))
          have hf : Measurable f :=
            (measurable_pi_apply _).prodMk (measurable_pi_apply _)
          have hfuture : Measurable (fun z : ℕ × ((ℕ → ℕ) × (ℕ → ℕ)) => z.2.1) := by
            fun_prop
          calc
            M.map (fun x => (x (Int.ofNat (n + 1)), x (Int.ofNat (n + 1) + 1))) =
                S.map (fun z => (z.2.1 (n + 1), z.2.1 (n + 2))) := by
              unfold M reversibleStateAnchoredTwoSidedTrajMeasure
              rw [Measure.map_map
                (Measurable.prodMk (measurable_pi_apply _) (measurable_pi_apply _))
                measurable_spliceStateAndTails]
              rfl
            _ = (S.map (fun z => z.2.1)).map f := by
              symm
              rw [Measure.map_map hf hfuture]
              rfl
            _ = (stationaryTrajMeasure π.toMeasure K').map f := by
              rw [show S = stateAndIndependentTailsMeasure π.toMeasure K' by rfl,
                stateAndIndependentTailsMeasure_map_futureTail]
            _ = π.toMeasure ⊗ₘ K' := by
              exact stationaryTrajMeasure_consecutivePair hstationary (n + 1)
  | negSucc n =>
      cases n with
      | zero =>
          simpa [K'] using
            (reversibleStateAnchoredTwoSidedTrajMeasure_crossZeroPair_eq_stationaryPair
              hbalance)
      | succ n =>
          let M : Measure (ℤ → ℕ) :=
            reversibleStateAnchoredTwoSidedTrajMeasure π.toMeasure K'
          let S : Measure (ℕ × ((ℕ → ℕ) × (ℕ → ℕ))) :=
            stateAndIndependentTailsMeasure π.toMeasure K'
          let f : (ℕ → ℕ) → ℕ × ℕ := fun x => (x (n + 1), x (n + 2))
          let g : (ℕ → ℕ) → ℕ × ℕ := fun x => (x (n + 2), x (n + 1))
          have hf : Measurable f :=
            (measurable_pi_apply _).prodMk (measurable_pi_apply _)
          have hg : Measurable g :=
            (measurable_pi_apply _).prodMk (measurable_pi_apply _)
          have hpast : Measurable (fun z : ℕ × ((ℕ → ℕ) × (ℕ → ℕ)) => z.2.2) := by
            fun_prop
          calc
            M.map (fun x =>
                (x (Int.negSucc (n + 1)), x (Int.negSucc (n + 1) + 1))) =
                S.map (fun z => (z.2.2 (n + 2), z.2.2 (n + 1))) := by
              unfold M reversibleStateAnchoredTwoSidedTrajMeasure
              rw [Measure.map_map
                (Measurable.prodMk (measurable_pi_apply _) (measurable_pi_apply _))
                measurable_spliceStateAndTails]
              rfl
            _ = (S.map (fun z => z.2.2)).map g := by
              symm
              rw [Measure.map_map hg hpast]
              rfl
            _ = (stationaryTrajMeasure π.toMeasure K').map g := by
              rw [show S = stateAndIndependentTailsMeasure π.toMeasure K' by rfl,
                stateAndIndependentTailsMeasure_map_pastTail]
            _ = ((stationaryTrajMeasure π.toMeasure K').map f).map Prod.swap := by
              rw [Measure.map_map measurable_swap hf]
              rfl
            _ = (π.toMeasure ⊗ₘ K').map Prod.swap := by
              rw [stationaryTrajMeasure_consecutivePair hstationary (n + 1)]
            _ = π.toMeasure ⊗ₘ K' := by
              rw [hbalance.compProd_swap]

end

end AppliedModelingLib.Probability.Queueing
