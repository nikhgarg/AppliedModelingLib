import AppliedModelingLib.Foundations.Probability.StationaryPoissonFutureInputFactors
import AppliedModelingLib.Foundations.Probability.StationaryPoissonWorkFutureMarkFactors
import AppliedModelingLib.Foundations.Probability.IidStatePrefixStopping

/-!
# A measurable section for stationary Poisson full-future IID factors

The full-future factor of a stationary marked Poisson input retains the
equilibrium past and exposes an IID sequence of future arrival-gap/work
pairs.  This module supplies a measurable reconstruction section and proves
that it is exact on every literal stationary input.
-/

namespace AppliedModelingLib.Probability.Queueing

open MeasureTheory ProbabilityTheory
open PoissonProcess

noncomputable section

/-- Under the full stationary marked-Poisson future pair law, the arrival-gap
projection has null singleton fibers. -/
theorem measure_expMeasure_prod_fst_preimage_singleton_eq_zero
    {rate : ℝ} (hrate : 0 < rate) (a : ℝ) :
    ((expMeasure rate).prod (expMeasure (1 : ℝ))) (Prod.fst ⁻¹' {a}) = 0 := by
  letI : IsProbabilityMeasure (expMeasure (1 : ℝ)) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  apply IIDStream.measure_prod_fst_preimage_singleton_eq_zero
  simp [expMeasure, gammaMeasure]

/-- A future renewal epoch whose last gap is a fresh exponential coordinate
cannot equal a Borel threshold of the external state and all earlier marked
renewal pairs.  This is the atomless graph step used when a queueing argument
reduces a possible boundary arrival to an equality at a service-start clock. -/
theorem measure_futureArrivalTime_succ_eq_prefixFunction_zero
    {σ : Type*} [MeasurableSpace σ] (ρ : Measure σ)
    [IsProbabilityMeasure ρ] {rate : ℝ} (hrate : 0 < rate)
    (N : ℕ) (g : σ × (Finset.range (N + 1) → ℝ × ℝ) → ℝ)
    (hg : Measurable g) :
    (ρ.prod (IIDStream.measure ((expMeasure rate).prod (expMeasure (1 : ℝ)))))
      {z | PoissonProcess.arrivalTime (N + 1) (fun r => (z.2 r).1) =
        g (IIDStream.stateStreamPrefix (σ := σ) (α := ℝ × ℝ) N z)} = 0 := by
  let μ : Measure (ℝ × ℝ) := (expMeasure rate).prod (expMeasure (1 : ℝ))
  letI : IsProbabilityMeasure (expMeasure rate) :=
    isProbabilityMeasure_expMeasure hrate
  letI : IsProbabilityMeasure (expMeasure (1 : ℝ)) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  let shifted : σ × (Finset.range (N + 1) → ℝ × ℝ) → ℝ := fun x =>
    g x - ∑ r : Finset.range (N + 1), (x.2 r).1
  have hshifted : Measurable shifted := by
    apply hg.sub
    fun_prop
  have hzero : ∀ b : ℝ, μ (Prod.fst ⁻¹' {b}) = 0 := by
    intro b
    exact measure_expMeasure_prod_fst_preimage_singleton_eq_zero hrate b
  have hgraph := IIDStream.measure_state_coordinate_apply_eq_prefixFunction_zero
    ρ μ Prod.fst measurable_fst hzero N shifted hshifted
  change (ρ.prod (IIDStream.measure μ))
    {z | PoissonProcess.arrivalTime (N + 1) (fun r => (z.2 r).1) =
      g (IIDStream.stateStreamPrefix (σ := σ) (α := ℝ × ℝ) N z)} = 0
  have harrival : ∀ z : σ × (ℕ → ℝ × ℝ),
      PoissonProcess.arrivalTime (N + 1) (fun r => (z.2 r).1) =
        (∑ r : Finset.range (N + 1), (z.2 r).1) + (z.2 (N + 1)).1 := by
    intro z
    simp only [PoissonProcess.arrivalTime, PoissonProcess.interarrival]
    rw [Finset.sum_range_succ]
    exact congrArg (fun a : ℝ => a + (z.2 (N + 1)).1)
      (Finset.sum_attach _ _).symm
  have hprefixsum : ∀ z : σ × (ℕ → ℝ × ℝ),
      (∑ r : Finset.range (N + 1),
        (IIDStream.streamPrefix (α := ℝ × ℝ) N z.2 r).1) =
      ∑ r : Finset.range (N + 1), (z.2 r).1 := by
    intro z
    apply Finset.sum_congr rfl
    intro r _
    simp [IIDStream.streamPrefix, IIDStream.coordinate]
  have hevent :
      {z : σ × (ℕ → ℝ × ℝ) |
        PoissonProcess.arrivalTime (N + 1) (fun r => (z.2 r).1) =
          g (IIDStream.stateStreamPrefix (σ := σ) (α := ℝ × ℝ) N z)} =
      {z | Prod.fst (IIDStream.coordinate (N + 1) z.2) =
        shifted (IIDStream.stateStreamPrefix (σ := σ) (α := ℝ × ℝ) N z)} := by
    ext z
    simp only [Set.mem_setOf_eq]
    rw [harrival]
    simp only [IIDStream.coordinate, shifted, IIDStream.stateStreamPrefix]
    rw [hprefixsum]
    constructor <;> intro h <;> linarith
  rw [hevent]
  exact hgraph

/-- Every positive-index future renewal epoch is atomless relative to the
external state and exactly the earlier marked-renewal prefix.  This uniform
form includes the first future arrival, whose epoch uses the initial IID
coordinate. -/
theorem measure_futureArrivalTime_eq_prefixFunction_zero
    {σ : Type*} [MeasurableSpace σ] (ρ : Measure σ)
    [IsProbabilityMeasure ρ] {rate : ℝ} (hrate : 0 < rate)
    (N : ℕ) (g : σ × (Finset.range N → ℝ × ℝ) → ℝ)
    (hg : Measurable g) :
    (ρ.prod (IIDStream.measure ((expMeasure rate).prod (expMeasure (1 : ℝ)))))
      {z | PoissonProcess.arrivalTime N (fun r => (z.2 r).1) =
        g (z.1, fun r => z.2 r)} = 0 := by
  let μ : Measure (ℝ × ℝ) := (expMeasure rate).prod (expMeasure (1 : ℝ))
  letI : IsProbabilityMeasure (expMeasure rate) :=
    isProbabilityMeasure_expMeasure hrate
  letI : IsProbabilityMeasure (expMeasure (1 : ℝ)) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  cases N with
  | zero =>
      let emptyPrefix : Finset.range 0 → ℝ × ℝ := fun r =>
        False.elim (Nat.not_lt_zero r.1 (Finset.mem_range.mp r.2))
      let g0 : σ → ℝ := fun x => g (x, emptyPrefix)
      have hg0 : Measurable g0 := by
        apply hg.comp
        exact measurable_id.prodMk measurable_const
      have hzero : ∀ b : ℝ, μ (Prod.fst ⁻¹' {b}) = 0 := by
        intro b
        exact measure_expMeasure_prod_fst_preimage_singleton_eq_zero hrate b
      have hgraph := IIDStream.measure_state_coordinate_zero_apply_eq_externalFunction_zero
        ρ μ Prod.fst measurable_fst hzero g0 hg0
      change (ρ.prod (IIDStream.measure μ))
        {z | PoissonProcess.arrivalTime 0 (fun r => (z.2 r).1) =
          g (z.1, fun r => z.2 r)} = 0
      have hevent :
          {z : σ × (ℕ → ℝ × ℝ) |
            PoissonProcess.arrivalTime 0 (fun r => (z.2 r).1) =
              g (z.1, fun r => z.2 r)} =
          {z | Prod.fst (IIDStream.coordinate 0 z.2) = g0 z.1} := by
        ext z
        simp only [Set.mem_setOf_eq, IIDStream.coordinate, g0]
        rw [show PoissonProcess.arrivalTime 0 (fun r => (z.2 r).1) =
            (z.2 0).1 by
              simp [PoissonProcess.arrivalTime, PoissonProcess.interarrival]]
        have hempty : (fun r : Finset.range 0 => z.2 r) = emptyPrefix := by
          funext r
          exact False.elim (Nat.not_lt_zero r.1 (Finset.mem_range.mp r.2))
        rw [hempty]
      rw [hevent]
      exact hgraph
  | succ N =>
      simpa [IIDStream.stateStreamPrefix, IIDStream.streamPrefix] using
        measure_futureArrivalTime_succ_eq_prefixFunction_zero ρ hrate N g hg

/-- Reconstruct a stationary marked input from its external equilibrium data
and its IID future arrival-gap/work stream. -/
def stationaryPoissonWorkFromFutureExternalIidFactors
    (rate : ℝ) (hrate : 0 < rate) :
    (((ℕ → ℝ) × ℝ) × (ℕ → ℝ)) × (ℕ → (ℝ × ℝ)) →
      GoodSuspensionState × (ℤ → ℝ) :=
  fun x =>
    let future := MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ ℕ x.2
    let arrival := equilibriumToGoodSuspension rate hrate (future.1, x.1.1.1)
    stationaryPoissonWorkFromFutureMarkFactors
      (((arrival, x.1.1.2), x.1.2), future.2)

/-- The full-future reconstruction section is Borel measurable. -/
theorem measurable_stationaryPoissonWorkFromFutureExternalIidFactors
    (rate : ℝ) (hrate : 0 < rate) :
    Measurable (stationaryPoissonWorkFromFutureExternalIidFactors rate hrate) := by
  let E := ((ℕ → ℝ) × ℝ) × (ℕ → ℝ)
  let future : E × (ℕ → (ℝ × ℝ)) → (ℕ → ℝ) × (ℕ → ℝ) :=
    fun x => MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ ℕ x.2
  have hfuture : Measurable future :=
    (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ ℕ).measurable.comp measurable_snd
  let base : E × (ℕ → (ℝ × ℝ)) → (ℕ → ℝ) × (ℕ → ℝ) :=
    fun x => ((future x).1, x.1.1.1)
  have hbasePast : Measurable (fun x : E × (ℕ → (ℝ × ℝ)) => x.1.1.1) := by
    dsimp [E]
    fun_prop
  have hbase : Measurable base :=
    (measurable_fst.comp hfuture).prodMk hbasePast
  let arrival : E × (ℕ → (ℝ × ℝ)) → GoodSuspensionState :=
    equilibriumToGoodSuspension rate hrate ∘ base
  have harrival : Measurable arrival :=
    (measurable_equilibriumToGoodSuspension rate hrate).comp hbase
  let factors : E × (ℕ → (ℝ × ℝ)) →
      ((GoodSuspensionState × ℝ) × (ℕ → ℝ)) × (ℕ → ℝ) :=
    fun x => (((arrival x, x.1.1.2), x.1.2), (future x).2)
  have hhead : Measurable (fun x : E × (ℕ → (ℝ × ℝ)) => x.1.1.2) := by
    dsimp [E]
    fun_prop
  have hpast : Measurable (fun x : E × (ℕ → (ℝ × ℝ)) => x.1.2) := by
    dsimp [E]
    fun_prop
  have hfactors : Measurable factors :=
    ((harrival.prodMk hhead).prodMk hpast).prodMk
      (measurable_snd.comp hfuture)
  exact measurable_stationaryPoissonWorkFromFutureMarkFactors.comp hfactors

/-- Reconstructing the full-future factor of a literal stationary marked
input returns that input exactly. -/
theorem stationaryPoissonWorkFromFutureExternalIidFactors_apply_factors
    (rate : ℝ) (hrate : 0 < rate)
    (z : GoodSuspensionState × (ℤ → ℝ)) :
    stationaryPoissonWorkFromFutureExternalIidFactors rate hrate
      (stationaryPoissonWorkFutureExternalIidFactors z) = z := by
  rcases z with ⟨arrival, work⟩
  have harrival : equilibriumToGoodSuspension rate hrate
      ((MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ ℕ
        (stationaryPoissonWorkFutureExternalIidFactors (arrival, work)).2).1,
        (stationaryPoissonWorkFutureExternalIidFactors (arrival, work)).1.1.1) = arrival := by
    simpa [stationaryPoissonWorkFutureExternalIidFactors,
      equilibriumFutureExternalIidFactors, equilibriumFutureExternalFactors,
      stationaryPoissonWorkToEquilibrium, IIDStream.zip,
      MeasurableEquiv.arrowProdEquivProdArrow] using
      (equilibriumToGoodSuspension_apply_suspensionToEquilibrium rate hrate arrival)
  dsimp [stationaryPoissonWorkFromFutureExternalIidFactors]
  rw [harrival]
  simpa [stationaryPoissonWorkFutureExternalIidFactors,
    equilibriumFutureExternalIidFactors, equilibriumFutureExternalFactors,
    stationaryPoissonWorkToEquilibrium, IIDStream.zip,
    MeasurableEquiv.arrowProdEquivProdArrow,
    stationaryPoissonWorkFutureMarkFactors] using
    (stationaryPoissonWorkFromFutureMarkFactors_apply_factors (arrival, work))

/-- In a valid equilibrium reconstruction, the positive labelled arrival
epochs are the renewal sums of the exposed IID gap coordinates. -/
theorem stationaryPoissonWorkArrival_fromFutureExternalIidFactors_ofNat_succ
    (rate : ℝ) (hrate : 0 < rate)
    (external : ((ℕ → ℝ) × ℝ) × (ℕ → ℝ))
    (stream : ℕ → (ℝ × ℝ)) (n : ℕ)
    (hgood : equilibriumToSuspension
      ((MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ ℕ stream).1, external.1.1) ∈
        {p : (ℤ → ℝ) × ℝ | p ∈ suspensionCarrier ∧ suspensionGoodGapPath p.1}) :
    stationaryPoissonWorkArrival
      (stationaryPoissonWorkFromFutureExternalIidFactors rate hrate (external, stream))
      (Int.ofNat (n + 1)) =
        arrivalTime n (fun r => (stream r).1) := by
  have harrival : equilibriumToGoodSuspension rate hrate
      ((MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ ℕ stream).1, external.1.1) =
        ⟨equilibriumToSuspension
          ((MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ ℕ stream).1, external.1.1),
          hgood⟩ :=
    equilibriumToGoodSuspension_eq_mk_of_mem rate hrate _ hgood
  rw [show stationaryPoissonWorkArrival
      (stationaryPoissonWorkFromFutureExternalIidFactors rate hrate (external, stream))
      (Int.ofNat (n + 1)) =
      Probability.PoissonProcess.suspensionBaseArrival
        (equilibriumToGoodSuspension rate hrate
          ((MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ ℕ stream).1, external.1.1))
        (Int.ofNat (n + 1)) by
      rfl, harrival]
  rw [Probability.PoissonProcess.suspensionBaseArrival_ofNat_succ_eq_arrivalTime_sub,
    Probability.PoissonProcess.arrivalTime_suspensionFuturePath_equilibriumToSuspension]
  simp [MeasurableEquiv.arrowProdEquivProdArrow, Probability.PoissonProcess.equilibriumToSuspension]

/-- Two valid full-future reconstructions with the same external equilibrium
state agree at every nonpositive stationary arrival label. -/
theorem stationaryPoissonWorkArrival_fromFutureExternalIidFactors_eq_of_nonpositive
    (rate : ℝ) (hrate : 0 < rate)
    (external : ((ℕ → ℝ) × ℝ) × (ℕ → ℝ))
    (stream otherStream : ℕ → (ℝ × ℝ)) (m : ℤ)
    (hgood : equilibriumToSuspension
      ((MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ ℕ stream).1, external.1.1) ∈
        {p : (ℤ → ℝ) × ℝ | p ∈ suspensionCarrier ∧ suspensionGoodGapPath p.1})
    (hotherGood : equilibriumToSuspension
      ((MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ ℕ otherStream).1, external.1.1) ∈
        {p : (ℤ → ℝ) × ℝ | p ∈ suspensionCarrier ∧ suspensionGoodGapPath p.1})
    (hm : m ≤ 0) :
    stationaryPoissonWorkArrival
      (stationaryPoissonWorkFromFutureExternalIidFactors rate hrate (external, stream)) m =
      stationaryPoissonWorkArrival
        (stationaryPoissonWorkFromFutureExternalIidFactors rate hrate
          (external, otherStream)) m := by
  have harrival := equilibriumToGoodSuspension_eq_mk_of_mem rate hrate
    ((MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ ℕ stream).1, external.1.1) hgood
  have hotherArrival := equilibriumToGoodSuspension_eq_mk_of_mem rate hrate
    ((MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ ℕ otherStream).1, external.1.1)
      hotherGood
  cases m with
  | ofNat n =>
      norm_num at hm
      have hn : n = 0 := by omega
      subst n
      simp only [stationaryPoissonWorkArrival, Probability.Queueing.timedEmbeddedArrival,
        stationaryPoissonWorkFromFutureExternalIidFactors]
      rw [harrival, hotherArrival]
      rfl
  | negSucc n =>
      simp only [stationaryPoissonWorkArrival, Probability.Queueing.timedEmbeddedArrival,
        stationaryPoissonWorkFromFutureExternalIidFactors]
      rw [harrival, hotherArrival]
      rfl

/-- The external origin and past marks determine every nonpositive work mark
of a full-future stationary reconstruction. -/
theorem stationaryPoissonWorkRequirement_fromFutureExternalIidFactors_eq_of_nonpositive
    (rate : ℝ) (hrate : 0 < rate)
    (external : ((ℕ → ℝ) × ℝ) × (ℕ → ℝ))
    (stream otherStream : ℕ → (ℝ × ℝ)) (m : ℤ) (hm : m ≤ 0) :
    stationaryPoissonWorkRequirement
      (stationaryPoissonWorkFromFutureExternalIidFactors rate hrate (external, stream)) m =
      stationaryPoissonWorkRequirement
        (stationaryPoissonWorkFromFutureExternalIidFactors rate hrate
          (external, otherStream)) m := by
  cases m with
  | ofNat n =>
      norm_num at hm
      have hn : n = 0 := by omega
      subst n
      rfl
  | negSucc n => rfl

end

end AppliedModelingLib.Probability.Queueing
