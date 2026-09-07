import AppliedModelingLib.Foundations.Probability.FiniteAdaptiveSampling
import AppliedModelingLib.Foundations.Probability.MeasureInequalities
import AppliedModelingLib.Foundations.Probability.PMFKernel
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-!
# Infinite adaptive fresh sampling

This module gives a common probability space for an infinite adaptive stream
of conditionally IID finite batches.  It uses Mathlib's Ionescu--Tulcea
trajectory construction rather than rebuilding an infinite-product measure.

The coordinate at time zero is a dummy `PUnit`; coordinate `t + 1` is the
batch observed in adaptive round `t`.  This indexing lets the transition
kernel at time `t` inspect precisely the preceding `t` batches.

Upstream implementation reused:
<https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Probability/Kernel/IonescuTulcea/Traj.lean>
Documentation:
<https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Kernel/IonescuTulcea/Traj.html>
-/

open scoped ENNReal
open MeasureTheory ProbabilityTheory
open Preorder

namespace AppliedModelingLib

/-- The dependent coordinates of an infinite heterogeneous adaptive trace.
Coordinate zero is a dummy initial value and coordinate `round + 1` is the
batch sampled in round `round`. -/
def HeterogeneousBatchTraceCoordinate (BatchIndex : ℕ → Type*) (Data : Type*) : ℕ → Type _
  | 0 => PUnit
  | round + 1 => BatchIndex round → Data

instance heterogeneousBatchTraceCoordinateFintype
    (BatchIndex : ℕ → Type*) (Data : Type*)
    [Fintype Data] [fintypeBatchIndex : ∀ round, Fintype (BatchIndex round)]
    [decidableEqBatchIndex : ∀ round, DecidableEq (BatchIndex round)] (round : ℕ) :
    Fintype (HeterogeneousBatchTraceCoordinate BatchIndex Data round) := by
  cases round with
  | zero => simpa only [HeterogeneousBatchTraceCoordinate] using (inferInstance : Fintype PUnit)
  | succ round =>
      letI : Fintype (BatchIndex round) := fintypeBatchIndex round
      letI : DecidableEq (BatchIndex round) := decidableEqBatchIndex round
      simpa only [HeterogeneousBatchTraceCoordinate] using
        (inferInstance : Fintype (BatchIndex round → Data))

instance heterogeneousBatchTraceCoordinateDecidableEq
    (BatchIndex : ℕ → Type*) (Data : Type*)
    [DecidableEq Data] [fintypeBatchIndex : ∀ round, Fintype (BatchIndex round)] (round : ℕ) :
    DecidableEq (HeterogeneousBatchTraceCoordinate BatchIndex Data round) := by
  cases round with
  | zero => simpa only [HeterogeneousBatchTraceCoordinate] using (inferInstance : DecidableEq PUnit)
  | succ round =>
      letI : Fintype (BatchIndex round) := fintypeBatchIndex round
      simpa only [HeterogeneousBatchTraceCoordinate] using
        (inferInstance : DecidableEq (BatchIndex round → Data))

instance heterogeneousBatchTraceCoordinateMeasurableSpace
    (BatchIndex : ℕ → Type*) (Data : Type*) [MeasurableSpace Data]
    (round : ℕ) :
    MeasurableSpace (HeterogeneousBatchTraceCoordinate BatchIndex Data round) := by
  cases round <;> simp only [HeterogeneousBatchTraceCoordinate] <;> infer_instance

instance heterogeneousBatchTraceCoordinateMeasurableSingleton
    (BatchIndex : ℕ → Type*) (Data : Type*) [MeasurableSpace Data]
    [MeasurableSingletonClass Data]
    [fintypeBatchIndex : ∀ round, Fintype (BatchIndex round)] (round : ℕ) :
    MeasurableSingletonClass (HeterogeneousBatchTraceCoordinate BatchIndex Data round) := by
  cases round with
  | zero => simpa only [HeterogeneousBatchTraceCoordinate] using
      (inferInstance : MeasurableSingletonClass PUnit)
  | succ round =>
      letI : Fintype (BatchIndex round) := fintypeBatchIndex round
      simpa only [HeterogeneousBatchTraceCoordinate] using
        (inferInstance : MeasurableSingletonClass (BatchIndex round → Data))

instance heterogeneousBatchTraceCoordinateNonempty
    (BatchIndex : ℕ → Type*) (Data : Type*) [Nonempty Data] (round : ℕ) :
    Nonempty (HeterogeneousBatchTraceCoordinate BatchIndex Data round) := by
  cases round <;> simp only [HeterogeneousBatchTraceCoordinate] <;> infer_instance

/-- Read the actual batch history from a trajectory prefix which also contains
the dummy coordinate zero. -/
def heterogeneousBatchTraceOfPrefix
    {BatchIndex : ℕ → Type*} {Data : Type*} (iteration : ℕ)
    (historyPrefix : (i : Finset.Iic iteration) →
      HeterogeneousBatchTraceCoordinate BatchIndex Data i.1) :
    HeterogeneousBatchTrace BatchIndex Data iteration :=
  fun round => historyPrefix
    ⟨round.1 + 1, Finset.mem_Iic.mpr (Nat.succ_le_of_lt round.2)⟩

/-- Read the first `iteration` sampled batches from an infinite trajectory. -/
def heterogeneousBatchTraceOfInfiniteTrace
    {BatchIndex : ℕ → Type*} {Data : Type*} (iteration : ℕ)
    (trace : (i : ℕ) → HeterogeneousBatchTraceCoordinate BatchIndex Data i) :
    HeterogeneousBatchTrace BatchIndex Data iteration :=
  fun round => trace (round.1 + 1)

/-- The finite trace read from an infinite heterogeneous execution grows by
exactly its next sampled batch. -/
theorem heterogeneousBatchTraceOfInfiniteTrace_succ
    {BatchIndex : ℕ → Type*} {Data : Type*} (iteration : ℕ)
    (trace : (i : ℕ) → HeterogeneousBatchTraceCoordinate BatchIndex Data i) :
    heterogeneousBatchTraceOfInfiniteTrace (iteration + 1) trace =
      heterogeneousBatchTraceSnoc (heterogeneousBatchTraceOfInfiniteTrace iteration trace)
        (fun index => trace (Nat.succ iteration) index) := by
  rw [← heterogeneousBatchTraceSnoc_init_last
    (heterogeneousBatchTraceOfInfiniteTrace (iteration + 1) trace)]
  congr

@[simp] theorem heterogeneousBatchTraceOfPrefix_frestrictLe
    {BatchIndex : ℕ → Type*} {Data : Type*} (iteration : ℕ)
    (trace : (i : ℕ) → HeterogeneousBatchTraceCoordinate BatchIndex Data i) :
    heterogeneousBatchTraceOfPrefix iteration (frestrictLe iteration trace) =
      heterogeneousBatchTraceOfInfiniteTrace iteration trace := by
  funext round index
  rfl

/-- The product measurable-space structure on a finite heterogeneous batch history. -/
instance heterogeneousBatchTraceMeasurableSpace
    (BatchIndex : ℕ → Type*) (Data : Type*) [MeasurableSpace Data] (iteration : ℕ) :
    MeasurableSpace (HeterogeneousBatchTrace BatchIndex Data iteration) := by
  unfold HeterogeneousBatchTrace
  letI : ∀ round : Fin iteration, MeasurableSpace (BatchIndex round.1 → Data) :=
    fun _ => inferInstance
  infer_instance

/-- A finite heterogeneous batch history has measurable singletons whenever
each sampled datum does.  This lets its recursive PMF law interface directly
with the measure-kernel trajectory construction. -/
instance heterogeneousBatchTraceMeasurableSingletonClass
    (BatchIndex : ℕ → Type*) (Data : Type*) [MeasurableSpace Data]
    [MeasurableSingletonClass Data] [∀ round, Fintype (BatchIndex round)]
    (iteration : ℕ) :
    MeasurableSingletonClass (HeterogeneousBatchTrace BatchIndex Data iteration) := by
  unfold HeterogeneousBatchTrace
  letI : Countable (Fin iteration) :=
    @Finite.to_countable (Fin iteration)
      (Fintype.finite (inferInstance : Fintype (Fin iteration)))
  letI : ∀ round : Fin iteration, Fintype (BatchIndex round.1) :=
    fun round => inferInstance
  letI : ∀ round : Fin iteration, Countable (BatchIndex round.1) :=
    fun round =>
      @Finite.to_countable (BatchIndex round.1)
        (Fintype.finite (inferInstance : Fintype (BatchIndex round.1)))
  letI : ∀ round : Fin iteration, MeasurableSpace (BatchIndex round.1 → Data) :=
    fun _ => inferInstance
  letI : ∀ round : Fin iteration, MeasurableSingletonClass (BatchIndex round.1 → Data) :=
    fun _ => inferInstance
  constructor
  intro history
  exact Set.univ_pi_singleton history ▸
    MeasurableSet.univ_pi fun round => measurableSet_singleton (history round)

/-- Reading the sampled finite history from a trajectory prefix is measurable. -/
theorem measurable_heterogeneousBatchTraceOfPrefix
    {BatchIndex : ℕ → Type*} {Data : Type*} [MeasurableSpace Data]
    (iteration : ℕ) :
    Measurable (heterogeneousBatchTraceOfPrefix (BatchIndex := BatchIndex) (Data := Data) iteration) := by
  unfold heterogeneousBatchTraceOfPrefix HeterogeneousBatchTrace
  letI : ∀ round : Fin iteration, MeasurableSpace (BatchIndex round.1 → Data) :=
    fun _ => inferInstance
  apply measurable_pi_lambda
  intro round
  apply measurable_pi_lambda
  intro index
  let prefixIndex : Finset.Iic iteration :=
    ⟨round.1 + 1, Finset.mem_Iic.mpr (Nat.succ_le_of_lt round.2)⟩
  change Measurable (fun historyPrefix :
    ((i : Finset.Iic iteration) → HeterogeneousBatchTraceCoordinate BatchIndex Data i.1) =>
      historyPrefix prefixIndex index)
  exact (measurable_pi_apply prefixIndex).eval

/--
The one-observation kernel on an adaptive batch history, induced by a data
kernel on the deployed state.  The state-of-history map is kept measurable
explicitly, so a law-valued map is never silently promoted to a kernel.

This uses Mathlib's `Kernel.comap` from
[`Probability/Kernel/Composition/MapComap.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Probability/Kernel/Composition/MapComap.lean)
([official documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Kernel/Composition/MapComap.html))
at the pinned Apache-2.0 Mathlib commit. No external Lean source is copied or
ported.
-/
noncomputable def heterogeneousBatchTraceOneObservationKernel
    {State Data : Type*} [MeasurableSpace State] [MeasurableSpace Data]
    (BatchIndex : ℕ → Type*) (dataKernel : Kernel State Data)
    (stateOfHistory : ∀ iteration, HeterogeneousBatchTrace BatchIndex Data iteration → State)
    (iteration : ℕ) (hstate : Measurable (stateOfHistory iteration)) :
    Kernel
      ((i : Finset.Iic iteration) → HeterogeneousBatchTraceCoordinate BatchIndex Data i.1)
      Data :=
  dataKernel.comap
    (fun historyPrefix =>
      stateOfHistory iteration (heterogeneousBatchTraceOfPrefix iteration historyPrefix))
    (hstate.comp (measurable_heterogeneousBatchTraceOfPrefix iteration))

/-- A history-induced one-observation kernel has the displayed deployed-state law. -/
theorem heterogeneousBatchTraceOneObservationKernel_apply
    {State Data : Type*} [MeasurableSpace State] [MeasurableSpace Data]
    (BatchIndex : ℕ → Type*) (dataKernel : Kernel State Data)
    (stateOfHistory : ∀ iteration, HeterogeneousBatchTrace BatchIndex Data iteration → State)
    (iteration : ℕ) (hstate : Measurable (stateOfHistory iteration))
    (historyPrefix : (i : Finset.Iic iteration) →
      HeterogeneousBatchTraceCoordinate BatchIndex Data i.1) :
    heterogeneousBatchTraceOneObservationKernel BatchIndex dataKernel stateOfHistory iteration hstate
      historyPrefix =
      dataKernel (stateOfHistory iteration
        (heterogeneousBatchTraceOfPrefix iteration historyPrefix)) :=
  rfl

/-- A Markov data kernel remains Markov after measurable deployment on a history. -/
theorem heterogeneousBatchTraceOneObservationKernel_isMarkov
    {State Data : Type*} [MeasurableSpace State] [MeasurableSpace Data]
    (BatchIndex : ℕ → Type*) (dataKernel : Kernel State Data) [IsMarkovKernel dataKernel]
    (stateOfHistory : ∀ iteration, HeterogeneousBatchTrace BatchIndex Data iteration → State)
    (iteration : ℕ) (hstate : Measurable (stateOfHistory iteration)) :
    IsMarkovKernel
      (heterogeneousBatchTraceOneObservationKernel BatchIndex dataKernel stateOfHistory iteration hstate) :=
  by
    exact Kernel.IsMarkovKernel.comap dataKernel
      (hstate.comp (measurable_heterogeneousBatchTraceOfPrefix iteration))

/-- The one-element batch version of a measure-valued data kernel.  Unlike
`adaptiveFreshHeterogeneousTraceKernel`, this construction does not require a
finite data carrier: a singleton batch is obtained by mapping the raw draw to
the constant `PUnit → Data` function. -/
noncomputable def adaptiveFreshPunitTraceKernel
    {Control Data : Type*} [MeasurableSpace Control] [MeasurableSpace Data]
    (dataKernel : Kernel Control Data)
    (controlOfHistory : ∀ iteration,
      HeterogeneousBatchTrace (fun _ : ℕ => PUnit) Data iteration → Control)
    (hmeasurable : ∀ iteration, Measurable (controlOfHistory iteration))
    (iteration : ℕ) :
    Kernel
      ((i : Finset.Iic iteration) →
        HeterogeneousBatchTraceCoordinate (fun _ : ℕ => PUnit) Data i.1)
      (HeterogeneousBatchTraceCoordinate (fun _ : ℕ => PUnit) Data (iteration + 1)) :=
  (dataKernel.comap
    (fun historyPrefix =>
      controlOfHistory iteration
        (heterogeneousBatchTraceOfPrefix iteration historyPrefix))
    ((hmeasurable iteration).comp
      (measurable_heterogeneousBatchTraceOfPrefix iteration))).map
    (fun (datum : Data) (_ : PUnit) => datum)

/-- The singleton-batch kernel is Markov whenever the raw data kernel is
Markov. -/
instance adaptiveFreshPunitTraceKernel_isMarkov
    {Control Data : Type*} [MeasurableSpace Control] [MeasurableSpace Data]
    (dataKernel : Kernel Control Data) [IsMarkovKernel dataKernel]
    (controlOfHistory : ∀ iteration,
      HeterogeneousBatchTrace (fun _ : ℕ => PUnit) Data iteration → Control)
    (hmeasurable : ∀ iteration, Measurable (controlOfHistory iteration))
    (iteration : ℕ) :
    IsMarkovKernel
      (adaptiveFreshPunitTraceKernel dataKernel controlOfHistory hmeasurable iteration) := by
  unfold adaptiveFreshPunitTraceKernel
  apply Kernel.IsMarkovKernel.map
  fun_prop

/-- Evaluating the singleton fresh batch recovers exactly the data law at the
control selected from the measurable preceding history. -/
theorem adaptiveFreshPunitTraceKernel_map_apply
    {Control Data : Type*} [MeasurableSpace Control] [MeasurableSpace Data]
    (dataKernel : Kernel Control Data)
    (controlOfHistory : ∀ iteration,
      HeterogeneousBatchTrace (fun _ : ℕ => PUnit) Data iteration → Control)
    (hmeasurable : ∀ iteration, Measurable (controlOfHistory iteration))
    (iteration : ℕ)
    (historyPrefix : (i : Finset.Iic iteration) →
      HeterogeneousBatchTraceCoordinate (fun _ : ℕ => PUnit) Data i.1) :
    (adaptiveFreshPunitTraceKernel dataKernel controlOfHistory hmeasurable iteration
      historyPrefix).map (fun batch => batch PUnit.unit) =
      dataKernel (controlOfHistory iteration
        (heterogeneousBatchTraceOfPrefix iteration historyPrefix)) := by
  unfold adaptiveFreshPunitTraceKernel
  rw [Kernel.map_apply _ (by fun_prop)]
  change Measure.map (fun batch : PUnit → Data => batch PUnit.unit)
      (Measure.map (fun (datum : Data) (_ : PUnit) => datum)
        (dataKernel (controlOfHistory iteration
          (heterogeneousBatchTraceOfPrefix iteration historyPrefix)))) = _
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  simpa only [Function.comp_apply] using
    (Measure.map_id : Measure.map id
      (dataKernel (controlOfHistory iteration
        (heterogeneousBatchTraceOfPrefix iteration historyPrefix))) = _)

/-- A common Ionescu--Tulcea probability space for singleton adaptive draws
from an arbitrary Markov data kernel.  The coordinate at zero is the dummy
`PUnit` value; coordinate `round + 1` is the fresh draw of round `round`. -/
noncomputable def adaptiveFreshPunitInfiniteTraceLaw
    {Control Data : Type*} [MeasurableSpace Control] [MeasurableSpace Data]
    (dataKernel : Kernel Control Data) [IsMarkovKernel dataKernel]
    (controlOfHistory : ∀ iteration,
      HeterogeneousBatchTrace (fun _ : ℕ => PUnit) Data iteration → Control)
    (hmeasurable : ∀ iteration, Measurable (controlOfHistory iteration)) :
    Measure ((i : ℕ) →
      HeterogeneousBatchTraceCoordinate (fun _ : ℕ => PUnit) Data i) :=
  letI : ∀ iteration, IsMarkovKernel
      (adaptiveFreshPunitTraceKernel dataKernel controlOfHistory hmeasurable iteration) :=
    fun iteration => adaptiveFreshPunitTraceKernel_isMarkov dataKernel controlOfHistory
      hmeasurable iteration
  Kernel.trajMeasure (Measure.dirac PUnit.unit)
    (adaptiveFreshPunitTraceKernel dataKernel controlOfHistory hmeasurable)

/-- The generic arbitrary-kernel adaptive trace law is a probability measure. -/
instance adaptiveFreshPunitInfiniteTraceLaw_isProbabilityMeasure
    {Control Data : Type*} [MeasurableSpace Control] [MeasurableSpace Data]
    (dataKernel : Kernel Control Data) [IsMarkovKernel dataKernel]
    (controlOfHistory : ∀ iteration,
      HeterogeneousBatchTrace (fun _ : ℕ => PUnit) Data iteration → Control)
    (hmeasurable : ∀ iteration, Measurable (controlOfHistory iteration)) :
    IsProbabilityMeasure
      (adaptiveFreshPunitInfiniteTraceLaw dataKernel controlOfHistory hmeasurable) := by
  unfold adaptiveFreshPunitInfiniteTraceLaw
  infer_instance

/-- The one-step Markov kernel for a heterogeneous adaptive batch stream. -/
noncomputable def adaptiveFreshHeterogeneousTraceKernel
    {State Data : Type*} [MeasurableSpace Data] [MeasurableSingletonClass Data]
    [Fintype Data] [DecidableEq Data]
    (BatchIndex : ℕ → Type*) [∀ round, Fintype (BatchIndex round)]
    [∀ round, DecidableEq (BatchIndex round)]
    (dataLaw : State → PMF Data)
    (stateOfHistory : ∀ iteration, HeterogeneousBatchTrace BatchIndex Data iteration → State)
    (iteration : ℕ) :
    Kernel
      ((i : Finset.Iic iteration) → HeterogeneousBatchTraceCoordinate BatchIndex Data i.1)
      (HeterogeneousBatchTraceCoordinate BatchIndex Data (iteration + 1)) :=
  Kernel.ofFunOfCountable fun historyPrefix =>
    (pmfProduct (BatchIndex iteration) Data
      (dataLaw (stateOfHistory iteration
        (heterogeneousBatchTraceOfPrefix iteration historyPrefix)))).toMeasure

instance adaptiveFreshHeterogeneousTraceKernel_isMarkovKernel
    {State Data : Type*} [MeasurableSpace Data] [MeasurableSingletonClass Data]
    [Fintype Data] [DecidableEq Data]
    (BatchIndex : ℕ → Type*) [∀ round, Fintype (BatchIndex round)]
    [∀ round, DecidableEq (BatchIndex round)]
    (dataLaw : State → PMF Data)
    (stateOfHistory : ∀ iteration, HeterogeneousBatchTrace BatchIndex Data iteration → State)
    (iteration : ℕ) :
    IsMarkovKernel
      (adaptiveFreshHeterogeneousTraceKernel BatchIndex dataLaw stateOfHistory iteration) where
  isProbabilityMeasure historyPrefix := by
    unfold adaptiveFreshHeterogeneousTraceKernel Kernel.ofFunOfCountable
    change IsProbabilityMeasure
      ((pmfProduct (BatchIndex iteration) Data
        (dataLaw (stateOfHistory iteration
          (heterogeneousBatchTraceOfPrefix iteration historyPrefix)))).toMeasure)
    infer_instance

/-- For a singleton batch index, the fresh-batch kernel's observable value has
exactly the history-selected data law. -/
theorem adaptiveFreshHeterogeneousTraceKernel_punit_map_apply
    {State Data : Type*} [MeasurableSpace Data] [MeasurableSingletonClass Data]
    [Fintype Data] [DecidableEq Data]
    (dataLaw : State → PMF Data)
    (stateOfHistory : ∀ iteration, HeterogeneousBatchTrace (fun _ : ℕ => PUnit) Data iteration →
      State)
    (iteration : ℕ)
    (historyPrefix : (i : Finset.Iic iteration) →
      HeterogeneousBatchTraceCoordinate (fun _ : ℕ => PUnit) Data i.1) :
    (adaptiveFreshHeterogeneousTraceKernel (fun _ : ℕ => PUnit) dataLaw stateOfHistory iteration
      historyPrefix).map (fun batch => batch PUnit.unit) =
        (dataLaw (stateOfHistory iteration
          (heterogeneousBatchTraceOfPrefix iteration historyPrefix))).toMeasure := by
  unfold adaptiveFreshHeterogeneousTraceKernel Kernel.ofFunOfCountable
  change Measure.map (fun batch : PUnit → Data => batch PUnit.unit)
      (PMF.toMeasure (pmfProduct PUnit Data
        (dataLaw (stateOfHistory iteration
          (heterogeneousBatchTraceOfPrefix iteration historyPrefix))))) = _
  rw [PMF.toMeasure_map]
  · simp
  · exact measurable_of_countable _

/-- The common law of an infinite, history-adaptive stream of fresh IID
batches.  It realizes every round on one probability space, with the
history-selected IID law exposed by the conditional-distribution theorem
below. -/
noncomputable def adaptiveFreshHeterogeneousInfiniteTraceLaw
    {State Data : Type*} [MeasurableSpace Data] [MeasurableSingletonClass Data]
    [Fintype Data] [DecidableEq Data]
    (BatchIndex : ℕ → Type*) [∀ round, Fintype (BatchIndex round)]
    [∀ round, DecidableEq (BatchIndex round)]
    (dataLaw : State → PMF Data)
    (stateOfHistory : ∀ iteration, HeterogeneousBatchTrace BatchIndex Data iteration → State) :
    Measure ((i : ℕ) → HeterogeneousBatchTraceCoordinate BatchIndex Data i) :=
  Kernel.trajMeasure (Measure.dirac PUnit.unit)
    (adaptiveFreshHeterogeneousTraceKernel BatchIndex dataLaw stateOfHistory)

instance adaptiveFreshHeterogeneousInfiniteTraceLaw.isProbabilityMeasure
    {State Data : Type*} [MeasurableSpace Data] [MeasurableSingletonClass Data]
    [Fintype Data] [DecidableEq Data]
    (BatchIndex : ℕ → Type*) [∀ round, Fintype (BatchIndex round)]
    [∀ round, DecidableEq (BatchIndex round)]
    (dataLaw : State → PMF Data)
    (stateOfHistory : ∀ iteration, HeterogeneousBatchTrace BatchIndex Data iteration → State) :
    IsProbabilityMeasure
      (adaptiveFreshHeterogeneousInfiniteTraceLaw BatchIndex dataLaw stateOfHistory) := by
  unfold adaptiveFreshHeterogeneousInfiniteTraceLaw
  infer_instance

/-- The adaptive fresh-trace law is the trajectory law started from its unique
dummy coordinate-zero prefix.  This exposes the full future-trajectory kernel,
not only its next-coordinate marginal. -/
theorem adaptiveFreshHeterogeneousInfiniteTraceLaw_eq_traj
    {State Data : Type*} [MeasurableSpace Data] [MeasurableSingletonClass Data]
    [Fintype Data] [DecidableEq Data]
    (BatchIndex : ℕ → Type*) [∀ round, Fintype (BatchIndex round)]
    [∀ round, DecidableEq (BatchIndex round)]
    (dataLaw : State → PMF Data)
    (stateOfHistory : ∀ iteration, HeterogeneousBatchTrace BatchIndex Data iteration → State) :
    adaptiveFreshHeterogeneousInfiniteTraceLaw BatchIndex dataLaw stateOfHistory =
      Kernel.traj (adaptiveFreshHeterogeneousTraceKernel BatchIndex dataLaw stateOfHistory) 0
        ((MeasurableEquiv.piUnique
          (fun i : Finset.Iic 0 => HeterogeneousBatchTraceCoordinate BatchIndex Data i.1)).symm
          PUnit.unit) := by
  unfold adaptiveFreshHeterogeneousInfiniteTraceLaw Kernel.trajMeasure
  have hmap : Measure.map
      ((MeasurableEquiv.piUnique
        (fun i : Finset.Iic 0 => HeterogeneousBatchTraceCoordinate BatchIndex Data i.1)).symm)
      (Measure.dirac PUnit.unit) =
      Measure.dirac
        ((MeasurableEquiv.piUnique
          (fun i : Finset.Iic 0 => HeterogeneousBatchTraceCoordinate BatchIndex Data i.1)).symm
          PUnit.unit) := by
    exact Measure.map_dirac' (by fun_prop) _
  change Measure.bind
    (Measure.map
      ((MeasurableEquiv.piUnique
        (fun i : Finset.Iic 0 => HeterogeneousBatchTraceCoordinate BatchIndex Data i.1)).symm)
      (Measure.dirac PUnit.unit))
    (Kernel.traj (adaptiveFreshHeterogeneousTraceKernel BatchIndex dataLaw stateOfHistory) 0) = _
  rw [hmap]
  rw [Measure.dirac_bind (Kernel.measurable _)]

/-- Every finite decoded prefix of the common infinite adaptive trace has the
same law as the recursively defined finite adaptive PMF trace. -/
theorem adaptiveFreshHeterogeneousInfiniteTraceLaw_map_trace_eq
    {State Data : Type*} [MeasurableSpace Data] [MeasurableSingletonClass Data]
    [Fintype Data] [DecidableEq Data]
    (BatchIndex : ℕ → Type*) [∀ round, Fintype (BatchIndex round)]
    [∀ round, DecidableEq (BatchIndex round)]
    (dataLaw : State → PMF Data)
    (stateOfHistory : ∀ iteration, HeterogeneousBatchTrace BatchIndex Data iteration → State)
    (rounds : ℕ) :
    (adaptiveFreshHeterogeneousInfiniteTraceLaw BatchIndex dataLaw stateOfHistory).map
      (heterogeneousBatchTraceOfInfiniteTrace rounds) =
      (adaptiveFreshHeterogeneousTraceLaw BatchIndex dataLaw stateOfHistory rounds).toMeasure := by
  classical
  let kernel := adaptiveFreshHeterogeneousTraceKernel BatchIndex dataLaw stateOfHistory
  let initialPrefix : (i : Finset.Iic 0) →
      HeterogeneousBatchTraceCoordinate BatchIndex Data i.1 :=
    fun i => by
      have hi : i.1 = 0 := Nat.eq_zero_of_le_zero (Finset.mem_Iic.mp i.2)
      simpa [HeterogeneousBatchTraceCoordinate, hi] using PUnit.unit
  have hinfinite : adaptiveFreshHeterogeneousInfiniteTraceLaw BatchIndex dataLaw stateOfHistory =
      Kernel.traj kernel 0 initialPrefix := by
    simpa [kernel, initialPrefix] using
      (adaptiveFreshHeterogeneousInfiniteTraceLaw_eq_traj BatchIndex dataLaw stateOfHistory)
  have hprefixLaw : ∀ round : ℕ,
      Measure.map (heterogeneousBatchTraceOfPrefix round)
        (Kernel.partialTraj kernel 0 round initialPrefix) =
        (adaptiveFreshHeterogeneousTraceLaw BatchIndex dataLaw stateOfHistory round).toMeasure := by
    intro round
    induction round with
    | zero =>
        rw [Kernel.partialTraj_self, Kernel.id_apply, Measure.map_dirac]
        change Measure.dirac _ = (PMF.pure _).toMeasure
        rw [PMF.toMeasure_pure]
        congr
        funext index
        exact Fin.elim0 index
    | succ round ih =>
        let step : HeterogeneousBatchTrace BatchIndex Data round →
            PMF (HeterogeneousBatchTrace BatchIndex Data (round + 1)) := fun history =>
          (pmfProduct (BatchIndex round) Data
            (dataLaw (stateOfHistory round history))).map
            (heterogeneousBatchTraceSnoc history)
        have hfiniteSucc :
            adaptiveFreshHeterogeneousTraceLaw BatchIndex dataLaw stateOfHistory (round + 1) =
              (adaptiveFreshHeterogeneousTraceLaw BatchIndex dataLaw stateOfHistory round).bind step := by
          rfl
        have hnext (historyPrefix : (index : Finset.Iic round) →
            HeterogeneousBatchTraceCoordinate BatchIndex Data index.1) :
            Measure.map (heterogeneousBatchTraceOfPrefix (round + 1))
              (Kernel.partialTraj kernel round (round + 1) historyPrefix) =
              (step (heterogeneousBatchTraceOfPrefix round historyPrefix)).toMeasure := by
          have hdecode_succ (next : HeterogeneousBatchTraceCoordinate BatchIndex Data (round + 1)) :
              heterogeneousBatchTraceOfPrefix (round + 1)
                (IicProdIoc round (round + 1)
                  (historyPrefix, MeasurableEquiv.piSingleton round next)) =
                heterogeneousBatchTraceSnoc
                (heterogeneousBatchTraceOfPrefix round historyPrefix) next := by
            funext stage
            refine Fin.lastCases ?_ (fun previous => ?_) stage
            · funext index
              simp [heterogeneousBatchTraceOfPrefix, heterogeneousBatchTraceSnoc,
                IicProdIoc, MeasurableEquiv.piSingleton]
            · funext index
              simp [heterogeneousBatchTraceOfPrefix, heterogeneousBatchTraceSnoc,
                IicProdIoc]
          have hpi : Measurable (MeasurableEquiv.piSingleton
              (X := fun index : ℕ => HeterogeneousBatchTraceCoordinate BatchIndex Data index)
              round) :=
            (MeasurableEquiv.piSingleton
              (X := fun index : ℕ => HeterogeneousBatchTraceCoordinate BatchIndex Data index)
              round).measurable
          have hdecode : Measurable (heterogeneousBatchTraceOfPrefix (round + 1)) :=
            measurable_heterogeneousBatchTraceOfPrefix
              (BatchIndex := BatchIndex) (Data := Data) (round + 1)
          have happend : Measurable (IicProdIoc (X := fun index : ℕ =>
              HeterogeneousBatchTraceCoordinate BatchIndex Data index) round (round + 1)) :=
            measurable_IicProdIoc
          have houter : Measurable (heterogeneousBatchTraceOfPrefix (round + 1) ∘
              IicProdIoc round (round + 1)) := hdecode.comp happend
          rw [Kernel.partialTraj_succ_self]
          rw [← Kernel.map_apply _ hdecode]
          rw [← Kernel.map_comp_right _ happend hdecode]
          rw [Kernel.map_apply _ houter]
          rw [Kernel.prod_apply, Kernel.id_apply]
          rw [Kernel.map_apply _ hpi]
          rw [Measure.dirac_prod]
          have hcombine : Measurable ((heterogeneousBatchTraceOfPrefix (round + 1) ∘
              IicProdIoc round (round + 1)) ∘ Prod.mk historyPrefix) :=
            houter.comp measurable_prodMk_left
          rw [Measure.map_map houter measurable_prodMk_left]
          rw [Measure.map_map hcombine hpi]
          have hmap : ((heterogeneousBatchTraceOfPrefix (round + 1) ∘
              IicProdIoc round (round + 1)) ∘ Prod.mk historyPrefix) ∘
              MeasurableEquiv.piSingleton round =
              heterogeneousBatchTraceSnoc
                (heterogeneousBatchTraceOfPrefix round historyPrefix) := by
            funext next
            exact hdecode_succ next
          rw [hmap]
          change Measure.map (heterogeneousBatchTraceSnoc
              (heterogeneousBatchTraceOfPrefix round historyPrefix))
              (pmfProduct (BatchIndex round) Data
                (dataLaw (stateOfHistory round
                  (heterogeneousBatchTraceOfPrefix round historyPrefix)))).toMeasure =
            (PMF.map (heterogeneousBatchTraceSnoc
              (heterogeneousBatchTraceOfPrefix round historyPrefix))
              (pmfProduct (BatchIndex round) Data
                (dataLaw (stateOfHistory round
                  (heterogeneousBatchTraceOfPrefix round historyPrefix))))).toMeasure
          rw [PMF.toMeasure_map]
          exact measurable_of_countable _
        have hdecodeOld : Measurable (heterogeneousBatchTraceOfPrefix round) :=
          measurable_heterogeneousBatchTraceOfPrefix
            (BatchIndex := BatchIndex) (Data := Data) round
        have hdecodeNext : Measurable (heterogeneousBatchTraceOfPrefix (round + 1)) :=
          measurable_heterogeneousBatchTraceOfPrefix
            (BatchIndex := BatchIndex) (Data := Data) (round + 1)
        have hstepKernel :
            (Kernel.partialTraj kernel round (round + 1)).map
                (heterogeneousBatchTraceOfPrefix (round + 1)) =
              pmfToMeasureKernel step ∘ₖ
                Kernel.deterministic (heterogeneousBatchTraceOfPrefix round) hdecodeOld := by
          apply Kernel.ext
          intro historyPrefix
          rw [Kernel.map_apply _ hdecodeNext, Kernel.comp_apply,
            Kernel.deterministic_apply hdecodeOld,
            Measure.dirac_bind (pmfToMeasureKernel step).measurable]
          simpa [pmfToMeasureKernel, Kernel.ofFunOfCountable] using hnext historyPrefix
        rw [← Kernel.map_apply _ hdecodeNext]
        rw [Kernel.partialTraj_succ_eq_comp (a := 0) (b := round) (by omega)]
        rw [Kernel.map_comp, hstepKernel, Kernel.comp_assoc]
        rw [Kernel.deterministic_comp_eq_map hdecodeOld]
        rw [Kernel.comp_apply, Kernel.map_apply _ hdecodeOld, ih]
        rw [pmfToMeasure_bind_pmfToMeasureKernel_eq_pmf_bind_toMeasure]
        rw [← hfiniteSucc]
  rw [hinfinite]
  let decodeInf : ((index : ℕ) → HeterogeneousBatchTraceCoordinate BatchIndex Data index) →
      HeterogeneousBatchTrace BatchIndex Data rounds :=
    heterogeneousBatchTraceOfInfiniteTrace rounds
  let decodePrefix : ((index : Finset.Iic rounds) →
      HeterogeneousBatchTraceCoordinate BatchIndex Data index.1) →
      HeterogeneousBatchTrace BatchIndex Data rounds :=
    heterogeneousBatchTraceOfPrefix rounds
  have hdecode : decodeInf = decodePrefix ∘ (frestrictLe rounds) := by
    funext trace
    exact (heterogeneousBatchTraceOfPrefix_frestrictLe rounds trace).symm
  have hrestrict : Measurable (frestrictLe
      (π := fun index : ℕ => HeterogeneousBatchTraceCoordinate BatchIndex Data index) rounds) :=
    measurable_frestrictLe rounds
  have hprefix : Measurable decodePrefix :=
    measurable_heterogeneousBatchTraceOfPrefix rounds
  change Measure.map decodeInf ((Kernel.traj kernel 0) initialPrefix) = _
  rw [hdecode, ← Measure.map_map hprefix hrestrict]
  rw [Kernel.traj_map_frestrictLe_apply]
  exact hprefixLaw rounds

/-- Conditional expectation under the common adaptive law is integration over
the Ionescu--Tulcea continuation from the realized finite prefix.  It provides
the full-episode conditional law needed by adaptive trajectory arguments. -/
theorem condExp_adaptiveFreshHeterogeneousInfiniteTraceLaw
    {State Data : Type*} [MeasurableSpace Data] [MeasurableSingletonClass Data]
    [Fintype Data] [DecidableEq Data]
    (BatchIndex : ℕ → Type*) [∀ round, Fintype (BatchIndex round)]
    [∀ round, DecidableEq (BatchIndex round)]
    (dataLaw : State → PMF Data)
    (stateOfHistory : ∀ iteration, HeterogeneousBatchTrace BatchIndex Data iteration → State)
    (iteration : ℕ)
    (f : ((i : ℕ) → HeterogeneousBatchTraceCoordinate BatchIndex Data i) → ℝ)
    (hf : Integrable f
      (adaptiveFreshHeterogeneousInfiniteTraceLaw BatchIndex dataLaw stateOfHistory)) :
    (adaptiveFreshHeterogeneousInfiniteTraceLaw BatchIndex dataLaw stateOfHistory)[f |
        MeasurableSpace.comap (frestrictLe iteration) inferInstance] =ᵐ[
          adaptiveFreshHeterogeneousInfiniteTraceLaw BatchIndex dataLaw stateOfHistory]
      fun trace => ∫ future, f future ∂
        Kernel.traj (adaptiveFreshHeterogeneousTraceKernel BatchIndex dataLaw stateOfHistory)
          iteration (frestrictLe iteration trace) := by
  rw [adaptiveFreshHeterogeneousInfiniteTraceLaw_eq_traj] at hf ⊢
  simpa only [MeasureTheory.Filtration.piLE_eq_comap_frestrictLe] using
    (Kernel.condExp_traj
      (κ := adaptiveFreshHeterogeneousTraceKernel BatchIndex dataLaw stateOfHistory)
      (a := 0) (b := iteration) (zero_le iteration) hf)

/--
The common law of an infinite heterogeneous batch trace driven by explicitly
supplied Markov kernels.  Unlike
`adaptiveFreshHeterogeneousInfiniteTraceLaw`, this does not require a finite
data carrier: the caller supplies the measurability needed to make each
history-dependent batch law a kernel.

This is the appropriate Ionescu--Tulcea boundary for general-law adaptive
sampling.  In particular, a map into probability measures is not silently
treated as a kernel; an application must establish that premise separately.
-/
noncomputable def heterogeneousBatchTraceInfiniteLaw
    {Data : Type*} [MeasurableSpace Data]
    (BatchIndex : ℕ → Type*)
    (kernel : (iteration : ℕ) →
      Kernel
        ((i : Finset.Iic iteration) → HeterogeneousBatchTraceCoordinate BatchIndex Data i.1)
        (HeterogeneousBatchTraceCoordinate BatchIndex Data (iteration + 1)))
    [∀ iteration, IsMarkovKernel (kernel iteration)] :
    Measure ((i : ℕ) → HeterogeneousBatchTraceCoordinate BatchIndex Data i) :=
  Kernel.trajMeasure (Measure.dirac PUnit.unit) kernel

instance heterogeneousBatchTraceInfiniteLaw.isProbabilityMeasure
    {Data : Type*} [MeasurableSpace Data]
    (BatchIndex : ℕ → Type*)
    (kernel : (iteration : ℕ) →
      Kernel
        ((i : Finset.Iic iteration) → HeterogeneousBatchTraceCoordinate BatchIndex Data i.1)
        (HeterogeneousBatchTraceCoordinate BatchIndex Data (iteration + 1)))
    [∀ iteration, IsMarkovKernel (kernel iteration)] :
    IsProbabilityMeasure (heterogeneousBatchTraceInfiniteLaw BatchIndex kernel) := by
  unfold heterogeneousBatchTraceInfiniteLaw
  infer_instance

/-- The event that adaptive round `iteration` is bad on an infinite
heterogeneous trace. -/
def adaptiveFreshHeterogeneousInfiniteTraceBadEvent
    {Data : Type*} (BatchIndex : ℕ → Type*)
    (bad : ∀ iteration, HeterogeneousBatchTrace BatchIndex Data iteration →
      (BatchIndex iteration → Data) → Prop)
    (iteration : ℕ) :
    Set ((i : ℕ) → HeterogeneousBatchTraceCoordinate BatchIndex Data i) :=
  {trace | bad iteration (heterogeneousBatchTraceOfInfiniteTrace iteration trace)
    (trace (iteration + 1))}

/-- The finite-prefix/batch event whose cylinder is an infinite trace's bad
event at one round.  General-law applications supply its measurability. -/
def heterogeneousBatchTraceBadEventPair
    {Data : Type*} (BatchIndex : ℕ → Type*)
    (bad : ∀ iteration, HeterogeneousBatchTrace BatchIndex Data iteration →
      (BatchIndex iteration → Data) → Prop)
    (iteration : ℕ) :
    Set
      (((i : Finset.Iic iteration) → HeterogeneousBatchTraceCoordinate BatchIndex Data i.1) ×
        HeterogeneousBatchTraceCoordinate BatchIndex Data (iteration + 1)) :=
  {pair | bad iteration (heterogeneousBatchTraceOfPrefix iteration pair.1) pair.2}

/--
A measurable finite-prefix/batch event gives a measurable cylinder on a
general heterogeneous infinite trace.  This is the general-law counterpart of
`measurableSet_adaptiveFreshHeterogeneousInfiniteTraceBadEvent`; unlike that
finite-alphabet convenience lemma, it takes the pair-event measurability as an
explicit analytic hypothesis.
-/
theorem measurableSet_adaptiveFreshHeterogeneousInfiniteTraceBadEvent_of_pair
    {Data : Type*} [MeasurableSpace Data]
    (BatchIndex : ℕ → Type*)
    (bad : ∀ iteration, HeterogeneousBatchTrace BatchIndex Data iteration →
      (BatchIndex iteration → Data) → Prop)
    (iteration : ℕ)
    (hevent : MeasurableSet
      (heterogeneousBatchTraceBadEventPair BatchIndex bad iteration)) :
    MeasurableSet
      (adaptiveFreshHeterogeneousInfiniteTraceBadEvent BatchIndex bad iteration) := by
  let pairOfTrace :
      ((i : ℕ) → HeterogeneousBatchTraceCoordinate BatchIndex Data i) →
        ((i : Finset.Iic iteration) → HeterogeneousBatchTraceCoordinate BatchIndex Data i.1) ×
          HeterogeneousBatchTraceCoordinate BatchIndex Data (iteration + 1) :=
    fun trace => (frestrictLe iteration trace, trace (iteration + 1))
  have hpairOfTrace : Measurable pairOfTrace :=
    (measurable_frestrictLe iteration).prodMk (measurable_pi_apply _)
  have hbadEvent :
      adaptiveFreshHeterogeneousInfiniteTraceBadEvent BatchIndex bad iteration =
        pairOfTrace ⁻¹' heterogeneousBatchTraceBadEventPair BatchIndex bad iteration := by
    ext trace
    simp only [adaptiveFreshHeterogeneousInfiniteTraceBadEvent, Set.mem_preimage,
      Set.mem_setOf_eq, pairOfTrace, heterogeneousBatchTraceBadEventPair]
    rw [heterogeneousBatchTraceOfPrefix_frestrictLe]
  rw [hbadEvent]
  exact hpairOfTrace hevent

/--
An all-round bad-event probability bound yields a high-probability safe
property on a general heterogeneous Ionescu--Tulcea trace.  Event
measurability is discharged from the measurable finite prefix/batch events.
-/
theorem one_sub_le_measureReal_heterogeneousBatchTraceInfinite_safe_of_iUnionBad_le
    {Data : Type*} [MeasurableSpace Data]
    (BatchIndex : ℕ → Type*)
    (kernel : (iteration : ℕ) →
      Kernel
        ((i : Finset.Iic iteration) → HeterogeneousBatchTraceCoordinate BatchIndex Data i.1)
        (HeterogeneousBatchTraceCoordinate BatchIndex Data (iteration + 1)))
    [∀ iteration, IsMarkovKernel (kernel iteration)]
    (bad : ∀ iteration, HeterogeneousBatchTrace BatchIndex Data iteration →
      (BatchIndex iteration → Data) → Prop)
    (p : ℝ)
    (hevent : ∀ iteration, MeasurableSet
      (heterogeneousBatchTraceBadEventPair BatchIndex bad iteration))
    (hbad : (heterogeneousBatchTraceInfiniteLaw BatchIndex kernel).real
      (⋃ iteration,
        adaptiveFreshHeterogeneousInfiniteTraceBadEvent BatchIndex bad iteration) ≤ p)
    (safe : Set ((i : ℕ) → HeterogeneousBatchTraceCoordinate BatchIndex Data i))
    (hsafe : ∀ trace, trace ∉ ⋃ iteration,
      adaptiveFreshHeterogeneousInfiniteTraceBadEvent BatchIndex bad iteration → trace ∈ safe) :
    1 - p ≤ (heterogeneousBatchTraceInfiniteLaw BatchIndex kernel).real safe := by
  letI : IsProbabilityMeasure (heterogeneousBatchTraceInfiniteLaw BatchIndex kernel) := by
    infer_instance
  apply one_sub_le_measureReal_of_measureReal_bad_le
    (heterogeneousBatchTraceInfiniteLaw BatchIndex kernel)
    (bad := ⋃ iteration : ℕ,
      adaptiveFreshHeterogeneousInfiniteTraceBadEvent BatchIndex bad iteration)
    (safe := safe) (p := p)
  · apply MeasurableSet.iUnion
    intro iteration
    exact measurableSet_adaptiveFreshHeterogeneousInfiniteTraceBadEvent_of_pair
      BatchIndex bad iteration (hevent iteration)
  · exact hbad
  · intro trace htrace
    exact hsafe trace htrace

/-- A pointwise conditional bound on a measurable general-law round event
controls that event under the common Ionescu--Tulcea trace.  This is the
non-finite counterpart of
`measure_adaptiveFreshHeterogeneousInfiniteTraceBadEvent_le`; the pair-event
measurability hypothesis is intentionally explicit. -/
theorem measure_heterogeneousBatchTraceInfiniteBadEvent_le
    {Data : Type*} [MeasurableSpace Data]
    (BatchIndex : ℕ → Type*)
    (kernel : (iteration : ℕ) →
      Kernel
        ((i : Finset.Iic iteration) → HeterogeneousBatchTraceCoordinate BatchIndex Data i.1)
        (HeterogeneousBatchTraceCoordinate BatchIndex Data (iteration + 1)))
    [∀ iteration, IsMarkovKernel (kernel iteration)]
    (bad : ∀ iteration, HeterogeneousBatchTrace BatchIndex Data iteration →
      (BatchIndex iteration → Data) → Prop)
    (iteration : ℕ) (failure : ℝ≥0∞)
    (hevent : MeasurableSet
      (heterogeneousBatchTraceBadEventPair BatchIndex bad iteration))
    (hfailure : ∀ historyPrefix,
      kernel iteration historyPrefix
        {batch | bad iteration (heterogeneousBatchTraceOfPrefix iteration historyPrefix) batch} ≤
        failure) :
    heterogeneousBatchTraceInfiniteLaw BatchIndex kernel
      (adaptiveFreshHeterogeneousInfiniteTraceBadEvent BatchIndex bad iteration) ≤ failure := by
  let pairOfTrace :
      ((i : ℕ) → HeterogeneousBatchTraceCoordinate BatchIndex Data i) →
        ((i : Finset.Iic iteration) → HeterogeneousBatchTraceCoordinate BatchIndex Data i.1) ×
          HeterogeneousBatchTraceCoordinate BatchIndex Data (iteration + 1) :=
    fun trace => (frestrictLe iteration trace, trace (iteration + 1))
  have hpairOfTrace : Measurable pairOfTrace :=
    (measurable_frestrictLe iteration).prodMk (measurable_pi_apply _)
  have hbadEvent :
      adaptiveFreshHeterogeneousInfiniteTraceBadEvent BatchIndex bad iteration =
        pairOfTrace ⁻¹' heterogeneousBatchTraceBadEventPair BatchIndex bad iteration := by
    ext trace
    simp only [adaptiveFreshHeterogeneousInfiniteTraceBadEvent, Set.mem_preimage,
      Set.mem_setOf_eq, pairOfTrace, heterogeneousBatchTraceBadEventPair]
    rw [heterogeneousBatchTraceOfPrefix_frestrictLe]
  have htrajectory := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (X := HeterogeneousBatchTraceCoordinate BatchIndex Data)
    (μ₀ := Measure.dirac PUnit.unit) (κ := kernel) (a := iteration)
  calc
    heterogeneousBatchTraceInfiniteLaw BatchIndex kernel
        (adaptiveFreshHeterogeneousInfiniteTraceBadEvent BatchIndex bad iteration) =
        (heterogeneousBatchTraceInfiniteLaw BatchIndex kernel).map pairOfTrace
          (heterogeneousBatchTraceBadEventPair BatchIndex bad iteration) := by
      rw [Measure.map_apply hpairOfTrace hevent, ← hbadEvent]
    _ =
        ((heterogeneousBatchTraceInfiniteLaw BatchIndex kernel).map
          (frestrictLe iteration) ⊗ₘ kernel iteration)
          (heterogeneousBatchTraceBadEventPair BatchIndex bad iteration) := by
      simpa only [heterogeneousBatchTraceInfiniteLaw, pairOfTrace] using
        congrArg (fun measure =>
          measure (heterogeneousBatchTraceBadEventPair BatchIndex bad iteration)) htrajectory.symm
    _ = ∫⁻ historyPrefix,
        kernel iteration historyPrefix
          (Prod.mk historyPrefix ⁻¹'
            heterogeneousBatchTraceBadEventPair BatchIndex bad iteration) ∂
          (heterogeneousBatchTraceInfiniteLaw BatchIndex kernel).map (frestrictLe iteration) :=
      Measure.compProd_apply hevent
    _ ≤ ∫⁻ _ : (i : Finset.Iic iteration) →
          HeterogeneousBatchTraceCoordinate BatchIndex Data i.1,
        failure ∂ (heterogeneousBatchTraceInfiniteLaw BatchIndex kernel).map
          (frestrictLe iteration) := by
      apply lintegral_mono
      intro historyPrefix
      simpa only [heterogeneousBatchTraceBadEventPair, Set.mem_preimage, Set.mem_setOf_eq]
        using hfailure historyPrefix
    _ = failure := by
      letI : IsProbabilityMeasure (heterogeneousBatchTraceInfiniteLaw BatchIndex kernel) := by
        infer_instance
      have hprob : IsProbabilityMeasure
          ((heterogeneousBatchTraceInfiniteLaw BatchIndex kernel).map (frestrictLe iteration)) :=
        Measure.isProbabilityMeasure_map (measurable_frestrictLe iteration).aemeasurable
      simp [hprob.measure_univ]

/-- Real-valued form of
`measure_heterogeneousBatchTraceInfiniteBadEvent_le`. -/
theorem measureReal_heterogeneousBatchTraceInfiniteBadEvent_le
    {Data : Type*} [MeasurableSpace Data]
    (BatchIndex : ℕ → Type*)
    (kernel : (iteration : ℕ) →
      Kernel
        ((i : Finset.Iic iteration) → HeterogeneousBatchTraceCoordinate BatchIndex Data i.1)
        (HeterogeneousBatchTraceCoordinate BatchIndex Data (iteration + 1)))
    [∀ iteration, IsMarkovKernel (kernel iteration)]
    (bad : ∀ iteration, HeterogeneousBatchTrace BatchIndex Data iteration →
      (BatchIndex iteration → Data) → Prop)
    (iteration : ℕ) (failure : ℝ) (hfailure_nonneg : 0 ≤ failure)
    (hevent : MeasurableSet
      (heterogeneousBatchTraceBadEventPair BatchIndex bad iteration))
    (hfailure : ∀ historyPrefix,
      kernel iteration historyPrefix
        {batch | bad iteration (heterogeneousBatchTraceOfPrefix iteration historyPrefix) batch} ≤
        ENNReal.ofReal failure) :
    (heterogeneousBatchTraceInfiniteLaw BatchIndex kernel).real
      (adaptiveFreshHeterogeneousInfiniteTraceBadEvent BatchIndex bad iteration) ≤ failure := by
  unfold Measure.real
  calc
    (heterogeneousBatchTraceInfiniteLaw BatchIndex kernel
        (adaptiveFreshHeterogeneousInfiniteTraceBadEvent BatchIndex bad iteration)).toReal ≤
        (ENNReal.ofReal failure).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top
        (measure_heterogeneousBatchTraceInfiniteBadEvent_le BatchIndex kernel bad iteration
          (ENNReal.ofReal failure) hevent hfailure)
    _ = failure := ENNReal.toReal_ofReal hfailure_nonneg

/-- Each round bad event is a measurable cylinder in the infinite adaptive
trace.  Finiteness and measurable singletons make the event on the finite
history/batch pair measurable, while Mathlib's measurable prefix restriction
and coordinate evaluation provide the cylinder map. -/
theorem measurableSet_adaptiveFreshHeterogeneousInfiniteTraceBadEvent
    {Data : Type*}
    [MeasurableSpace Data] [MeasurableSingletonClass Data]
    [Fintype Data] [DecidableEq Data]
    (BatchIndex : ℕ → Type*) [∀ round, Fintype (BatchIndex round)]
    [∀ round, DecidableEq (BatchIndex round)]
    (bad : ∀ iteration, HeterogeneousBatchTrace BatchIndex Data iteration →
      (BatchIndex iteration → Data) → Prop)
    (iteration : ℕ) :
    MeasurableSet (adaptiveFreshHeterogeneousInfiniteTraceBadEvent BatchIndex bad iteration) := by
  let eventPair : Set
      (((i : Finset.Iic iteration) → HeterogeneousBatchTraceCoordinate BatchIndex Data i.1) ×
        HeterogeneousBatchTraceCoordinate BatchIndex Data (iteration + 1)) :=
    {pair | bad iteration (heterogeneousBatchTraceOfPrefix iteration pair.1) pair.2}
  have heventPair : MeasurableSet eventPair := MeasurableSet.of_discrete
  let pairOfTrace :
      ((i : ℕ) → HeterogeneousBatchTraceCoordinate BatchIndex Data i) →
        ((i : Finset.Iic iteration) → HeterogeneousBatchTraceCoordinate BatchIndex Data i.1) ×
          HeterogeneousBatchTraceCoordinate BatchIndex Data (iteration + 1) :=
    fun trace => (frestrictLe iteration trace, trace (iteration + 1))
  have hpairOfTrace : Measurable pairOfTrace :=
    (measurable_frestrictLe iteration).prodMk (measurable_pi_apply _)
  have hbadEvent :
      adaptiveFreshHeterogeneousInfiniteTraceBadEvent BatchIndex bad iteration =
        pairOfTrace ⁻¹' eventPair := by
    ext trace
    simp only [adaptiveFreshHeterogeneousInfiniteTraceBadEvent, Set.mem_preimage,
      Set.mem_setOf_eq, pairOfTrace, eventPair]
    rw [heterogeneousBatchTraceOfPrefix_frestrictLe]
  rw [hbadEvent]
  exact hpairOfTrace heventPair

/-- If an infinite adaptive trace belongs to none of its round bad events,
then every finite prefix is free of the recursively accumulated bad event.
This is the deterministic bridge from an all-rounds Ionescu--Tulcea event to
the finite-prefix recursion used by adaptive algorithms. -/
theorem not_adaptiveFreshHeterogeneousTraceAnyBadEvent_of_not_iUnion_infiniteBadEvent
    {BatchIndex : ℕ → Type*} {Data : Type*}
    (bad : ∀ iteration, HeterogeneousBatchTrace BatchIndex Data iteration →
      (BatchIndex iteration → Data) → Prop)
    (trace : (i : ℕ) → HeterogeneousBatchTraceCoordinate BatchIndex Data i)
    (iteration : ℕ)
    (hgood : trace ∉ ⋃ round,
      adaptiveFreshHeterogeneousInfiniteTraceBadEvent BatchIndex bad round) :
    ¬ adaptiveFreshHeterogeneousTraceAnyBadEvent BatchIndex bad iteration
      (heterogeneousBatchTraceOfInfiniteTrace iteration trace) := by
  induction iteration with
  | zero => simp [adaptiveFreshHeterogeneousTraceAnyBadEvent]
  | succ iteration ih =>
      intro hbad
      change adaptiveFreshHeterogeneousTraceAnyBadEvent BatchIndex bad iteration
          (heterogeneousBatchTraceOfInfiniteTrace iteration trace) ∨
        bad iteration (heterogeneousBatchTraceOfInfiniteTrace iteration trace)
          (trace (iteration + 1)) at hbad
      cases hbad with
      | inl hprevious => exact ih hprevious
      | inr hround =>
          apply hgood
          exact Set.mem_iUnion.mpr ⟨iteration, hround⟩

/--
If an infinite adaptive trace is outside the union of round bad events, its
actual sampled batch is good at every particular round.  This is the
one-step version of the prefix-safe bridge, useful for deterministic
recurrences along a fixed trace.
-/
theorem not_adaptiveFreshHeterogeneousInfiniteTraceBadEvent_of_not_iUnion
    {BatchIndex : ℕ → Type*} {Data : Type*}
    (bad : ∀ iteration, HeterogeneousBatchTrace BatchIndex Data iteration →
      (BatchIndex iteration → Data) → Prop)
    (trace : (i : ℕ) → HeterogeneousBatchTraceCoordinate BatchIndex Data i)
    (iteration : ℕ)
    (hgood : trace ∉ ⋃ round,
      adaptiveFreshHeterogeneousInfiniteTraceBadEvent BatchIndex bad round) :
    ¬ bad iteration (heterogeneousBatchTraceOfInfiniteTrace iteration trace)
      (trace (iteration + 1)) := by
  intro hbad
  apply hgood
  exact Set.mem_iUnion.mpr ⟨iteration, hbad⟩

/-- A pointwise conditional bound on a history-adaptive round event bounds
the same round event under the common infinite trace law.  The statement is
in `ℝ≥0∞`, avoiding an artificial conversion between finite-PMF probabilities
and measure probabilities. -/
theorem measure_adaptiveFreshHeterogeneousInfiniteTraceBadEvent_le
    {State Data : Type*} [MeasurableSpace Data] [MeasurableSingletonClass Data]
    [Fintype Data] [DecidableEq Data]
    (BatchIndex : ℕ → Type*) [∀ round, Fintype (BatchIndex round)]
    [∀ round, DecidableEq (BatchIndex round)]
    (dataLaw : State → PMF Data)
    (stateOfHistory : ∀ iteration, HeterogeneousBatchTrace BatchIndex Data iteration → State)
    (bad : ∀ iteration, HeterogeneousBatchTrace BatchIndex Data iteration →
      (BatchIndex iteration → Data) → Prop)
    (iteration : ℕ) (failure : ℝ≥0∞)
    (hfailure : ∀ historyPrefix,
      (pmfProduct (BatchIndex iteration) Data
        (dataLaw (stateOfHistory iteration
          (heterogeneousBatchTraceOfPrefix iteration historyPrefix)))).toMeasure
          {batch | bad iteration
            (heterogeneousBatchTraceOfPrefix iteration historyPrefix) batch} ≤ failure) :
    adaptiveFreshHeterogeneousInfiniteTraceLaw BatchIndex dataLaw stateOfHistory
      (adaptiveFreshHeterogeneousInfiniteTraceBadEvent BatchIndex bad iteration) ≤ failure := by
  let eventPair : Set
      (((i : Finset.Iic iteration) → HeterogeneousBatchTraceCoordinate BatchIndex Data i.1) ×
        HeterogeneousBatchTraceCoordinate BatchIndex Data (iteration + 1)) :=
    {pair | bad iteration (heterogeneousBatchTraceOfPrefix iteration pair.1) pair.2}
  have heventPair : MeasurableSet eventPair := MeasurableSet.of_discrete
  let pairOfTrace :
      ((i : ℕ) → HeterogeneousBatchTraceCoordinate BatchIndex Data i) →
        ((i : Finset.Iic iteration) → HeterogeneousBatchTraceCoordinate BatchIndex Data i.1) ×
          HeterogeneousBatchTraceCoordinate BatchIndex Data (iteration + 1) :=
    fun trace => (frestrictLe iteration trace, trace (iteration + 1))
  have hpairOfTrace : Measurable pairOfTrace :=
    (measurable_frestrictLe iteration).prodMk (measurable_pi_apply _)
  have hbadEvent :
      adaptiveFreshHeterogeneousInfiniteTraceBadEvent BatchIndex bad iteration =
        pairOfTrace ⁻¹' eventPair := by
    ext trace
    simp only [adaptiveFreshHeterogeneousInfiniteTraceBadEvent, Set.mem_preimage,
      Set.mem_setOf_eq, pairOfTrace, eventPair]
    rw [heterogeneousBatchTraceOfPrefix_frestrictLe]
  have htrajectory := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (X := HeterogeneousBatchTraceCoordinate BatchIndex Data)
    (μ₀ := Measure.dirac PUnit.unit)
    (κ := adaptiveFreshHeterogeneousTraceKernel BatchIndex dataLaw stateOfHistory)
    (a := iteration)
  calc
    adaptiveFreshHeterogeneousInfiniteTraceLaw BatchIndex dataLaw stateOfHistory
        (adaptiveFreshHeterogeneousInfiniteTraceBadEvent BatchIndex bad iteration) =
        (adaptiveFreshHeterogeneousInfiniteTraceLaw BatchIndex dataLaw stateOfHistory).map
          pairOfTrace eventPair := by
      rw [Measure.map_apply hpairOfTrace heventPair, ← hbadEvent]
    _ =
        ((adaptiveFreshHeterogeneousInfiniteTraceLaw BatchIndex dataLaw stateOfHistory).map
          (frestrictLe iteration) ⊗ₘ
          adaptiveFreshHeterogeneousTraceKernel BatchIndex dataLaw stateOfHistory iteration)
          eventPair := by
      simpa only [adaptiveFreshHeterogeneousInfiniteTraceLaw, pairOfTrace] using
        congrArg (fun measure => measure eventPair) htrajectory.symm
    _ = ∫⁻ historyPrefix,
        (adaptiveFreshHeterogeneousTraceKernel BatchIndex dataLaw stateOfHistory iteration)
          historyPrefix (Prod.mk historyPrefix ⁻¹' eventPair) ∂
        (adaptiveFreshHeterogeneousInfiniteTraceLaw BatchIndex dataLaw stateOfHistory).map
          (frestrictLe iteration) :=
      Measure.compProd_apply heventPair
    _ ≤ ∫⁻ _ : (i : Finset.Iic iteration) →
          HeterogeneousBatchTraceCoordinate BatchIndex Data i.1,
        failure ∂ (adaptiveFreshHeterogeneousInfiniteTraceLaw BatchIndex dataLaw stateOfHistory).map
          (frestrictLe iteration) := by
      apply lintegral_mono
      intro historyPrefix
      simpa only [adaptiveFreshHeterogeneousTraceKernel, Kernel.ofFunOfCountable, eventPair]
        using hfailure historyPrefix
    _ = failure := by
      letI : IsProbabilityMeasure
          (adaptiveFreshHeterogeneousInfiniteTraceLaw BatchIndex dataLaw stateOfHistory) := by
        infer_instance
      have hprob : IsProbabilityMeasure
          ((adaptiveFreshHeterogeneousInfiniteTraceLaw BatchIndex dataLaw stateOfHistory).map
            (frestrictLe iteration)) :=
        Measure.isProbabilityMeasure_map (measurable_frestrictLe iteration).aemeasurable
      simp [hprob.measure_univ]

/-- Real-valued form of
`measure_adaptiveFreshHeterogeneousInfiniteTraceBadEvent_le`. -/
theorem measureReal_adaptiveFreshHeterogeneousInfiniteTraceBadEvent_le
    {State Data : Type*} [MeasurableSpace Data] [MeasurableSingletonClass Data]
    [Fintype Data] [DecidableEq Data]
    (BatchIndex : ℕ → Type*) [∀ round, Fintype (BatchIndex round)]
    [∀ round, DecidableEq (BatchIndex round)]
    (dataLaw : State → PMF Data)
    (stateOfHistory : ∀ iteration, HeterogeneousBatchTrace BatchIndex Data iteration → State)
    (bad : ∀ iteration, HeterogeneousBatchTrace BatchIndex Data iteration →
      (BatchIndex iteration → Data) → Prop)
    (iteration : ℕ) (failure : ℝ) (hfailure_nonneg : 0 ≤ failure)
    (hfailure : ∀ historyPrefix,
      (pmfProduct (BatchIndex iteration) Data
        (dataLaw (stateOfHistory iteration
          (heterogeneousBatchTraceOfPrefix iteration historyPrefix)))).toMeasure
          {batch | bad iteration
            (heterogeneousBatchTraceOfPrefix iteration historyPrefix) batch} ≤
              ENNReal.ofReal failure) :
    (adaptiveFreshHeterogeneousInfiniteTraceLaw BatchIndex dataLaw stateOfHistory).real
      (adaptiveFreshHeterogeneousInfiniteTraceBadEvent BatchIndex bad iteration) ≤ failure := by
  unfold Measure.real
  calc
    (adaptiveFreshHeterogeneousInfiniteTraceLaw BatchIndex dataLaw stateOfHistory
        (adaptiveFreshHeterogeneousInfiniteTraceBadEvent BatchIndex bad iteration)).toReal ≤
        (ENNReal.ofReal failure).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top
        (measure_adaptiveFreshHeterogeneousInfiniteTraceBadEvent_le BatchIndex dataLaw
          stateOfHistory bad iteration (ENNReal.ofReal failure) hfailure)
    _ = failure := ENNReal.toReal_ofReal hfailure_nonneg

/-- Under the common infinite trace law, the conditional distribution of the
next batch after a finite prefix is exactly the history-selected IID batch
law. -/
theorem condDistrib_adaptiveFreshHeterogeneousInfiniteTraceLaw
    {State Data : Type*} [MeasurableSpace Data] [MeasurableSingletonClass Data]
    [Fintype Data] [DecidableEq Data] [Nonempty Data]
    (BatchIndex : ℕ → Type*) [∀ round, Fintype (BatchIndex round)]
    [∀ round, DecidableEq (BatchIndex round)]
    (dataLaw : State → PMF Data)
    (stateOfHistory : ∀ iteration, HeterogeneousBatchTrace BatchIndex Data iteration → State)
    (iteration : ℕ) :
    condDistrib (fun trace => trace (iteration + 1)) (frestrictLe iteration)
      (adaptiveFreshHeterogeneousInfiniteTraceLaw BatchIndex dataLaw stateOfHistory)
      =ᵐ[(adaptiveFreshHeterogeneousInfiniteTraceLaw BatchIndex dataLaw stateOfHistory).map
        (frestrictLe iteration)]
      adaptiveFreshHeterogeneousTraceKernel BatchIndex dataLaw stateOfHistory iteration := by
  apply Kernel.condDistrib_trajMeasure

end AppliedModelingLib
