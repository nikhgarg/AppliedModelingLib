import AppliedModelingLib.Queueing.ManyServerMarkedStateTrajectory
import AppliedModelingLib.Queueing.MM1.TwoSided.ReverseFiniteWindows
import AppliedModelingLib.Queueing.MM1.TwoSided.FullStationarity
import AppliedModelingLib.Foundations.Probability.PoissonFiniteHorizonMarkedThinning
import AppliedModelingLib.Foundations.Probability.IidPrefixStopping
import Mathlib.Probability.Independence.Process.Basic
import Mathlib.Tactic

/-!
# Finite iid mark prefixes of the many-server uniformization

The augmented many-server embedded chain retains the current potential-event
mark.  This module proves that every finite prefix of those marks has the
literal finite iid Bernoulli product law, jointly independent of the initial
queue state.  It is a discrete-time construction step only: no Poisson clock,
continuous-time thinning, or functional convergence is asserted here.
-/

namespace AppliedModelingLib.Probability.Queueing

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

/-- The finite iid product measure on Boolean potential-event marks. -/
def manyServerIidMarkPrefix (markLaw : Measure Bool) (n : ℕ) :
    Measure (Fin n → Bool) :=
  Measure.pi (fun _ => markLaw)

/-- The complete potential-event mark path retained by an augmented
many-server trajectory. -/
def manyServerMarkedStateArrivalMarkPath (path : ℕ → ℕ × Bool) : ℕ → Bool :=
  fun index => (path index).2

/-- The retained complete mark path is Borel measurable. -/
theorem measurable_manyServerMarkedStateArrivalMarkPath :
    Measurable (manyServerMarkedStateArrivalMarkPath) := by
  apply measurable_pi_lambda
  intro index
  exact measurable_snd.comp (measurable_pi_apply index)

/-- Append one fresh mark to a finite Boolean mark prefix. -/
def manyServerAppendMarkPrefix (n : ℕ) :
    (ℕ × (Fin (n + 1) → Bool)) × Bool → ℕ × (Fin (n + 2) → Bool) :=
  fun value => (value.1.1, snocWindow value.1.2 value.2)

theorem measurable_manyServerAppendMarkPrefix (n : ℕ) :
    Measurable (manyServerAppendMarkPrefix n) :=
  measurable_of_countable _

/-- The iid prefix law extends by appending one independent mark. -/
theorem manyServerIidMarkPrefix_snoc
    (markLaw : Measure Bool) [IsProbabilityMeasure markLaw] (n : ℕ) :
    Measure.map (fun value : (Fin (n + 1) → Bool) × Bool =>
      snocWindow value.1 value.2)
      ((manyServerIidMarkPrefix markLaw (n + 1)).prod markLaw) =
      manyServerIidMarkPrefix markLaw (n + 2) := by
  let equiv := MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (n + 2) => Bool) (Fin.last (n + 1))
  have hequiv := measurePreserving_piFinSuccAbove
    (fun _ : Fin (n + 2) => markLaw) (Fin.last (n + 1))
  have hfun :
      (fun value : (Fin (n + 1) → Bool) × Bool =>
        snocWindow value.1 value.2) =
        equiv.symm ∘ Prod.swap := by
    funext value
    simp [equiv, snocWindow, Fin.snocEquiv]
  calc
    Measure.map (fun value : (Fin (n + 1) → Bool) × Bool =>
        snocWindow value.1 value.2)
        ((manyServerIidMarkPrefix markLaw (n + 1)).prod markLaw) =
        Measure.map equiv.symm
          (Measure.map Prod.swap
            ((manyServerIidMarkPrefix markLaw (n + 1)).prod markLaw)) := by
              rw [Measure.map_map equiv.symm.measurable measurable_swap, hfun]
    _ = Measure.map equiv.symm
          (markLaw.prod (manyServerIidMarkPrefix markLaw (n + 1))) := by
            rw [Measure.prod_swap]
    _ = manyServerIidMarkPrefix markLaw (n + 2) := by
          simpa [equiv, manyServerIidMarkPrefix] using hequiv.symm.map_eq

/-- Encode one Boolean mark as a length-one prefix. -/
def manyServerSingletonMarkPrefix (mark : Bool) : Fin 1 → Bool := fun _ => mark

theorem manyServerIidMarkPrefix_zero (markLaw : Measure Bool) :
    manyServerIidMarkPrefix markLaw 0 =
      Measure.dirac (fun i : Fin 0 => Fin.elim0 i) := by
  exact Measure.pi_of_empty _ _

theorem manyServerIidMarkPrefix_one_from_singleton
    (markLaw : Measure Bool) [IsProbabilityMeasure markLaw] :
    Measure.map manyServerSingletonMarkPrefix markLaw =
      manyServerIidMarkPrefix markLaw 1 := by
  let equiv := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 1 => Bool) 0
  let empty : Fin 0 → Bool := fun i => Fin.elim0 i
  have hequiv := measurePreserving_piFinSuccAbove
    (fun _ : Fin 1 => markLaw) 0
  have hfun : manyServerSingletonMarkPrefix =
      equiv.symm ∘ fun mark => (mark, empty) := by
    funext mark
    funext i
    fin_cases i
    rfl
  calc
    Measure.map manyServerSingletonMarkPrefix markLaw =
        Measure.map equiv.symm
          (Measure.map (fun mark => (mark, empty)) markLaw) := by
            rw [Measure.map_map equiv.symm.measurable (measurable_of_countable _), hfun]
    _ = Measure.map equiv.symm (markLaw.prod (Measure.dirac empty)) := by
          rw [Measure.prod_dirac]
    _ = Measure.map equiv.symm
          (markLaw.prod (manyServerIidMarkPrefix markLaw 0)) := by
            rw [manyServerIidMarkPrefix_zero]
    _ = manyServerIidMarkPrefix markLaw 1 := by
          simpa [equiv, manyServerIidMarkPrefix] using hequiv.symm.map_eq

/-- Appending a fresh iid mark to a queue-state/mark-prefix product law gives
the next queue-state/longer-prefix product law. -/
theorem manyServerStateIidMarkPrefix_snoc
    (initial : Measure ℕ) (markLaw : Measure Bool)
    [IsProbabilityMeasure initial] [IsProbabilityMeasure markLaw] (n : ℕ) :
    Measure.map (manyServerAppendMarkPrefix n)
      ((initial.prod (manyServerIidMarkPrefix markLaw (n + 1))).prod markLaw) =
      initial.prod (manyServerIidMarkPrefix markLaw (n + 2)) := by
  let prefixLaw : Measure (Fin (n + 1) → Bool) :=
    manyServerIidMarkPrefix markLaw (n + 1)
  let snoc : (Fin (n + 1) → Bool) × Bool → Fin (n + 2) → Bool :=
    fun value => snocWindow value.1 value.2
  have hsnoc : Measurable snoc := measurable_snocWindow (n + 1)
  have hfun : manyServerAppendMarkPrefix n =
      (Prod.map id snoc) ∘ (MeasurableEquiv.prodAssoc :
        ((ℕ × (Fin (n + 1) → Bool)) × Bool) ≃ᵐ
          ℕ × ((Fin (n + 1) → Bool) × Bool)) := by
    rfl
  have hassoc := measurePreserving_prodAssoc initial prefixLaw markLaw
  calc
    Measure.map (manyServerAppendMarkPrefix n)
        ((initial.prod prefixLaw).prod markLaw) =
        Measure.map (Prod.map id snoc)
          (Measure.map MeasurableEquiv.prodAssoc
            ((initial.prod prefixLaw).prod markLaw)) := by
              rw [Measure.map_map (measurable_id.prodMap hsnoc)
                MeasurableEquiv.prodAssoc.measurable, hfun]
    _ = Measure.map (Prod.map id snoc) (initial.prod (prefixLaw.prod markLaw)) := by
          rw [hassoc.map_eq]
    _ = (Measure.map id initial).prod (Measure.map snoc (prefixLaw.prod markLaw)) := by
          rw [Measure.map_prod_map initial (prefixLaw.prod markLaw)
            measurable_id hsnoc]
    _ = initial.prod (manyServerIidMarkPrefix markLaw (n + 2)) := by
          rw [Measure.map_id]
          rw [show Measure.map snoc (prefixLaw.prod markLaw) =
            manyServerIidMarkPrefix markLaw (n + 2) by
              simpa [prefixLaw, snoc] using manyServerIidMarkPrefix_snoc markLaw n]

/-- Retain the initial queue state and the mark prefix in a finite augmented
state window. -/
def manyServerStateMarkPrefix (n : ℕ)
    (window : Fin (n + 1) → ℕ × Bool) : ℕ × (Fin (n + 1) → Bool) :=
  ((window 0).1, fun i => (window i).2)

theorem measurable_manyServerStateMarkPrefix (n : ℕ) :
    Measurable (manyServerStateMarkPrefix n) :=
  measurable_of_countable _

/-- Retain a mark prefix and the current augmented queue state, so that the
next Markov transition may read that current state. -/
def manyServerStateMarkPrefixHistoryLast (n : ℕ)
    (window : Fin (n + 1) → ℕ × Bool) :
    (ℕ × (Fin (n + 1) → Bool)) × (ℕ × Bool) :=
  (manyServerStateMarkPrefix n window, window (Fin.last n))

theorem measurable_manyServerStateMarkPrefixHistoryLast (n : ℕ) :
    Measurable (manyServerStateMarkPrefixHistoryLast n) :=
  measurable_of_countable _

/-- After retaining any countable history with the current augmented state,
one marked transition appends an independent Bernoulli next mark. -/
theorem manyServerRetainedHistory_nextMark_productLaw
    {γ : Type*} [MeasurableSpace γ] [Countable γ] [MeasurableSingletonClass γ]
    (μ : Measure (γ × (ℕ × Bool))) [IsProbabilityMeasure μ]
    (trafficIntensity : ℝ≥0) (servers : ℕ) (hservers : 0 < servers) :
    Measure.map (fun value : (γ × (ℕ × Bool)) × (ℕ × Bool) =>
      (value.1.1, value.2.2))
      (μ ⊗ₘ (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers).prodMkLeft γ) =
      (Measure.map Prod.fst μ).prod
        (manyServerUniformizationArrivalMark trafficIntensity).toMeasure := by
  let markLaw : Measure Bool :=
    (manyServerUniformizationArrivalMark trafficIntensity).toMeasure
  let kernel : Kernel (ℕ × Bool) (ℕ × Bool) :=
    manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers
  let liftedKernel : Kernel (γ × (ℕ × Bool)) (ℕ × Bool) :=
    kernel.prodMkLeft γ
  let output : (γ × (ℕ × Bool)) × (ℕ × Bool) → γ × Bool :=
    fun value => (value.1.1, value.2.2)
  have houtput : Measurable output := measurable_of_countable _
  apply Measure.ext_of_singleton
  rintro ⟨history, nextMark⟩
  let historyEvent : Set (γ × (ℕ × Bool)) := {value | value.1 = history}
  have hhistoryEvent : MeasurableSet historyEvent :=
    (measurableSet_singleton history).preimage measurable_fst
  have hmapHistory : μ historyEvent = Measure.map Prod.fst μ {history} := by
    rw [Measure.map_apply measurable_fst (measurableSet_singleton _)]
    rfl
  have hlocal (stateAndMark : ℕ × Bool) :
      kernel stateAndMark (Prod.snd ⁻¹' ({nextMark} : Set Bool)) =
        markLaw {nextMark} := by
    have hmap : Measure.map Prod.snd (kernel stateAndMark) = markLaw := by
      rw [← Kernel.map_apply kernel (measurable_of_countable _),
        manyServerMarkedStateUniformizationMeasureKernel_map_snd]
      rfl
    have hpoint := congrArg (fun law : Measure Bool => law {nextMark}) hmap
    change Measure.map Prod.snd (kernel stateAndMark) {nextMark} =
      markLaw {nextMark} at hpoint
    rw [Measure.map_apply (measurable_of_countable _)
      (measurableSet_singleton nextMark)] at hpoint
    exact hpoint
  have hfiber (value : γ × (ℕ × Bool)) :
      liftedKernel value
        (Prod.mk value ⁻¹' (output ⁻¹' ({(history, nextMark)} : Set (γ × Bool)))) =
        historyEvent.indicator (fun _ => markLaw {nextMark}) value := by
    by_cases hvalue : value ∈ historyEvent
    · rcases value with ⟨historyValue, stateAndMark⟩
      have hhistoryValue : historyValue = history := hvalue
      change kernel stateAndMark
        (Prod.mk (historyValue, stateAndMark) ⁻¹'
          (output ⁻¹' ({(history, nextMark)} : Set (γ × Bool)))) = _
      rw [show Prod.mk (historyValue, stateAndMark) ⁻¹'
          (output ⁻¹' ({(history, nextMark)} : Set (γ × Bool))) =
            Prod.snd ⁻¹' ({nextMark} : Set Bool) by
              ext nextStateAndMark
              simp [output, hhistoryValue]]
      rw [hlocal]
      simp [historyEvent, hvalue]
    · rcases value with ⟨historyValue, stateAndMark⟩
      have hhistoryValue : historyValue ≠ history := by
        simpa [historyEvent] using hvalue
      change kernel stateAndMark
        (Prod.mk (historyValue, stateAndMark) ⁻¹'
          (output ⁻¹' ({(history, nextMark)} : Set (γ × Bool)))) = _
      rw [show Prod.mk (historyValue, stateAndMark) ⁻¹'
          (output ⁻¹' ({(history, nextMark)} : Set (γ × Bool))) = ∅ by
              ext nextStateAndMark
              simp [output, hhistoryValue]]
      simp [historyEvent, hvalue]
  have hpre : MeasurableSet
      (output ⁻¹' ({(history, nextMark)} : Set (γ × Bool))) :=
    (measurableSet_singleton _).preimage houtput
  change Measure.map output (μ ⊗ₘ liftedKernel) {(history, nextMark)} =
    (Measure.map Prod.fst μ).prod markLaw {(history, nextMark)}
  rw [Measure.map_apply houtput (measurableSet_singleton _),
    Measure.compProd_apply hpre]
  calc
    (∫⁻ value, liftedKernel value
      (Prod.mk value ⁻¹' (output ⁻¹' ({(history, nextMark)} : Set (γ × Bool)))) ∂μ) =
        ∫⁻ value, historyEvent.indicator (fun _ => markLaw {nextMark}) value ∂μ := by
          apply lintegral_congr_ae
          filter_upwards [] with value
          exact hfiber value
    _ = markLaw {nextMark} * μ historyEvent := by
          exact MeasureTheory.lintegral_indicator_const hhistoryEvent (markLaw {nextMark})
    _ = markLaw {nextMark} * Measure.map Prod.fst μ {history} := by
          rw [hmapHistory]
    _ = (Measure.map Prod.fst μ).prod markLaw {(history, nextMark)} := by
          rw [← Set.singleton_prod_singleton, Measure.prod_prod, mul_comm]

/-- One Markov extension of a finite augmented-state window appends one fresh
independent potential-event mark to its retained mark prefix. -/
theorem manyServerStateMarkPrefix_transition
    (ν : Measure (Fin (n + 1) → ℕ × Bool)) [IsProbabilityMeasure ν]
    (trafficIntensity : ℝ≥0) (servers : ℕ) (hservers : 0 < servers) :
    Measure.map (manyServerStateMarkPrefix (n + 1))
      (Measure.map (fun value : (Fin (n + 1) → ℕ × Bool) × (ℕ × Bool) =>
        snocWindow value.1 value.2)
        (ν ⊗ₘ (manyServerMarkedStateUniformizationMeasureKernel
          trafficIntensity servers hservers ∘ₖ
            Kernel.deterministic
              (fun window : Fin (n + 1) → ℕ × Bool => window (Fin.last n))
              (measurable_pi_apply _)))) =
      Measure.map (manyServerAppendMarkPrefix n)
        ((Measure.map (manyServerStateMarkPrefix n) ν).prod
          (manyServerUniformizationArrivalMark trafficIntensity).toMeasure) := by
  let γ : Type := ℕ × (Fin (n + 1) → Bool)
  let kernel : Kernel (ℕ × Bool) (ℕ × Bool) :=
    manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers
  let f : (Fin (n + 1) → ℕ × Bool) → γ × (ℕ × Bool) :=
    manyServerStateMarkPrefixHistoryLast n
  let transition : Kernel (Fin (n + 1) → ℕ × Bool) (ℕ × Bool) :=
    kernel ∘ₖ Kernel.deterministic
      (fun window : Fin (n + 1) → ℕ × Bool => window (Fin.last n))
      (measurable_pi_apply _)
  let snoc : (Fin (n + 1) → ℕ × Bool) × (ℕ × Bool) →
      Fin (n + 2) → ℕ × Bool :=
    fun value => snocWindow value.1 value.2
  let h : (Fin (n + 1) → ℕ × Bool) × (ℕ × Bool) → γ × Bool :=
    fun value => (manyServerStateMarkPrefix n value.1, value.2.2)
  let mark : (γ × (ℕ × Bool)) × (ℕ × Bool) → γ × Bool :=
    fun value => (value.1.1, value.2.2)
  have hf : Measurable f := measurable_manyServerStateMarkPrefixHistoryLast n
  have hsnoc : Measurable snoc := measurable_snocWindow (n + 1)
  have hh : Measurable h := measurable_of_countable _
  have hmark : Measurable mark := measurable_of_countable _
  have happend : Measurable (manyServerAppendMarkPrefix n) :=
    measurable_manyServerAppendMarkPrefix n
  have hframe : Measurable (fun value :
      (Fin (n + 1) → ℕ × Bool) × (ℕ × Bool) => (f value.1, value.2)) :=
    hf.comp measurable_fst |>.prodMk measurable_snd
  have hkernel :
      kernel ∘ₖ Kernel.deterministic
          (fun window : Fin (n + 1) → ℕ × Bool => window (Fin.last n))
          (measurable_pi_apply _) =
        kernel ∘ₖ Kernel.deterministic
          (Prod.snd ∘ f) (measurable_snd.comp hf) := by
    have hread :
        (fun window : Fin (n + 1) → ℕ × Bool => window (Fin.last n)) =
          Prod.snd ∘ f := by
      funext window
      rfl
    exact congrArg (fun L => kernel ∘ₖ L)
      (Kernel.deterministic_congr hread)
  have hproductKernel :
      kernel ∘ₖ Kernel.deterministic Prod.snd measurable_snd =
        kernel.prodMkLeft γ := by
    rw [Kernel.comp_deterministic_eq_comap]
    rfl
  have hthrough :
      Measure.map (fun value :
        (Fin (n + 1) → ℕ × Bool) × (ℕ × Bool) => (f value.1, value.2))
        (ν ⊗ₘ transition) =
        (Measure.map f ν) ⊗ₘ kernel.prodMkLeft γ := by
    change Measure.map (fun value :
      (Fin (n + 1) → ℕ × Bool) × (ℕ × Bool) => (f value.1, value.2))
      (ν ⊗ₘ (kernel ∘ₖ Kernel.deterministic
        (Prod.snd ∘ f) (measurable_snd.comp hf))) = _
    rw [Measure.compProd_map_through ν kernel f hf Prod.snd measurable_snd,
      hproductKernel]
  letI : IsProbabilityMeasure (Measure.map f ν) :=
    Measure.isProbabilityMeasure_map hf.aemeasurable
  have hmarkLaw :
      Measure.map mark ((Measure.map f ν) ⊗ₘ kernel.prodMkLeft γ) =
        (Measure.map (manyServerStateMarkPrefix n) ν).prod
          (manyServerUniformizationArrivalMark trafficIntensity).toMeasure := by
    calc
      Measure.map mark ((Measure.map f ν) ⊗ₘ kernel.prodMkLeft γ) =
          (Measure.map Prod.fst (Measure.map f ν)).prod
            (manyServerUniformizationArrivalMark trafficIntensity).toMeasure := by
              exact manyServerRetainedHistory_nextMark_productLaw
                (Measure.map f ν) trafficIntensity servers hservers
      _ = (Measure.map (manyServerStateMarkPrefix n) ν).prod
            (manyServerUniformizationArrivalMark trafficIntensity).toMeasure := by
              rw [Measure.map_map measurable_fst hf]
              rfl
  calc
    Measure.map (manyServerStateMarkPrefix (n + 1))
        (Measure.map snoc (ν ⊗ₘ transition)) =
        Measure.map (fun value :
          (Fin (n + 1) → ℕ × Bool) × (ℕ × Bool) =>
          manyServerStateMarkPrefix (n + 1) (snoc value)) (ν ⊗ₘ transition) := by
            rw [Measure.map_map (measurable_manyServerStateMarkPrefix (n + 1)) hsnoc]
            rfl
    _ = Measure.map (fun value :
          (Fin (n + 1) → ℕ × Bool) × (ℕ × Bool) =>
          manyServerAppendMarkPrefix n (h value)) (ν ⊗ₘ transition) := by
            congr 1
            funext value
            apply Prod.ext
            · rfl
            · funext i
              refine Fin.lastCases ?_ (fun j => ?_) i
              · simp [manyServerStateMarkPrefix, manyServerAppendMarkPrefix,
                  snoc, h, snocWindow]
              · simp [manyServerStateMarkPrefix, manyServerAppendMarkPrefix,
                  snoc, h, snocWindow]
    _ = Measure.map (manyServerAppendMarkPrefix n)
          (Measure.map h (ν ⊗ₘ transition)) := by
            rw [Measure.map_map happend hh]
            rfl
    _ = Measure.map (manyServerAppendMarkPrefix n)
          (Measure.map mark
            (Measure.map (fun value :
              (Fin (n + 1) → ℕ × Bool) × (ℕ × Bool) =>
              (f value.1, value.2)) (ν ⊗ₘ transition))) := by
            congr 1
            rw [Measure.map_map hmark hframe]
            rfl
    _ = Measure.map (manyServerAppendMarkPrefix n)
          (Measure.map mark ((Measure.map f ν) ⊗ₘ kernel.prodMkLeft γ)) := by
            rw [hthrough]
    _ = _ := by
          rw [hmarkLaw]

/-- Every finite prefix of the augmented many-server trajectory's potential-
event marks has the literal iid Bernoulli product law and is independent of
the initial queue state. -/
theorem manyServerMarkedStateTrajectory_state_markPrefix_hasLaw
    {initial : PMF ℕ} (trafficIntensity : ℝ≥0) (servers : ℕ)
    (hservers : 0 < servers) (n : ℕ) :
    HasLaw (fun path : ℕ → ℕ × Bool =>
      manyServerStateMarkPrefix n (natPrefix n path))
      (initial.toMeasure.prod
        (manyServerIidMarkPrefix
          (manyServerUniformizationArrivalMark trafficIntensity).toMeasure
          (n + 1)))
      (stationaryTrajMeasure
        (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
        (manyServerMarkedStateUniformizationMeasureKernel
          trafficIntensity servers hservers)) := by
  let markLaw : Measure Bool :=
    (manyServerUniformizationArrivalMark trafficIntensity).toMeasure
  let markedInitial : Measure (ℕ × Bool) :=
    (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
  let markedKernel : Kernel (ℕ × Bool) (ℕ × Bool) :=
    manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers
  let trajectory : Measure (ℕ → ℕ × Bool) :=
    stationaryTrajMeasure markedInitial markedKernel
  letI : IsProbabilityMeasure initial.toMeasure := by infer_instance
  letI : IsProbabilityMeasure markLaw := by
    dsimp [markLaw]
    infer_instance
  letI : IsProbabilityMeasure markedInitial := by
    dsimp [markedInitial]
    infer_instance
  letI : IsMarkovKernel markedKernel := by
    dsimp [markedKernel]
    infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  induction n with
  | zero =>
      let base : (ℕ × Bool) → ℕ × (Fin 1 → Bool) :=
        fun stateAndMark => (stateAndMark.1,
          manyServerSingletonMarkPrefix stateAndMark.2)
      have hbase : Measurable base := measurable_of_countable _
      have hstateMark : HasLaw (fun path : ℕ → ℕ × Bool => path 0)
          (initial.toMeasure.prod markLaw) trajectory := by
        refine ⟨(measurable_pi_apply 0).aemeasurable, ?_⟩
        rw [show trajectory = stationaryTrajMeasure markedInitial markedKernel by rfl,
          stationaryTrajMeasure_zero_marginal]
        exact manyServerMarkedStatePMF_toMeasure_eq_prod initial trafficIntensity
      refine ⟨(measurable_manyServerStateMarkPrefix 0 |>.comp
        (measurable_natPrefix 0)).aemeasurable, ?_⟩
      change Measure.map (fun path : ℕ → ℕ × Bool =>
        manyServerStateMarkPrefix 0 (natPrefix 0 path)) trajectory =
        initial.toMeasure.prod (manyServerIidMarkPrefix markLaw 1)
      calc
        Measure.map (fun path : ℕ → ℕ × Bool =>
          manyServerStateMarkPrefix 0 (natPrefix 0 path)) trajectory =
            Measure.map base
              (Measure.map (fun path : ℕ → ℕ × Bool => path 0) trajectory) := by
              symm
              rw [Measure.map_map hbase (measurable_pi_apply 0)]
              congr 1
              funext path
              apply Prod.ext
              · rfl
              · funext i
                fin_cases i
                rfl
        _ = Measure.map base (initial.toMeasure.prod markLaw) := by
              rw [hstateMark.map_eq]
        _ = (Measure.map id initial.toMeasure).prod
            (Measure.map manyServerSingletonMarkPrefix markLaw) := by
              rw [show base = Prod.map id manyServerSingletonMarkPrefix by rfl,
                Measure.map_prod_map initial.toMeasure markLaw
                  measurable_id (measurable_of_countable _)]
        _ = initial.toMeasure.prod (manyServerIidMarkPrefix markLaw 1) := by
              rw [Measure.map_id, manyServerIidMarkPrefix_one_from_singleton]
  | succ n ih =>
      letI : IsProbabilityMeasure (Measure.map (natPrefix n) trajectory) :=
        Measure.isProbabilityMeasure_map (measurable_natPrefix n).aemeasurable
      have hprefix :
          Measure.map (manyServerStateMarkPrefix n)
            (Measure.map (natPrefix n) trajectory) =
            initial.toMeasure.prod (manyServerIidMarkPrefix markLaw (n + 1)) := by
        calc
          Measure.map (manyServerStateMarkPrefix n)
              (Measure.map (natPrefix n) trajectory) =
              Measure.map (fun path : ℕ → ℕ × Bool =>
                manyServerStateMarkPrefix n (natPrefix n path)) trajectory := by
                  rw [Measure.map_map (measurable_manyServerStateMarkPrefix n)
                    (measurable_natPrefix n)]
                  rfl
          _ = initial.toMeasure.prod
              (manyServerIidMarkPrefix markLaw (n + 1)) := by
                simpa [markLaw, markedInitial, markedKernel, trajectory] using ih.map_eq
      refine ⟨(measurable_manyServerStateMarkPrefix (n + 1) |>.comp
        (measurable_natPrefix (n + 1))).aemeasurable, ?_⟩
      change Measure.map (fun path : ℕ → ℕ × Bool =>
        manyServerStateMarkPrefix (n + 1) (natPrefix (n + 1) path)) trajectory =
        initial.toMeasure.prod (manyServerIidMarkPrefix markLaw (n + 2))
      calc
        Measure.map (fun path : ℕ → ℕ × Bool =>
          manyServerStateMarkPrefix (n + 1) (natPrefix (n + 1) path)) trajectory =
            Measure.map (manyServerStateMarkPrefix (n + 1))
              (Measure.map (natPrefix (n + 1)) trajectory) := by
                symm
                rw [Measure.map_map (measurable_manyServerStateMarkPrefix (n + 1))
                  (measurable_natPrefix (n + 1))]
                rfl
        _ = Measure.map (manyServerStateMarkPrefix (n + 1))
              (Measure.map (fun value :
                (Fin (n + 1) → ℕ × Bool) × (ℕ × Bool) =>
                snocWindow value.1 value.2)
                ((Measure.map (natPrefix n) trajectory) ⊗ₘ
                  (markedKernel ∘ₖ Kernel.deterministic
                    (fun window : Fin (n + 1) → ℕ × Bool => window (Fin.last n))
                    (measurable_pi_apply _)))) := by
                  rw [stationaryTrajMeasure_natPrefix_succ]
        _ = Measure.map (manyServerAppendMarkPrefix n)
              ((Measure.map (manyServerStateMarkPrefix n)
                (Measure.map (natPrefix n) trajectory)).prod markLaw) := by
                  simpa [markLaw, markedKernel] using
                    (manyServerStateMarkPrefix_transition
                      (ν := Measure.map (natPrefix n) trajectory)
                      trafficIntensity servers hservers)
        _ = Measure.map (manyServerAppendMarkPrefix n)
              ((initial.toMeasure.prod
                (manyServerIidMarkPrefix markLaw (n + 1))).prod markLaw) := by
                  rw [hprefix]
        _ = initial.toMeasure.prod (manyServerIidMarkPrefix markLaw (n + 2)) := by
                  exact manyServerStateIidMarkPrefix_snoc initial.toMeasure markLaw n

/-- The initial queue-state coordinate is independent of every finite prefix
of retained potential-event marks. -/
theorem manyServerMarkedStateTrajectory_initial_indep_markPrefix
    {initial : PMF ℕ} (trafficIntensity : ℝ≥0) (servers : ℕ)
    (hservers : 0 < servers) (n : ℕ) :
    IndepFun
      (fun path : ℕ → (ℕ × Bool) => (path 0).1)
      (fun path (i : Fin (n + 1)) => (path i).2)
      (stationaryTrajMeasure
        (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
        (manyServerMarkedStateUniformizationMeasureKernel
          trafficIntensity servers hservers)) := by
  let trajectory : Measure (ℕ → (ℕ × Bool)) := stationaryTrajMeasure
    (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
    (manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers)
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  let markLaw : Measure Bool :=
    (manyServerUniformizationArrivalMark trafficIntensity).toMeasure
  let marks : Measure (Fin (n + 1) → Bool) :=
    manyServerIidMarkPrefix markLaw (n + 1)
  letI : IsProbabilityMeasure markLaw := by
    dsimp [markLaw]
    infer_instance
  letI : IsProbabilityMeasure marks := by
    change IsProbabilityMeasure (Measure.pi (fun _ : Fin (n + 1) => markLaw))
    infer_instance
  let state : (ℕ → (ℕ × Bool)) → ℕ := fun path => (path 0).1
  let markPrefix : (ℕ → (ℕ × Bool)) → Fin (n + 1) → Bool :=
    fun path i => (path i).2
  let pair : (ℕ → (ℕ × Bool)) → ℕ × (Fin (n + 1) → Bool) :=
    fun path => (state path, markPrefix path)
  have hprefix : HasLaw pair (initial.toMeasure.prod marks) trajectory := by
    simpa [pair, state, markPrefix, marks, markLaw, trajectory,
      manyServerStateMarkPrefix, natPrefix] using
      (manyServerMarkedStateTrajectory_state_markPrefix_hasLaw
        (initial := initial) trafficIntensity servers hservers n)
  have hpair : Measure.map pair trajectory = initial.toMeasure.prod marks := hprefix.map_eq
  have hpair_meas : Measurable pair := by
    simpa [pair, state, markPrefix] using
      (measurable_manyServerStateMarkPrefix n).comp (measurable_natPrefix n)
  have hstate_meas : Measurable state := by
    change Measurable (Prod.fst ∘ pair)
    exact measurable_fst.comp hpair_meas
  have hpref_meas : Measurable markPrefix := by
    change Measurable (Prod.snd ∘ pair)
    exact measurable_snd.comp hpair_meas
  have hstate : Measure.map state trajectory = initial.toMeasure := by
    change Measure.map (Prod.fst ∘ pair) trajectory = initial.toMeasure
    rw [← Measure.map_map measurable_fst hpair_meas, hpair]
    simp
  have hpref : Measure.map markPrefix trajectory = marks := by
    change Measure.map (Prod.snd ∘ pair) trajectory = marks
    rw [← Measure.map_map measurable_snd hpair_meas, hpair]
    simp
  apply (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
    hstate_meas.aemeasurable hpref_meas.aemeasurable).2
  change Measure.map pair trajectory = (Measure.map state trajectory).prod
    (Measure.map markPrefix trajectory)
  rw [hpair, hstate, hpref]

/-- The finite mark-prefix product is exactly the PMF used by the reusable
finite marked-Poisson thinning construction. -/
theorem manyServerIidMarkPrefix_eq_finiteHorizonIidMarks
    (trafficIntensity : ℝ≥0) (n : ℕ) :
    manyServerIidMarkPrefix
      (manyServerUniformizationArrivalMark trafficIntensity).toMeasure n =
      (FiniteHorizonMarkedPoisson.iidMarks
        (uniformizedBirthProbability trafficIntensity)
        (uniformizedBirthProbability_le_one trafficIntensity) n).toMeasure := by
  apply Measure.ext_of_singleton
  intro marks
  have hsingleton : ({marks} : Set (Fin n → Bool)) =
      Set.univ.pi (fun i : Fin n => ({marks i} : Set Bool)) := by
    ext value
    constructor
    · intro hvalue
      subst value
      simp
    · intro hvalue
      apply funext
      intro i
      simpa using hvalue i (by simp)
  rw [PMF.toMeasure_apply_singleton
    (FiniteHorizonMarkedPoisson.iidMarks
      (uniformizedBirthProbability trafficIntensity)
      (uniformizedBirthProbability_le_one trafficIntensity) n)
      marks (measurableSet_singleton _)]
  change Measure.pi (fun _ : Fin n =>
    (manyServerUniformizationArrivalMark trafficIntensity).toMeasure)
      {marks} = _
  rw [hsingleton, Measure.pi_pi]
  simp [FiniteHorizonMarkedPoisson.iidMarks,
    manyServerUniformizationArrivalMark]

/-- Finite many-server event-mark prefixes have precisely the literal PMF law
used by marked-Poisson thinning. -/
theorem manyServerMarkedStateTrajectory_state_markPrefix_hasLaw_iidMarks
    {initial : PMF ℕ} (trafficIntensity : ℝ≥0) (servers : ℕ)
    (hservers : 0 < servers) (n : ℕ) :
    HasLaw (fun path : ℕ → ℕ × Bool =>
      manyServerStateMarkPrefix n (natPrefix n path))
      (initial.toMeasure.prod
        (FiniteHorizonMarkedPoisson.iidMarks
          (uniformizedBirthProbability trafficIntensity)
          (uniformizedBirthProbability_le_one trafficIntensity)
          (n + 1)).toMeasure)
      (stationaryTrajMeasure
        (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
        (manyServerMarkedStateUniformizationMeasureKernel
          trafficIntensity servers hservers)) := by
  have hprefix := manyServerMarkedStateTrajectory_state_markPrefix_hasLaw
    (initial := initial) trafficIntensity servers hservers n
  rw [manyServerIidMarkPrefix_eq_finiteHorizonIidMarks] at hprefix
  simpa using hprefix

/-- The complete potential-event mark path of an augmented many-server
trajectory is an iid Bernoulli stream, for every initial queue-state law. -/
theorem manyServerMarkedStateTrajectory_arrivalMarkPath_hasLaw
    {initial : PMF ℕ} (trafficIntensity : ℝ≥0) (servers : ℕ)
    (hservers : 0 < servers) :
    HasLaw manyServerMarkedStateArrivalMarkPath
      (IIDStream.measure
        (manyServerUniformizationArrivalMark trafficIntensity).toMeasure)
      (stationaryTrajMeasure
        (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
        (manyServerMarkedStateUniformizationMeasureKernel
          trafficIntensity servers hservers)) := by
  let markLaw : Measure Bool :=
    (manyServerUniformizationArrivalMark trafficIntensity).toMeasure
  let trajectory : Measure (ℕ → ℕ × Bool) := stationaryTrajMeasure
    (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
    (manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers)
  letI : IsProbabilityMeasure initial.toMeasure := by infer_instance
  letI : IsProbabilityMeasure markLaw := by
    dsimp [markLaw]
    infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  apply IIDStream.hasLaw_iidPath_of_hasLaw_positive_prefixes markLaw
    manyServerMarkedStateArrivalMarkPath measurable_manyServerMarkedStateArrivalMarkPath
  intro q hq
  cases q with
  | zero => exact (Nat.ne_of_gt hq rfl).elim
  | succ n =>
      let markPrefix : (ℕ → ℕ × Bool) → ℕ × (Fin (n + 1) → Bool) :=
        fun path => manyServerStateMarkPrefix n (natPrefix n path)
      have hprefix : HasLaw markPrefix
          (initial.toMeasure.prod (manyServerIidMarkPrefix markLaw (n + 1))) trajectory := by
        simpa [markPrefix, markLaw, trajectory] using
          (manyServerMarkedStateTrajectory_state_markPrefix_hasLaw
            (initial := initial) trafficIntensity servers hservers n)
      have hsnd : HasLaw Prod.snd (manyServerIidMarkPrefix markLaw (n + 1))
          (initial.toMeasure.prod (manyServerIidMarkPrefix markLaw (n + 1))) := by
        refine ⟨measurable_snd.aemeasurable, ?_⟩
        rw [Measure.map_snd_prod, measure_univ, one_smul]
      simpa [manyServerMarkedStateArrivalMarkPath, markPrefix, Function.comp_def,
        manyServerIidMarkPrefix] using hsnd.comp hprefix

/-- The initial queue-state coordinate is independent of the complete retained
potential-event mark stream. -/
theorem manyServerMarkedStateTrajectory_initial_indep_arrivalMarkPath
    {initial : PMF ℕ} (trafficIntensity : ℝ≥0) (servers : ℕ)
    (hservers : 0 < servers) :
    IndepFun
      (fun path : ℕ → (ℕ × Bool) => (path 0).1)
      manyServerMarkedStateArrivalMarkPath
      (stationaryTrajMeasure
        (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
        (manyServerMarkedStateUniformizationMeasureKernel
          trafficIntensity servers hservers)) := by
  let trajectory : Measure (ℕ → (ℕ × Bool)) := stationaryTrajMeasure
    (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
    (manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers)
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  apply ProbabilityTheory.IndepFun.indepFun_process
    ((measurable_fst.comp (measurable_pi_apply 0)).comp measurable_id)
    (fun _ => (measurable_pi_apply _).comp
      measurable_manyServerMarkedStateArrivalMarkPath)
  intro indices
  let bound : ℕ := indices.sup id
  have hsubset : indices ⊆ Finset.range (bound + 1) := by
    simpa [bound] using Finset.subset_range_sup_succ indices
  let select : (Fin (bound + 1) → Bool) → indices → Bool :=
    fun marks index => marks ⟨index, Finset.mem_range.mp (hsubset index.property)⟩
  have hselect : Measurable select := by
    apply measurable_pi_lambda
    intro index
    exact measurable_pi_apply _
  have hindependent := manyServerMarkedStateTrajectory_initial_indep_markPrefix
    (initial := initial) trafficIntensity servers hservers bound
  have hcomposed := hindependent.comp measurable_id hselect
  simpa [trajectory, bound, select, Function.comp_def,
    manyServerMarkedStateArrivalMarkPath] using hcomposed

/-- The finite queue-state prefix of the unmarked many-server embedded chain,
defined by its literal one-step PMF recursion. -/
def manyServerUnmarkedStatePrefixPMF
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (servers : ℕ)
    (hservers : 0 < servers) : (n : ℕ) → PMF (Fin (n + 1) → ℕ)
  | 0 => initial.map (fun state _ => state)
  | n + 1 =>
      (manyServerUnmarkedStatePrefixPMF initial trafficIntensity servers hservers n).bind
        fun stateWindow =>
          (manyServerUniformizedKernel trafficIntensity servers hservers
            (stateWindow (Fin.last n))).map fun successor =>
              snocWindow stateWindow successor

/-- Adjoin the independent current potential-event mark to a finite unmarked
queue-state prefix.  The mark is the one used for the transition out of the
last state of the prefix. -/
def manyServerQueuePrefixCurrentMarkPMF
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (servers : ℕ)
    (hservers : 0 < servers) (n : ℕ) :
    PMF ((Fin (n + 1) → ℕ) × Bool) :=
  (manyServerUnmarkedStatePrefixPMF initial trafficIntensity servers hservers n).bind
    fun stateWindow =>
      (manyServerUniformizationArrivalMark trafficIntensity).map
        fun mark => (stateWindow, mark)

/-- Advancing a queue-prefix/current-mark PMF consumes the current mark,
extends the queue-state prefix, and independently samples the next mark. -/
theorem manyServerQueuePrefixCurrentMarkPMF_succ
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (servers : ℕ)
    (hservers : 0 < servers) (n : ℕ) :
    (manyServerQueuePrefixCurrentMarkPMF initial trafficIntensity servers hservers n).bind
      (fun history =>
        (manyServerMarkedStateUniformizationKernel
          trafficIntensity servers hservers (history.1 (Fin.last n), history.2)).map
          fun next => (snocWindow history.1 next.1, next.2)) =
      manyServerQueuePrefixCurrentMarkPMF initial trafficIntensity servers hservers (Nat.succ n) := by
  unfold manyServerQueuePrefixCurrentMarkPMF
  simp only [manyServerUnmarkedStatePrefixPMF]
  conv_lhs => rw [PMF.bind_bind]
  conv_rhs => rw [PMF.bind_bind]
  apply congrArg (fun transition =>
    (manyServerUnmarkedStatePrefixPMF initial trafficIntensity servers hservers n).bind transition)
  funext stateWindow
  rw [PMF.bind_map]
  unfold manyServerMarkedStateUniformizationKernel
  change
    (manyServerUniformizationArrivalMark trafficIntensity).bind (fun mark =>
      PMF.map (fun next => (snocWindow stateWindow next.1, next.2))
        ((manyServerUniformizedStateUpdate servers hservers
          (stateWindow (Fin.last n)) mark).bind fun successor =>
            (manyServerUniformizationArrivalMark trafficIntensity).map
              fun nextMark => (successor, nextMark))) =
      (PMF.map (fun successor => snocWindow stateWindow successor)
        (manyServerUniformizedKernel trafficIntensity servers hservers
          (stateWindow (Fin.last n)))).bind fun stateWindow =>
            (manyServerUniformizationArrivalMark trafficIntensity).map
              fun mark => (stateWindow, mark)
  simp_rw [PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def]
  rw [manyServerUniformizedKernel_eq_arrivalMark_bind]
  rw [PMF.map_bind]
  conv_rhs => rw [PMF.bind_bind]
  simp_rw [PMF.bind_map]
  simp only [Function.comp_def]

/-- The literal PMF recursion for finite unmarked prefixes agrees with the
measure-valued Ionescu--Tulcea one-step extension. -/
theorem manyServerUnmarkedStatePrefixPMF_toMeasure_succ
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (servers : ℕ)
    (hservers : 0 < servers) (n : ℕ) :
    (manyServerUnmarkedStatePrefixPMF initial trafficIntensity servers hservers
      (Nat.succ n)).toMeasure =
      Measure.map (fun value : (Fin (n + 1) → ℕ) × ℕ =>
        snocWindow value.1 value.2)
        ((manyServerUnmarkedStatePrefixPMF initial trafficIntensity servers hservers n).toMeasure ⊗ₘ
          (countablePMFKernel
            (manyServerUniformizedKernel trafficIntensity servers hservers) ∘ₖ
              Kernel.deterministic
                (fun stateWindow : Fin (n + 1) → ℕ => stateWindow (Fin.last n))
                (measurable_pi_apply _))) := by
  let prefixKernel : (Fin (n + 1) → ℕ) → PMF ℕ :=
    fun stateWindow => manyServerUniformizedKernel trafficIntensity servers hservers
      (stateWindow (Fin.last n))
  have hkernel : countablePMFKernelTo prefixKernel =
      countablePMFKernel
        (manyServerUniformizedKernel trafficIntensity servers hservers) ∘ₖ
          Kernel.deterministic
            (fun stateWindow : Fin (n + 1) → ℕ => stateWindow (Fin.last n))
            (measurable_pi_apply _) := by
    rw [Kernel.comp_deterministic_eq_comap]
    rfl
  have hpair :
      (initialTransitionPairPMFTo
        (manyServerUnmarkedStatePrefixPMF initial trafficIntensity servers hservers n)
        prefixKernel).map (fun value : (Fin (n + 1) → ℕ) × ℕ =>
          snocWindow value.1 value.2) =
        manyServerUnmarkedStatePrefixPMF initial trafficIntensity servers hservers
          (Nat.succ n) := by
    unfold initialTransitionPairPMFTo
    rw [PMF.map_bind]
    simp only [PMF.map_comp, Function.comp_def]
    rfl
  rw [← hpair]
  rw [← PMF.toMeasure_map (fun value : (Fin (n + 1) → ℕ) × ℕ =>
      snocWindow value.1 value.2)
    (initialTransitionPairPMFTo
      (manyServerUnmarkedStatePrefixPMF initial trafficIntensity servers hservers n)
      prefixKernel)
    (measurable_of_countable _)]
  rw [initialTransitionPairPMFTo_toMeasure_eq_compProd]
  rw [hkernel]

/-- Every finite prefix of the arbitrary-initial-law unmarked many-server
embedded trajectory has the literal recursively generated prefix PMF law. -/
theorem manyServerUniformizedEmbeddedTrajectory_natPrefix_hasLaw
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (servers : ℕ)
    (hservers : 0 < servers) (n : ℕ) :
    HasLaw (natPrefix n)
      (manyServerUnmarkedStatePrefixPMF initial trafficIntensity servers hservers n).toMeasure
      (manyServerUniformizedEmbeddedTrajectoryMeasure
        initial.toMeasure trafficIntensity servers hservers) := by
  let trajectory : Measure (ℕ → ℕ) :=
    manyServerUniformizedEmbeddedTrajectoryMeasure
      initial.toMeasure trafficIntensity servers hservers
  let kernel : Kernel ℕ ℕ :=
    countablePMFKernel (manyServerUniformizedKernel trafficIntensity servers hservers)
  letI : IsProbabilityMeasure initial.toMeasure := by infer_instance
  letI : IsMarkovKernel kernel := by
    dsimp [kernel]
    infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory, manyServerUniformizedEmbeddedTrajectoryMeasure]
    unfold stationaryTrajMeasure
    infer_instance
  induction n with
  | zero =>
      have hsingleton : Measurable (fun state : ℕ => fun _ : Fin 1 => state) :=
        measurable_of_countable _
      refine ⟨(measurable_natPrefix 0).aemeasurable, ?_⟩
      change Measure.map (natPrefix 0) trajectory =
        (initial.map (fun state _ => state)).toMeasure
      rw [← PMF.toMeasure_map (fun state : ℕ => fun _ : Fin 1 => state) initial
        (measurable_of_countable _)]
      calc
        Measure.map (natPrefix 0) trajectory =
            Measure.map (fun state : ℕ => fun _ : Fin 1 => state)
              (Measure.map (fun path : ℕ → ℕ => path 0) trajectory) := by
                symm
                rw [Measure.map_map hsingleton
                  (measurable_pi_apply 0)]
                congr 1
                funext path
                funext index
                fin_cases index
                rfl
        _ = Measure.map (fun state : ℕ => fun _ : Fin 1 => state) initial.toMeasure := by
              rw [show Measure.map (fun path : ℕ → ℕ => path 0) trajectory =
                initial.toMeasure by
                  exact manyServerUniformizedEmbeddedTrajectoryMeasure_zero_marginal
                    trafficIntensity servers hservers]
  | succ n ih =>
      refine ⟨(measurable_natPrefix (Nat.succ n)).aemeasurable, ?_⟩
      change Measure.map (natPrefix (Nat.succ n)) trajectory =
        (manyServerUnmarkedStatePrefixPMF initial trafficIntensity servers hservers
          (Nat.succ n)).toMeasure
      calc
        Measure.map (natPrefix (Nat.succ n)) trajectory =
            Measure.map (fun value : (Fin (n + 1) → ℕ) × ℕ =>
              snocWindow value.1 value.2)
              ((Measure.map (natPrefix n) trajectory) ⊗ₘ
                (kernel ∘ₖ Kernel.deterministic
                  (fun stateWindow : Fin (n + 1) → ℕ => stateWindow (Fin.last n))
                  (measurable_pi_apply _))) := by
                    simpa [trajectory, kernel] using
                      (stationaryTrajMeasure_natPrefix_succ
                        (π := initial.toMeasure)
                        (K := countablePMFKernel
                          (manyServerUniformizedKernel trafficIntensity servers hservers)) n)
        _ = Measure.map (fun value : (Fin (n + 1) → ℕ) × ℕ =>
              snocWindow value.1 value.2)
              ((manyServerUnmarkedStatePrefixPMF initial trafficIntensity servers hservers n).toMeasure ⊗ₘ
                (kernel ∘ₖ Kernel.deterministic
                  (fun stateWindow : Fin (n + 1) → ℕ => stateWindow (Fin.last n))
                  (measurable_pi_apply _))) := by
                    rw [ih.map_eq]
        _ = (manyServerUnmarkedStatePrefixPMF initial trafficIntensity servers hservers
              (Nat.succ n)).toMeasure := by
                symm
                exact manyServerUnmarkedStatePrefixPMF_toMeasure_succ
                  initial trafficIntensity servers hservers n

/-- Forget the marks in a finite augmented queue-state prefix while retaining
the final, as-yet-unused mark that governs the next embedded transition. -/
def manyServerMarkedStateQueuePrefixCurrentMark (n : ℕ)
    (window : Fin (n + 1) → ℕ × Bool) : (Fin (n + 1) → ℕ) × Bool :=
  (fun index => (window index).1, (window (Fin.last n)).2)

theorem measurable_manyServerMarkedStateQueuePrefixCurrentMark (n : ℕ) :
    Measurable (manyServerMarkedStateQueuePrefixCurrentMark n) :=
  measurable_of_countable _

/-- The zero-prefix/current-mark PMF is precisely the marked initial PMF with
its queue coordinate repackaged as a singleton prefix. -/
theorem manyServerQueuePrefixCurrentMarkPMF_zero_eq_markedStatePMF_map
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (servers : ℕ)
    (hservers : 0 < servers) :
    (manyServerMarkedStatePMF initial trafficIntensity).map
      (fun stateAndMark : ℕ × Bool =>
        (fun _ : Fin 1 => stateAndMark.1, stateAndMark.2)) =
      manyServerQueuePrefixCurrentMarkPMF initial trafficIntensity servers hservers 0 := by
  unfold manyServerMarkedStatePMF manyServerQueuePrefixCurrentMarkPMF
    manyServerUnmarkedStatePrefixPMF
  rw [PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def]
  rw [PMF.bind_map]
  rfl

/-- The measure-valued one-step extension of a queue-prefix/current-mark PMF
has exactly the recursively defined next prefix/current-mark PMF law. -/
theorem manyServerQueuePrefixCurrentMarkPMF_toMeasure_succ
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (servers : ℕ)
    (hservers : 0 < servers) (n : ℕ) :
    (manyServerQueuePrefixCurrentMarkPMF initial trafficIntensity servers hservers
      (Nat.succ n)).toMeasure =
      Measure.map (fun value : ((Fin (n + 1) → ℕ) × Bool) × (ℕ × Bool) =>
        (snocWindow value.1.1 value.2.1, value.2.2))
        ((manyServerQueuePrefixCurrentMarkPMF initial trafficIntensity servers hservers n).toMeasure ⊗ₘ
          (manyServerMarkedStateUniformizationMeasureKernel
            trafficIntensity servers hservers ∘ₖ
              Kernel.deterministic
                (fun history : (Fin (n + 1) → ℕ) × Bool =>
                  (history.1 (Fin.last n), history.2))
                (measurable_of_countable _))) := by
  let prefixKernel : ((Fin (n + 1) → ℕ) × Bool) → PMF (ℕ × Bool) :=
    fun history => manyServerMarkedStateUniformizationKernel
      trafficIntensity servers hservers (history.1 (Fin.last n), history.2)
  let output : ((Fin (n + 1) → ℕ) × Bool) × (ℕ × Bool) →
      (Fin (n + 2) → ℕ) × Bool :=
    fun value => (snocWindow value.1.1 value.2.1, value.2.2)
  have hkernel : countablePMFKernelTo prefixKernel =
      manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers ∘ₖ
          Kernel.deterministic
            (fun history : (Fin (n + 1) → ℕ) × Bool =>
              (history.1 (Fin.last n), history.2))
            (measurable_of_countable _) := by
    rw [Kernel.comp_deterministic_eq_comap]
    rfl
  have hpair :
      (initialTransitionPairPMFTo
        (manyServerQueuePrefixCurrentMarkPMF initial trafficIntensity servers hservers n)
        prefixKernel).map output =
        manyServerQueuePrefixCurrentMarkPMF initial trafficIntensity servers hservers
          (Nat.succ n) := by
    unfold initialTransitionPairPMFTo output prefixKernel
    rw [PMF.map_bind]
    simp only [PMF.map_comp, Function.comp_def]
    exact manyServerQueuePrefixCurrentMarkPMF_succ
      initial trafficIntensity servers hservers n
  rw [← hpair]
  rw [← PMF.toMeasure_map output
    (initialTransitionPairPMFTo
      (manyServerQueuePrefixCurrentMarkPMF initial trafficIntensity servers hservers n)
      prefixKernel)
    (measurable_of_countable _)]
  rw [initialTransitionPairPMFTo_toMeasure_eq_compProd]
  rw [hkernel]

/-- Repacking an augmented state prefix as its queue-state prefix plus current
mark commutes with one Ionescu--Tulcea extension. -/
theorem manyServerMarkedStateQueuePrefixCurrentMark_transition
    (ν : Measure (Fin (n + 1) → ℕ × Bool)) [IsProbabilityMeasure ν]
    (trafficIntensity : ℝ≥0) (servers : ℕ) (hservers : 0 < servers) :
    Measure.map (manyServerMarkedStateQueuePrefixCurrentMark (Nat.succ n))
      (Measure.map (fun value : (Fin (n + 1) → ℕ × Bool) × (ℕ × Bool) =>
        snocWindow value.1 value.2)
        (ν ⊗ₘ (manyServerMarkedStateUniformizationMeasureKernel
          trafficIntensity servers hservers ∘ₖ
            Kernel.deterministic
              (fun window : Fin (n + 1) → ℕ × Bool => window (Fin.last n))
              (measurable_pi_apply _)))) =
      Measure.map (fun value : ((Fin (n + 1) → ℕ) × Bool) × (ℕ × Bool) =>
        (snocWindow value.1.1 value.2.1, value.2.2))
        ((Measure.map (manyServerMarkedStateQueuePrefixCurrentMark n) ν) ⊗ₘ
          (manyServerMarkedStateUniformizationMeasureKernel
            trafficIntensity servers hservers ∘ₖ
              Kernel.deterministic
                (fun history : (Fin (n + 1) → ℕ) × Bool =>
                  (history.1 (Fin.last n), history.2))
                (measurable_of_countable _))) := by
  let markedKernel : Kernel (ℕ × Bool) (ℕ × Bool) :=
    manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers
  let repack : (Fin (n + 1) → ℕ × Bool) → (Fin (n + 1) → ℕ) × Bool :=
    manyServerMarkedStateQueuePrefixCurrentMark n
  let readRepacked : ((Fin (n + 1) → ℕ) × Bool) → ℕ × Bool :=
    fun history => (history.1 (Fin.last n), history.2)
  let readMarked : (Fin (n + 1) → ℕ × Bool) → ℕ × Bool :=
    fun window => window (Fin.last n)
  let snocMarked : (Fin (n + 1) → ℕ × Bool) × (ℕ × Bool) →
      Fin (n + 2) → ℕ × Bool :=
    fun value => snocWindow value.1 value.2
  let output : ((Fin (n + 1) → ℕ) × Bool) × (ℕ × Bool) →
      (Fin (n + 2) → ℕ) × Bool :=
    fun value => (snocWindow value.1.1 value.2.1, value.2.2)
  have hrepack : Measurable repack :=
    measurable_manyServerMarkedStateQueuePrefixCurrentMark n
  have hreadRepacked : Measurable readRepacked := measurable_of_countable _
  have hreadMarked : Measurable readMarked := measurable_pi_apply _
  have hsnocMarked : Measurable snocMarked := measurable_snocWindow (n + 1)
  have houtput : Measurable output := measurable_of_countable _
  have hframe : Measurable (fun value :
      (Fin (n + 1) → ℕ × Bool) × (ℕ × Bool) => (repack value.1, value.2)) :=
    hrepack.comp measurable_fst |>.prodMk measurable_snd
  have hread : readMarked = readRepacked ∘ repack := by
    funext window
    rfl
  have hthrough :
      Measure.map (fun value :
        (Fin (n + 1) → ℕ × Bool) × (ℕ × Bool) => (repack value.1, value.2))
        (ν ⊗ₘ (markedKernel ∘ₖ
          Kernel.deterministic (readRepacked ∘ repack)
            (hreadRepacked.comp hrepack))) =
        (Measure.map repack ν) ⊗ₘ
          (markedKernel ∘ₖ Kernel.deterministic readRepacked hreadRepacked) := by
    exact Measure.compProd_map_through ν markedKernel repack hrepack
      readRepacked hreadRepacked
  calc
    Measure.map (manyServerMarkedStateQueuePrefixCurrentMark (Nat.succ n))
        (Measure.map snocMarked
          (ν ⊗ₘ (markedKernel ∘ₖ
            Kernel.deterministic readMarked hreadMarked))) =
        Measure.map (fun value :
          (Fin (n + 1) → ℕ × Bool) × (ℕ × Bool) =>
            output (repack value.1, value.2))
          (ν ⊗ₘ (markedKernel ∘ₖ
            Kernel.deterministic (readRepacked ∘ repack)
              (hreadRepacked.comp hrepack))) := by
            rw [Measure.map_map
              (measurable_manyServerMarkedStateQueuePrefixCurrentMark (Nat.succ n))
              hsnocMarked]
            congr 1
            funext value
            apply Prod.ext
            · funext index
              refine Fin.lastCases ?_ (fun previous => ?_) index
              · simp [repack, manyServerMarkedStateQueuePrefixCurrentMark, snocMarked,
                  output, snocWindow]
              · simp [repack, manyServerMarkedStateQueuePrefixCurrentMark, snocMarked,
                  output, snocWindow]
            · simp [manyServerMarkedStateQueuePrefixCurrentMark, snocMarked,
                output, snocWindow]
    _ = Measure.map output
          (Measure.map (fun value :
            (Fin (n + 1) → ℕ × Bool) × (ℕ × Bool) =>
              (repack value.1, value.2))
            (ν ⊗ₘ (markedKernel ∘ₖ
              Kernel.deterministic (readRepacked ∘ repack)
                (hreadRepacked.comp hrepack)))) := by
            symm
            rw [Measure.map_map houtput hframe]
            rfl
    _ = Measure.map output
          ((Measure.map repack ν) ⊗ₘ
            (markedKernel ∘ₖ Kernel.deterministic readRepacked hreadRepacked)) := by
            rw [hthrough]
    _ = _ := by
      rfl

/-- Every finite marked many-server trajectory prefix, after forgetting its
past marks and retaining its current mark, has the corresponding queue-prefix
and independent-current-mark PMF law. -/
theorem manyServerMarkedStateTrajectory_queuePrefixCurrentMark_hasLaw
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (servers : ℕ)
    (hservers : 0 < servers) (n : ℕ) :
    HasLaw (fun path : ℕ → ℕ × Bool =>
      manyServerMarkedStateQueuePrefixCurrentMark n (natPrefix n path))
      (manyServerQueuePrefixCurrentMarkPMF
        initial trafficIntensity servers hservers n).toMeasure
      (stationaryTrajMeasure
        (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
        (manyServerMarkedStateUniformizationMeasureKernel
          trafficIntensity servers hservers)) := by
  let markedInitial : Measure (ℕ × Bool) :=
    (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
  let markedKernel : Kernel (ℕ × Bool) (ℕ × Bool) :=
    manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers
  let trajectory : Measure (ℕ → ℕ × Bool) :=
    stationaryTrajMeasure markedInitial markedKernel
  letI : IsProbabilityMeasure initial.toMeasure := by infer_instance
  letI : IsProbabilityMeasure markedInitial := by
    dsimp [markedInitial]
    infer_instance
  letI : IsMarkovKernel markedKernel := by
    dsimp [markedKernel]
    infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  induction n with
  | zero =>
      let base : (ℕ × Bool) → (Fin 1 → ℕ) × Bool :=
        fun stateAndMark => (fun _ => stateAndMark.1, stateAndMark.2)
      have hbase : Measurable base := measurable_of_countable _
      refine ⟨(measurable_manyServerMarkedStateQueuePrefixCurrentMark 0 |>.comp
        (measurable_natPrefix 0)).aemeasurable, ?_⟩
      change Measure.map (fun path : ℕ → ℕ × Bool =>
        manyServerMarkedStateQueuePrefixCurrentMark 0 (natPrefix 0 path)) trajectory =
        (manyServerQueuePrefixCurrentMarkPMF
          initial trafficIntensity servers hservers 0).toMeasure
      calc
        Measure.map (fun path : ℕ → ℕ × Bool =>
          manyServerMarkedStateQueuePrefixCurrentMark 0 (natPrefix 0 path)) trajectory =
            Measure.map base
              (Measure.map (fun path : ℕ → ℕ × Bool => path 0) trajectory) := by
                symm
                rw [Measure.map_map hbase (measurable_pi_apply 0)]
                congr 1
                funext path
                apply Prod.ext
                · funext index
                  fin_cases index
                  rfl
                · rfl
        _ = Measure.map base markedInitial := by
              rw [show Measure.map (fun path : ℕ → ℕ × Bool => path 0) trajectory =
                markedInitial by
                  exact stationaryTrajMeasure_zero_marginal]
        _ = ((manyServerMarkedStatePMF initial trafficIntensity).map base).toMeasure := by
              rw [PMF.toMeasure_map base
                (manyServerMarkedStatePMF initial trafficIntensity) hbase]
        _ = (manyServerQueuePrefixCurrentMarkPMF
              initial trafficIntensity servers hservers 0).toMeasure := by
              rw [manyServerQueuePrefixCurrentMarkPMF_zero_eq_markedStatePMF_map]
  | succ n ih =>
      letI : IsProbabilityMeasure (Measure.map (natPrefix n) trajectory) :=
        Measure.isProbabilityMeasure_map (measurable_natPrefix n).aemeasurable
      let repack : (Fin (n + 1) → ℕ × Bool) → (Fin (n + 1) → ℕ) × Bool :=
        manyServerMarkedStateQueuePrefixCurrentMark n
      let output : ((Fin (n + 1) → ℕ) × Bool) × (ℕ × Bool) →
          (Fin (n + 2) → ℕ) × Bool :=
        fun value => (snocWindow value.1.1 value.2.1, value.2.2)
      have hcurrent : Measure.map repack
          (Measure.map (natPrefix n) trajectory) =
          (manyServerQueuePrefixCurrentMarkPMF
            initial trafficIntensity servers hservers n).toMeasure := by
        calc
          Measure.map repack (Measure.map (natPrefix n) trajectory) =
              Measure.map (fun path : ℕ → ℕ × Bool =>
                manyServerMarkedStateQueuePrefixCurrentMark n (natPrefix n path)) trajectory := by
                  rw [Measure.map_map
                    (measurable_manyServerMarkedStateQueuePrefixCurrentMark n)
                    (measurable_natPrefix n)]
                  rfl
          _ = _ := ih.map_eq
      refine ⟨(measurable_manyServerMarkedStateQueuePrefixCurrentMark (Nat.succ n) |>.comp
        (measurable_natPrefix (Nat.succ n))).aemeasurable, ?_⟩
      change Measure.map (fun path : ℕ → ℕ × Bool =>
        manyServerMarkedStateQueuePrefixCurrentMark (Nat.succ n)
          (natPrefix (Nat.succ n) path)) trajectory =
        (manyServerQueuePrefixCurrentMarkPMF
          initial trafficIntensity servers hservers (Nat.succ n)).toMeasure
      calc
        Measure.map (fun path : ℕ → ℕ × Bool =>
          manyServerMarkedStateQueuePrefixCurrentMark (Nat.succ n)
            (natPrefix (Nat.succ n) path)) trajectory =
            Measure.map (manyServerMarkedStateQueuePrefixCurrentMark (Nat.succ n))
              (Measure.map (natPrefix (Nat.succ n)) trajectory) := by
                symm
                rw [Measure.map_map
                  (measurable_manyServerMarkedStateQueuePrefixCurrentMark (Nat.succ n))
                  (measurable_natPrefix (Nat.succ n))]
                rfl
        _ = Measure.map (manyServerMarkedStateQueuePrefixCurrentMark (Nat.succ n))
              (Measure.map (fun value :
                (Fin (n + 1) → ℕ × Bool) × (ℕ × Bool) => snocWindow value.1 value.2)
                ((Measure.map (natPrefix n) trajectory) ⊗ₘ
                  (markedKernel ∘ₖ Kernel.deterministic
                    (fun window : Fin (n + 1) → ℕ × Bool => window (Fin.last n))
                    (measurable_pi_apply _)))) := by
                    rw [stationaryTrajMeasure_natPrefix_succ]
        _ = Measure.map output
              ((Measure.map repack (Measure.map (natPrefix n) trajectory)) ⊗ₘ
                (markedKernel ∘ₖ Kernel.deterministic
                  (fun history : (Fin (n + 1) → ℕ) × Bool =>
                    (history.1 (Fin.last n), history.2))
                  (measurable_of_countable _))) := by
                    simpa [repack, output, markedKernel] using
                      (manyServerMarkedStateQueuePrefixCurrentMark_transition
                        (ν := Measure.map (natPrefix n) trajectory)
                        trafficIntensity servers hservers)
        _ = Measure.map output
              ((manyServerQueuePrefixCurrentMarkPMF
                initial trafficIntensity servers hservers n).toMeasure ⊗ₘ
                (markedKernel ∘ₖ Kernel.deterministic
                  (fun history : (Fin (n + 1) → ℕ) × Bool =>
                    (history.1 (Fin.last n), history.2))
                  (measurable_of_countable _))) := by
                    rw [hcurrent]
        _ = (manyServerQueuePrefixCurrentMarkPMF
              initial trafficIntensity servers hservers (Nat.succ n)).toMeasure := by
                symm
                simpa [output, markedKernel] using
                  (manyServerQueuePrefixCurrentMarkPMF_toMeasure_succ
                    initial trafficIntensity servers hservers n)

/-- Forgetting the current mark of a queue-prefix/current-mark PMF recovers
exactly its unmarked queue-state prefix PMF. -/
theorem manyServerQueuePrefixCurrentMarkPMF_map_fst
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (servers : ℕ)
    (hservers : 0 < servers) (n : ℕ) :
    (manyServerQueuePrefixCurrentMarkPMF
      initial trafficIntensity servers hservers n).map Prod.fst =
      manyServerUnmarkedStatePrefixPMF initial trafficIntensity servers hservers n := by
  unfold manyServerQueuePrefixCurrentMarkPMF
  rw [PMF.map_bind]
  calc
    (manyServerUnmarkedStatePrefixPMF initial trafficIntensity servers hservers n).bind
        (fun stateWindow =>
          PMF.map Prod.fst
            (PMF.map (fun mark => (stateWindow, mark))
              (manyServerUniformizationArrivalMark trafficIntensity))) =
        (manyServerUnmarkedStatePrefixPMF initial trafficIntensity servers hservers n).bind
          PMF.pure := by
            apply congrArg (fun transition =>
              (manyServerUnmarkedStatePrefixPMF initial trafficIntensity servers hservers n).bind
                transition)
            funext stateWindow
            rw [PMF.map_comp]
            change (manyServerUniformizationArrivalMark trafficIntensity).map
                (Function.const Bool stateWindow) = PMF.pure stateWindow
            exact PMF.map_const _ stateWindow
    _ = manyServerUnmarkedStatePrefixPMF initial trafficIntensity servers hservers n :=
      PMF.bind_pure _

/-- The queue-state prefix obtained by forgetting every mark from a marked
trajectory has the exact recursively generated unmarked prefix law. -/
theorem manyServerMarkedStateTrajectory_queuePrefix_hasLaw
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (servers : ℕ)
    (hservers : 0 < servers) (n : ℕ) :
    HasLaw (fun path : ℕ → ℕ × Bool =>
      fun index : Fin (n + 1) => (path index).1)
      (manyServerUnmarkedStatePrefixPMF
        initial trafficIntensity servers hservers n).toMeasure
      (stationaryTrajMeasure
        (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
        (manyServerMarkedStateUniformizationMeasureKernel
          trafficIntensity servers hservers)) := by
  have hcurrent := manyServerMarkedStateTrajectory_queuePrefixCurrentMark_hasLaw
    initial trafficIntensity servers hservers n
  have hprojection : HasLaw Prod.fst
      (manyServerUnmarkedStatePrefixPMF
        initial trafficIntensity servers hservers n).toMeasure
      (manyServerQueuePrefixCurrentMarkPMF
        initial trafficIntensity servers hservers n).toMeasure := by
    refine ⟨measurable_fst.aemeasurable, ?_⟩
    rw [PMF.toMeasure_map Prod.fst
      (manyServerQueuePrefixCurrentMarkPMF
        initial trafficIntensity servers hservers n)
      (measurable_of_countable _),
      manyServerQueuePrefixCurrentMarkPMF_map_fst]
  simpa [Function.comp_def] using hprojection.comp hcurrent

/-- Forgetting the Boolean marks from the complete marked many-server
trajectory gives exactly the ordinary unmarked embedded trajectory law. -/
theorem manyServerMarkedStateTrajectory_queuePath_map_eq_unmarked
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (servers : ℕ)
    (hservers : 0 < servers) :
    Measure.map (fun path : ℕ → ℕ × Bool => fun index => (path index).1)
      (stationaryTrajMeasure
        (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
        (manyServerMarkedStateUniformizationMeasureKernel
          trafficIntensity servers hservers)) =
      manyServerUniformizedEmbeddedTrajectoryMeasure
        initial.toMeasure trafficIntensity servers hservers := by
  let markedTrajectory : Measure (ℕ → ℕ × Bool) :=
    stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
  let unmarkedTrajectory : Measure (ℕ → ℕ) :=
    manyServerUniformizedEmbeddedTrajectoryMeasure
      initial.toMeasure trafficIntensity servers hservers
  let queuePath : (ℕ → ℕ × Bool) → ℕ → ℕ :=
    fun path index => (path index).1
  have hqueuePath : Measurable queuePath := by
    apply measurable_pi_lambda
    intro index
    exact measurable_fst.comp (measurable_pi_apply index)
  letI : IsProbabilityMeasure markedTrajectory := by
    dsimp [markedTrajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsProbabilityMeasure (Measure.map queuePath markedTrajectory) :=
    Measure.isProbabilityMeasure_map hqueuePath.aemeasurable
  letI : IsProbabilityMeasure unmarkedTrajectory := by
    dsimp [unmarkedTrajectory, manyServerUniformizedEmbeddedTrajectoryMeasure]
    unfold stationaryTrajMeasure
    infer_instance
  change Measure.map queuePath markedTrajectory = unmarkedTrajectory
  refine nat_measure_eq_of_all_prefix ?_
  intro n
  have hmarked := manyServerMarkedStateTrajectory_queuePrefix_hasLaw
    initial trafficIntensity servers hservers n
  have hunmarked := manyServerUniformizedEmbeddedTrajectory_natPrefix_hasLaw
    initial trafficIntensity servers hservers n
  calc
    Measure.map (natPrefix n) (Measure.map queuePath markedTrajectory) =
        Measure.map (fun path : ℕ → ℕ × Bool =>
          fun index : Fin (n + 1) => (path index).1)
          markedTrajectory := by
            rw [Measure.map_map (measurable_natPrefix n) hqueuePath]
            rfl
    _ = (manyServerUnmarkedStatePrefixPMF
          initial trafficIntensity servers hservers n).toMeasure := by
            simpa [markedTrajectory] using hmarked.map_eq
    _ = Measure.map (natPrefix n) unmarkedTrajectory := by
            symm
            simpa [unmarkedTrajectory] using hunmarked.map_eq

end

end AppliedModelingLib.Probability.Queueing
