import AppliedModelingLib.Queueing.ManyServerMarkedStatePrefix
import AppliedModelingLib.Queueing.ManyServerCanonicalTrajectory
import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalOccupation
import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalRenewalCountMarginal
import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalRenewalCountMGF
import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalIncrementBoundary
import AppliedModelingLib.Foundations.Probability.IidStatePrefixStopping
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic

/-!
# Canonical-clock finite marked laws for many-server uniformization

This module combines the marked embedded trajectory from an arbitrary initial
law with the independent canonical exponential clock.  It proves the
fixed-horizon joint law of the initial state, the all-event clock count, and
every deterministic finite prefix of actual event marks.  Random-horizon
thinning and any functional limit remain separate steps.
-/

namespace AppliedModelingLib.Probability.Queueing

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

/-- At one physical horizon, retain the initial queue state, the canonical
all-event clock count, and a deterministic prefix of the actual event marks. -/
def manyServerMarkedCanonicalClockPrefix (time : ℝ) (n : ℕ) :
    ((ℕ → ℕ × Bool) × (ℕ → ℝ)) → (ℕ × ℕ) × (Fin (n + 1) → Bool) :=
  fun value =>
    (((value.1 0).1, PoissonProcess.canonicalRenewalCount time value.2),
      fun i => (value.1 i).2)

theorem measurable_manyServerMarkedCanonicalClockPrefix (time : ℝ) (n : ℕ) :
    Measurable (manyServerMarkedCanonicalClockPrefix time n) := by
  unfold manyServerMarkedCanonicalClockPrefix
  apply ((measurable_fst.comp ((measurable_pi_apply 0).comp measurable_fst)).prodMk
    ((PoissonProcess.measurable_canonicalRenewalCount time).comp measurable_snd)).prodMk
  apply measurable_pi_lambda
  intro i
  exact measurable_snd.comp ((measurable_pi_apply (i : ℕ)).comp measurable_fst)

/-- The queue-length coordinate at time zero in the canonical marked
construction. -/
def manyServerMarkedCanonicalInitialQueue :
    ((ℕ → ℕ × Bool) × (ℕ → ℝ)) → ℕ :=
  fun value => (value.1 0).1

/-- The time-zero queue coordinate is measurable. -/
theorem measurable_manyServerMarkedCanonicalInitialQueue :
    Measurable manyServerMarkedCanonicalInitialQueue := by
  exact measurable_fst.comp ((measurable_pi_apply 0).comp measurable_fst)

/-- The time-zero queue coordinate of the canonical marked construction has
the specified initial queue law. -/
theorem map_manyServerMarkedCanonicalInitialQueue
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (serviceRate : ℝ) (servers : ℕ)
    (hservers : 0 < servers) (hserviceRate : 0 < serviceRate) :
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    let trajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    let gaps := PoissonProcess.exponentialInterarrivalMeasure rate
    Measure.map manyServerMarkedCanonicalInitialQueue (trajectory.prod gaps) = initial.toMeasure := by
  dsimp only
  let rate : ℝ := manyServerUniformizationRate
    (trafficIntensity : ℝ) serviceRate servers
  let markedInitial : PMF (ℕ × Bool) := manyServerMarkedStatePMF initial trafficIntensity
  let trajectory : Measure (ℕ → ℕ × Bool) := stationaryTrajMeasure
    markedInitial.toMeasure
    (manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers)
  let gaps : Measure (ℕ → ℝ) := PoissonProcess.exponentialInterarrivalMeasure rate
  let source : Measure ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := trajectory.prod gaps
  let markedAtZero : (ℕ → ℕ × Bool) → ℕ × Bool := fun path => path 0
  have hrate : 0 < rate :=
    manyServerUniformizationRate_pos trafficIntensity serviceRate servers hservers hserviceRate
  letI : IsProbabilityMeasure markedInitial.toMeasure := by
    dsimp [markedInitial]
    infer_instance
  letI : IsMarkovKernel
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers) := by
    infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsProbabilityMeasure gaps := by
    dsimp [gaps]
    exact PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  have hfst : Measure.map Prod.fst source = trajectory := by
    dsimp [source]
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  have hzero : Measure.map markedAtZero trajectory = markedInitial.toMeasure := by
    dsimp [trajectory, markedAtZero]
    exact stationaryTrajMeasure_zero_marginal
  have hqueue : Measure.map Prod.fst markedInitial.toMeasure = initial.toMeasure := by
    calc
      Measure.map Prod.fst markedInitial.toMeasure = (markedInitial.map Prod.fst).toMeasure := by
        exact PMF.toMeasure_map Prod.fst markedInitial (measurable_of_countable _)
      _ = initial.toMeasure := by
        dsimp [markedInitial]
        rw [manyServerMarkedStatePMF_map_fst]
  change Measure.map (Prod.fst ∘ markedAtZero ∘ Prod.fst) source = initial.toMeasure
  calc
    Measure.map (Prod.fst ∘ markedAtZero ∘ Prod.fst) source =
        Measure.map Prod.fst (Measure.map markedAtZero (Measure.map Prod.fst source)) := by
          symm
          rw [Measure.map_map measurable_fst (measurable_pi_apply 0),
            Measure.map_map (measurable_fst.comp (measurable_pi_apply 0)) measurable_fst]
          congr 1
    _ = Measure.map Prod.fst (Measure.map markedAtZero trajectory) := by rw [hfst]
    _ = Measure.map Prod.fst markedInitial.toMeasure := by rw [hzero]
    _ = initial.toMeasure := hqueue

/-- Every event determined by the initial queue coordinate has its specified
initial-law probability under the canonical marked construction. -/
theorem measure_manyServerMarkedCanonicalInitialQueue_preimage
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (serviceRate : ℝ) (servers : ℕ)
    (hservers : 0 < servers) (hserviceRate : 0 < serviceRate) (event : Set ℕ) :
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    let trajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    let gaps := PoissonProcess.exponentialInterarrivalMeasure rate
    (trajectory.prod gaps) (manyServerMarkedCanonicalInitialQueue ⁻¹' event) =
      initial.toMeasure event := by
  dsimp only
  rw [← Measure.map_apply measurable_manyServerMarkedCanonicalInitialQueue
    MeasurableSet.of_discrete]
  exact congrArg (fun measure : Measure ℕ => measure event)
    (map_manyServerMarkedCanonicalInitialQueue
      initial trafficIntensity serviceRate servers hservers hserviceRate)

/-- Reorder a state/mark-prefix/clock-count triple into state/count/mark-prefix
order without changing the corresponding product law. -/
private theorem manyServer_stateMarkPrefix_count_reorder
    (stateLaw : Measure ℕ) (markLaw : Measure (Fin (n + 1) → Bool))
    (countLaw : Measure ℕ)
    [IsProbabilityMeasure stateLaw] [IsProbabilityMeasure markLaw]
    [IsProbabilityMeasure countLaw] :
    Measure.map
      (fun value : (ℕ × (Fin (n + 1) → Bool)) × ℕ =>
        ((value.1.1, value.2), value.1.2))
      ((stateLaw.prod markLaw).prod countLaw) =
      (stateLaw.prod countLaw).prod markLaw := by
  let associate : (ℕ × (Fin (n + 1) → Bool)) × ℕ →
      ℕ × ((Fin (n + 1) → Bool) × ℕ) :=
    MeasurableEquiv.prodAssoc
  let swapTail : ℕ × ((Fin (n + 1) → Bool) × ℕ) →
      ℕ × (ℕ × (Fin (n + 1) → Bool)) :=
    Prod.map id Prod.swap
  let unassociate : ℕ × (ℕ × (Fin (n + 1) → Bool)) →
      (ℕ × ℕ) × (Fin (n + 1) → Bool) :=
    MeasurableEquiv.prodAssoc.symm
  let reorder : (ℕ × (Fin (n + 1) → Bool)) × ℕ →
      (ℕ × ℕ) × (Fin (n + 1) → Bool) :=
    unassociate ∘ swapTail ∘ associate
  have hassociateMeas : Measurable associate := MeasurableEquiv.prodAssoc.measurable
  have hswapTail : Measurable swapTail := measurable_id.prodMap measurable_swap
  have hunassociate : Measurable unassociate := MeasurableEquiv.prodAssoc.symm.measurable
  have hassociate : Measure.map associate ((stateLaw.prod markLaw).prod countLaw) =
      stateLaw.prod (markLaw.prod countLaw) := by
    simpa [associate] using (measurePreserving_prodAssoc stateLaw markLaw countLaw).map_eq
  have hswapTail_map :
      Measure.map swapTail (stateLaw.prod (markLaw.prod countLaw)) =
        stateLaw.prod (countLaw.prod markLaw) := by
    calc
      Measure.map swapTail (stateLaw.prod (markLaw.prod countLaw)) =
          (Measure.map id stateLaw).prod
            (Measure.map Prod.swap (markLaw.prod countLaw)) := by
              rw [show swapTail = Prod.map id Prod.swap by rfl,
                Measure.map_prod_map stateLaw (markLaw.prod countLaw)
                  measurable_id measurable_swap]
      _ = stateLaw.prod (countLaw.prod markLaw) := by
            rw [Measure.map_id, Measure.prod_swap]
  have hunassociate_map :
      Measure.map unassociate (stateLaw.prod (countLaw.prod markLaw)) =
        (stateLaw.prod countLaw).prod markLaw := by
    simpa [unassociate] using
      (measurePreserving_prodAssoc stateLaw countLaw markLaw).symm.map_eq
  have hreorder :
      (fun value : (ℕ × (Fin (n + 1) → Bool)) × ℕ =>
        ((value.1.1, value.2), value.1.2)) = reorder := by
    funext value
    rfl
  calc
    Measure.map
        (fun value : (ℕ × (Fin (n + 1) → Bool)) × ℕ =>
          ((value.1.1, value.2), value.1.2))
        ((stateLaw.prod markLaw).prod countLaw) =
        Measure.map reorder ((stateLaw.prod markLaw).prod countLaw) := by
              rw [hreorder]
    _ = Measure.map unassociate
          (Measure.map (swapTail ∘ associate)
            ((stateLaw.prod markLaw).prod countLaw)) := by
              exact (Measure.map_map hunassociate
                (hswapTail.comp hassociateMeas)).symm
    _ = Measure.map unassociate
          (Measure.map swapTail
            (Measure.map associate ((stateLaw.prod markLaw).prod countLaw))) := by
              rw [Measure.map_map hswapTail hassociateMeas]
    _ = Measure.map unassociate
          (Measure.map swapTail (stateLaw.prod (markLaw.prod countLaw))) := by
            rw [hassociate]
    _ = Measure.map unassociate (stateLaw.prod (countLaw.prod markLaw)) := by
          rw [hswapTail_map]
    _ = (stateLaw.prod countLaw).prod markLaw := hunassociate_map

/-- At a deterministic physical horizon, the marked many-server construction
has the exact product law of its initial state, independent Poisson all-event
count, and every deterministic iid mark prefix. -/
theorem stationaryManyServerMarkedCanonicalClockPrefix_hasLaw
    {initial : PMF ℕ} (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers : ℕ) (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    {time : ℝ} (htime : 0 ≤ time) (n : ℕ) :
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    let countLaw : Measure ℕ := ProbabilityTheory.poissonMeasure
      (⟨rate * time, mul_nonneg
        (le_of_lt (manyServerUniformizationRate_pos trafficIntensity serviceRate
          servers hservers hserviceRate)) htime⟩ : ℝ≥0)
    HasLaw (manyServerMarkedCanonicalClockPrefix time n)
      ((initial.toMeasure.prod countLaw).prod
        (FiniteHorizonMarkedPoisson.iidMarks
          (uniformizedBirthProbability trafficIntensity)
          (uniformizedBirthProbability_le_one trafficIntensity)
          (n + 1)).toMeasure)
      ((stationaryTrajMeasure
        (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
        (manyServerMarkedStateUniformizationMeasureKernel
          trafficIntensity servers hservers)).prod
        (PoissonProcess.exponentialInterarrivalMeasure rate)) := by
  dsimp only
  let rate : ℝ := manyServerUniformizationRate
    (trafficIntensity : ℝ) serviceRate servers
  let countLaw : Measure ℕ := ProbabilityTheory.poissonMeasure
    (⟨rate * time, mul_nonneg
      (le_of_lt (manyServerUniformizationRate_pos trafficIntensity serviceRate
        servers hservers hserviceRate)) htime⟩ : ℝ≥0)
  let markLaw : Measure (Fin (n + 1) → Bool) :=
    (FiniteHorizonMarkedPoisson.iidMarks
      (uniformizedBirthProbability trafficIntensity)
      (uniformizedBirthProbability_le_one trafficIntensity)
      (n + 1)).toMeasure
  let trajectory : Measure (ℕ → ℕ × Bool) := stationaryTrajMeasure
    (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
    (manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers)
  let gaps : Measure (ℕ → ℝ) :=
    PoissonProcess.exponentialInterarrivalMeasure rate
  let pathPrefix : (ℕ → ℕ × Bool) → ℕ × (Fin (n + 1) → Bool) :=
    fun path => manyServerStateMarkPrefix n (natPrefix n path)
  let count : (ℕ → ℝ) → ℕ := PoissonProcess.canonicalRenewalCount time
  let pair : ((ℕ → ℕ × Bool) × (ℕ → ℝ)) →
      (ℕ × (Fin (n + 1) → Bool)) × ℕ :=
    fun value => (pathPrefix value.1, count value.2)
  let reorder : (ℕ × (Fin (n + 1) → Bool)) × ℕ →
      (ℕ × ℕ) × (Fin (n + 1) → Bool) :=
    fun value => ((value.1.1, value.2), value.1.2)
  have hrate : 0 < rate := by
    exact manyServerUniformizationRate_pos trafficIntensity serviceRate
      servers hservers hserviceRate
  letI : IsProbabilityMeasure initial.toMeasure := by infer_instance
  letI : IsProbabilityMeasure markLaw := by
    dsimp [markLaw]
    infer_instance
  letI : IsProbabilityMeasure (IIDStream.measure markLaw) := by
    dsimp [IIDStream.measure]
    infer_instance
  letI : IsProbabilityMeasure countLaw := by
    dsimp [countLaw]
    infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsProbabilityMeasure gaps :=
    PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  have hpathPrefix : HasLaw pathPrefix (initial.toMeasure.prod markLaw) trajectory := by
    simpa [pathPrefix, markLaw, trajectory] using
      (manyServerMarkedStateTrajectory_state_markPrefix_hasLaw_iidMarks
        (initial := initial) trafficIntensity servers hservers n)
  have hcount : HasLaw count countLaw gaps := by
    simpa [count, countLaw, gaps] using
      (PoissonProcess.canonicalRenewalCount_hasLaw_poisson hrate htime)
  have hpairMeas : Measurable pair :=
    (measurable_manyServerStateMarkPrefix n |>.comp
      (measurable_natPrefix n)).prodMap
      (PoissonProcess.measurable_canonicalRenewalCount time)
  have hreorderMeas : Measurable reorder := measurable_of_countable _
  have hpair : HasLaw pair ((initial.toMeasure.prod markLaw).prod countLaw)
      (trajectory.prod gaps) := by
    refine ⟨hpairMeas.aemeasurable, ?_⟩
    calc
      Measure.map pair (trajectory.prod gaps) =
          (Measure.map pathPrefix trajectory).prod (Measure.map count gaps) := by
            change Measure.map (Prod.map pathPrefix count) (trajectory.prod gaps) = _
            exact (Measure.map_prod_map trajectory gaps
              (measurable_manyServerStateMarkPrefix n |>.comp (measurable_natPrefix n))
              (PoissonProcess.measurable_canonicalRenewalCount time)).symm
      _ = (initial.toMeasure.prod markLaw).prod countLaw := by
            rw [hpathPrefix.map_eq, hcount.map_eq]
  refine ⟨(measurable_manyServerMarkedCanonicalClockPrefix time n).aemeasurable, ?_⟩
  have hcomposition : manyServerMarkedCanonicalClockPrefix time n = reorder ∘ pair := by
    funext value
    rfl
  calc
    Measure.map (manyServerMarkedCanonicalClockPrefix time n) (trajectory.prod gaps) =
        Measure.map (reorder ∘ pair) (trajectory.prod gaps) := by
          rw [hcomposition]
    _ = Measure.map reorder (Measure.map pair (trajectory.prod gaps)) := by
          exact (Measure.map_map hreorderMeas hpairMeas).symm
    _ = Measure.map reorder ((initial.toMeasure.prod markLaw).prod countLaw) := by
          rw [hpair.map_eq]
    _ = (initial.toMeasure.prod countLaw).prod markLaw := by
          exact manyServer_stateMarkPrefix_count_reorder
            initial.toMeasure markLaw countLaw

/-- Forget the initial queue state from a canonical-clock state/count/mark
prefix triple. -/
def manyServerMarkedCanonicalClockMarkPrefix (time : ℝ) (n : ℕ) :
    ((ℕ → ℕ × Bool) × (ℕ → ℝ)) → ℕ × (Fin n → Bool) :=
  fun value =>
    (PoissonProcess.canonicalRenewalCount time value.2,
      fun i => (value.1 i).2)

theorem measurable_manyServerMarkedCanonicalClockMarkPrefix (time : ℝ) (n : ℕ) :
    Measurable (manyServerMarkedCanonicalClockMarkPrefix time n) := by
  unfold manyServerMarkedCanonicalClockMarkPrefix
  apply ((PoissonProcess.measurable_canonicalRenewalCount time).comp measurable_snd).prodMk
  apply measurable_pi_lambda
  intro i
  exact measurable_snd.comp ((measurable_pi_apply (i : ℕ)).comp measurable_fst)

/-- The all-event clock count and every finite actual mark prefix have the
product of their Poisson and iid-mark laws. -/
theorem stationaryManyServerMarkedCanonicalClockMarkPrefix_hasLaw
    {initial : PMF ℕ} (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers : ℕ) (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    {time : ℝ} (htime : 0 ≤ time) (n : ℕ) :
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    let countLaw : Measure ℕ := ProbabilityTheory.poissonMeasure
      (⟨rate * time, mul_nonneg
        (le_of_lt (manyServerUniformizationRate_pos trafficIntensity serviceRate
          servers hservers hserviceRate)) htime⟩ : ℝ≥0)
    HasLaw (manyServerMarkedCanonicalClockMarkPrefix time n)
      (countLaw.prod
        (FiniteHorizonMarkedPoisson.iidMarks
          (uniformizedBirthProbability trafficIntensity)
          (uniformizedBirthProbability_le_one trafficIntensity) n).toMeasure)
      ((stationaryTrajMeasure
        (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
        (manyServerMarkedStateUniformizationMeasureKernel
          trafficIntensity servers hservers)).prod
        (PoissonProcess.exponentialInterarrivalMeasure rate)) := by
  dsimp only
  let rate : ℝ := manyServerUniformizationRate
    (trafficIntensity : ℝ) serviceRate servers
  let countLaw : Measure ℕ := ProbabilityTheory.poissonMeasure
    (⟨rate * time, mul_nonneg
      (le_of_lt (manyServerUniformizationRate_pos trafficIntensity serviceRate
        servers hservers hserviceRate)) htime⟩ : ℝ≥0)
  let markLaw (length : ℕ) : Measure (Fin length → Bool) :=
    (FiniteHorizonMarkedPoisson.iidMarks
      (uniformizedBirthProbability trafficIntensity)
      (uniformizedBirthProbability_le_one trafficIntensity) length).toMeasure
  let trajectory : Measure (ℕ → ℕ × Bool) := stationaryTrajMeasure
    (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
    (manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers)
  let gaps : Measure (ℕ → ℝ) :=
    PoissonProcess.exponentialInterarrivalMeasure rate
  let count : (ℕ → ℝ) → ℕ := PoissonProcess.canonicalRenewalCount time
  have hrate : 0 < rate := by
    exact manyServerUniformizationRate_pos trafficIntensity serviceRate
      servers hservers hserviceRate
  letI : IsProbabilityMeasure initial.toMeasure := by infer_instance
  letI : IsProbabilityMeasure countLaw := by
    dsimp [countLaw]
    infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsProbabilityMeasure gaps :=
    PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  have hcount : HasLaw count countLaw gaps := by
    simpa [count, countLaw, gaps] using
      (PoissonProcess.canonicalRenewalCount_hasLaw_poisson hrate htime)
  cases n with
  | zero =>
      let empty : Fin 0 → Bool := fun i => Fin.elim0 i
      let lift : ℕ → ℕ × (Fin 0 → Bool) := fun value => (value, empty)
      have hmarkLaw : markLaw 0 = Measure.dirac empty := by
        dsimp [markLaw]
        rw [← manyServerIidMarkPrefix_eq_finiteHorizonIidMarks trafficIntensity 0,
          manyServerIidMarkPrefix_zero]
      have hsnd : HasLaw Prod.snd gaps (trajectory.prod gaps) := by
        refine ⟨measurable_snd.aemeasurable, ?_⟩
        rw [Measure.map_snd_prod, measure_univ, one_smul]
      have hcountProduct : HasLaw (fun value : (ℕ → ℕ × Bool) × (ℕ → ℝ) =>
          count value.2) countLaw (trajectory.prod gaps) := hcount.comp hsnd
      have hlift : HasLaw lift (countLaw.prod (Measure.dirac empty)) countLaw := by
        refine ⟨(measurable_id.prodMk (measurable_const : Measurable (fun _ : ℕ => empty))).aemeasurable,
          ?_⟩
        change Measure.map lift countLaw = countLaw.prod (Measure.dirac empty)
        rw [Measure.prod_dirac]
      have hresult := hlift.comp hcountProduct
      change HasLaw (fun value : (ℕ → ℕ × Bool) × (ℕ → ℝ) =>
        (count value.2, fun i : Fin 0 => (value.1 i).2))
        (countLaw.prod (markLaw 0)) (trajectory.prod gaps)
      rw [hmarkLaw]
      have hfunction :
          (fun value : (ℕ → ℕ × Bool) × (ℕ → ℝ) =>
            (count value.2, fun i : Fin 0 => (value.1 i).2)) =
            lift ∘ fun value : (ℕ → ℕ × Bool) × (ℕ → ℝ) => count value.2 := by
        funext value
        apply Prod.ext
        · rfl
        · funext i
          exact Fin.elim0 i
      rw [hfunction]
      exact hresult
  | succ n =>
      let fullPrefix : ((ℕ → ℕ × Bool) × (ℕ → ℝ)) →
          (ℕ × ℕ) × (Fin (n + 1) → Bool) :=
        manyServerMarkedCanonicalClockPrefix time n
      let fullLaw : Measure ((ℕ × ℕ) × (Fin (n + 1) → Bool)) :=
        (initial.toMeasure.prod countLaw).prod (markLaw (n + 1))
      let dropState : ((ℕ × ℕ) × (Fin (n + 1) → Bool)) →
          ℕ × (Fin (n + 1) → Bool) :=
        fun value => (value.1.2, value.2)
      have hfull : HasLaw fullPrefix fullLaw (trajectory.prod gaps) := by
        simpa [fullPrefix, fullLaw, countLaw, markLaw, trajectory, gaps, rate] using
          (stationaryManyServerMarkedCanonicalClockPrefix_hasLaw
            (initial := initial) trafficIntensity serviceRate servers hservers hserviceRate htime n)
      letI : IsProbabilityMeasure (markLaw (n + 1)) := by
        dsimp [markLaw]
        infer_instance
      have hdrop : HasLaw dropState (countLaw.prod (markLaw (n + 1))) fullLaw := by
        refine ⟨(measurable_snd.comp measurable_fst |>.prodMk measurable_snd).aemeasurable, ?_⟩
        change Measure.map dropState
          ((initial.toMeasure.prod countLaw).prod (markLaw (n + 1))) = _
        calc
          Measure.map dropState
              ((initial.toMeasure.prod countLaw).prod (markLaw (n + 1))) =
              (Measure.map Prod.snd (initial.toMeasure.prod countLaw)).prod
                (Measure.map id (markLaw (n + 1))) := by
                  change Measure.map (Prod.map Prod.snd id)
                    ((initial.toMeasure.prod countLaw).prod (markLaw (n + 1))) = _
                  exact (Measure.map_prod_map (initial.toMeasure.prod countLaw)
                    (markLaw (n + 1)) measurable_snd measurable_id).symm
          _ = countLaw.prod (markLaw (n + 1)) := by
                rw [Measure.map_snd_prod, measure_univ, one_smul, Measure.map_id]
      have hresult := hdrop.comp hfull
      change HasLaw (fun value : (ℕ → ℕ × Bool) × (ℕ → ℝ) =>
        (count value.2, fun i : Fin (n + 1) => (value.1 i).2))
        (countLaw.prod (markLaw (n + 1))) (trajectory.prod gaps)
      simpa [fullPrefix, dropState, count] using hresult

/-- The literal finite marked-Poisson sample formed from the actual marks up
to the canonical all-event-clock horizon. -/
def manyServerMarkedCanonicalHorizonSample (time : ℝ) :
    ((ℕ → ℕ × Bool) × (ℕ → ℝ)) → FiniteHorizonMarkedPoisson.Sample :=
  fun value =>
    ⟨PoissonProcess.canonicalRenewalCount time value.2,
      fun i => (value.1 i).2⟩

theorem measurable_manyServerMarkedCanonicalHorizonSample (time : ℝ) :
    Measurable (manyServerMarkedCanonicalHorizonSample time) := by
  classical
  let count : ((ℕ → ℕ × Bool) × (ℕ → ℝ)) → ℕ :=
    fun value => PoissonProcess.canonicalRenewalCount time value.2
  have hcount : Measurable count :=
    (PoissonProcess.measurable_canonicalRenewalCount time).comp measurable_snd
  refine measurable_to_countable' ?_
  rintro ⟨n, marks⟩
  have hpreimage :
      manyServerMarkedCanonicalHorizonSample time ⁻¹' ({⟨n, marks⟩} : Set _) =
        (count ⁻¹' ({n} : Set ℕ)) ∩
          ⋂ i : Fin n, {value : (ℕ → ℕ × Bool) × (ℕ → ℝ) |
            (value.1 i).2 = marks i} := by
    ext value
    simp [manyServerMarkedCanonicalHorizonSample, count]
    intro hcountValue
    subst n
    constructor
    · intro hvalue i
      exact congr_fun (eq_of_heq hvalue) i
    · intro hvalue
      exact heq_of_eq (funext hvalue)
  rw [hpreimage]
  apply (hcount (measurableSet_singleton _)).inter
  apply MeasurableSet.iInter
  intro i
  exact measurableSet_eq.preimage
    (measurable_snd.comp ((measurable_pi_apply (i : ℕ)).comp measurable_fst))

/-- The actual random-horizon canonical mark sample has exactly the reusable
finite marked-Poisson law.  Thus no synthetic mark vector is substituted when
applying finite-horizon thinning. -/
theorem stationaryManyServerMarkedCanonicalHorizonSample_hasLaw
    {initial : PMF ℕ} (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers : ℕ) (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    {time : ℝ} (htime : 0 ≤ time) :
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    let mean : ℝ≥0 := ⟨rate * time, mul_nonneg
      (le_of_lt (manyServerUniformizationRate_pos trafficIntensity serviceRate
        servers hservers hserviceRate)) htime⟩
    let arrivalProbability := uniformizedBirthProbability trafficIntensity
    HasLaw (manyServerMarkedCanonicalHorizonSample time)
      (FiniteHorizonMarkedPoisson.jointPMF mean arrivalProbability
        (uniformizedBirthProbability_le_one trafficIntensity)).toMeasure
      ((stationaryTrajMeasure
        (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
        (manyServerMarkedStateUniformizationMeasureKernel
          trafficIntensity servers hservers)).prod
        (PoissonProcess.exponentialInterarrivalMeasure rate)) := by
  dsimp only
  let rate : ℝ := manyServerUniformizationRate
    (trafficIntensity : ℝ) serviceRate servers
  let mean : ℝ≥0 := ⟨rate * time, mul_nonneg
    (le_of_lt (manyServerUniformizationRate_pos trafficIntensity serviceRate
      servers hservers hserviceRate)) htime⟩
  let arrivalProbability : ℝ≥0 := uniformizedBirthProbability trafficIntensity
  let arrivalProbability_le_one : arrivalProbability ≤ 1 :=
    uniformizedBirthProbability_le_one trafficIntensity
  let trajectory : Measure (ℕ → ℕ × Bool) := stationaryTrajMeasure
    (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
    (manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers)
  let gaps : Measure (ℕ → ℝ) :=
    PoissonProcess.exponentialInterarrivalMeasure rate
  let source : Measure ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := trajectory.prod gaps
  let countPrefix (n : ℕ) : ((ℕ → ℕ × Bool) × (ℕ → ℝ)) →
      ℕ × (Fin n → Bool) := manyServerMarkedCanonicalClockMarkPrefix time n
  have hrate : 0 < rate := by
    exact manyServerUniformizationRate_pos trafficIntensity serviceRate
      servers hservers hserviceRate
  letI : IsProbabilityMeasure initial.toMeasure := by infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsProbabilityMeasure gaps :=
    PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure source := by
    dsimp [source]
    infer_instance
  refine ⟨(measurable_manyServerMarkedCanonicalHorizonSample time).aemeasurable, ?_⟩
  apply Measure.ext_of_singleton
  rintro ⟨n, marks⟩
  let markPrefix : ((ℕ → ℕ × Bool) × (ℕ → ℝ)) → ℕ × (Fin n → Bool) :=
    countPrefix n
  have hprefix : HasLaw markPrefix
      ((ProbabilityTheory.poissonMeasure mean).prod
        (FiniteHorizonMarkedPoisson.iidMarks arrivalProbability
          arrivalProbability_le_one n).toMeasure) source := by
    simpa [markPrefix, countPrefix, source, trajectory, gaps, rate, mean,
      arrivalProbability, arrivalProbability_le_one] using
      (stationaryManyServerMarkedCanonicalClockMarkPrefix_hasLaw
        (initial := initial) trafficIntensity serviceRate servers hservers hserviceRate htime n)
  have hprefMeas : Measurable markPrefix := by
    dsimp [markPrefix, countPrefix]
    exact measurable_manyServerMarkedCanonicalClockMarkPrefix time n
  have hpreimage :
      manyServerMarkedCanonicalHorizonSample time ⁻¹' ({⟨n, marks⟩} : Set _) =
        markPrefix ⁻¹' ({(n, marks)} : Set _) := by
    ext value
    simp [manyServerMarkedCanonicalHorizonSample, markPrefix, countPrefix]
    constructor
    · rintro ⟨hcount, hvalue⟩
      cases hcount
      apply Prod.ext
      · rfl
      · exact eq_of_heq hvalue
    · intro hvalue
      cases hvalue
      exact ⟨rfl, heq_of_eq rfl⟩
  rw [Measure.map_apply (measurable_manyServerMarkedCanonicalHorizonSample time)
    (measurableSet_singleton _), hpreimage,
    ← Measure.map_apply hprefMeas (measurableSet_singleton _),
    hprefix.map_eq, ← Set.singleton_prod_singleton, Measure.prod_prod,
    PMF.toMeasure_apply_singleton
      (FiniteHorizonMarkedPoisson.jointPMF mean arrivalProbability
        arrivalProbability_le_one)
      (FiniteHorizonMarkedPoisson.Sample.mk n marks) (measurableSet_singleton _),
    FiniteHorizonMarkedPoisson.jointPMF_apply]
  calc
    (ProbabilityTheory.poissonMeasure mean) {n} *
        (FiniteHorizonMarkedPoisson.iidMarks arrivalProbability
          arrivalProbability_le_one n).toMeasure {marks} =
        ((ProbabilityTheory.poissonMeasure mean).toPMF).toMeasure {n} *
          (FiniteHorizonMarkedPoisson.iidMarks arrivalProbability
            arrivalProbability_le_one n).toMeasure {marks} := by
              rw [Measure.toPMF_toMeasure]
    _ = (ProbabilityTheory.poissonMeasure mean).toPMF n *
          (FiniteHorizonMarkedPoisson.iidMarks arrivalProbability
            arrivalProbability_le_one n) marks := by
              rw [PMF.toMeasure_apply_singleton
                (ProbabilityTheory.poissonMeasure mean).toPMF n
                (measurableSet_singleton _),
                PMF.toMeasure_apply_singleton
                  (FiniteHorizonMarkedPoisson.iidMarks arrivalProbability
                    arrivalProbability_le_one n)
                  marks (measurableSet_singleton _)]

/-- Separate the canonical exponential clock path from the complete retained
arrival-versus-potential-service mark path. -/
def manyServerMarkedCanonicalDriverFactors :
    ((ℕ → ℕ × Bool) × (ℕ → ℝ)) → (ℕ → ℝ) × (ℕ → Bool) :=
  fun value => (value.2, manyServerMarkedStateArrivalMarkPath value.1)

theorem measurable_manyServerMarkedCanonicalDriverFactors :
    Measurable manyServerMarkedCanonicalDriverFactors := by
  exact measurable_snd.prodMk
    (measurable_manyServerMarkedStateArrivalMarkPath.comp measurable_fst)

/-- The canonical clock path and retained event-mark path have the exact
product law of independent exponential gaps and an iid Bernoulli stream. -/
theorem manyServerMarkedCanonicalDriverFactors_hasLaw
    {initial : PMF ℕ} (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers : ℕ) (hservers : 0 < servers) (hserviceRate : 0 < serviceRate) :
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    HasLaw manyServerMarkedCanonicalDriverFactors
      ((PoissonProcess.exponentialInterarrivalMeasure rate).prod
        (IIDStream.measure
          (manyServerUniformizationArrivalMark trafficIntensity).toMeasure))
      ((stationaryTrajMeasure
        (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
        (manyServerMarkedStateUniformizationMeasureKernel
          trafficIntensity servers hservers)).prod
        (PoissonProcess.exponentialInterarrivalMeasure rate)) := by
  dsimp only
  let rate : ℝ := manyServerUniformizationRate
    (trafficIntensity : ℝ) serviceRate servers
  let markLaw : Measure Bool :=
    (manyServerUniformizationArrivalMark trafficIntensity).toMeasure
  let trajectory : Measure (ℕ → ℕ × Bool) := stationaryTrajMeasure
    (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
    (manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers)
  let gaps : Measure (ℕ → ℝ) :=
    PoissonProcess.exponentialInterarrivalMeasure rate
  let source : Measure ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := trajectory.prod gaps
  let marks : (ℕ → ℕ × Bool) → ℕ → Bool :=
    manyServerMarkedStateArrivalMarkPath
  let lift : ((ℕ → ℕ × Bool) × (ℕ → ℝ)) → (ℕ → Bool) × (ℕ → ℝ) :=
    Prod.map marks id
  have hrate : 0 < rate := by
    exact manyServerUniformizationRate_pos trafficIntensity serviceRate
      servers hservers hserviceRate
  letI : IsProbabilityMeasure initial.toMeasure := by infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsProbabilityMeasure gaps :=
    PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure markLaw := by
    dsimp [markLaw]
    infer_instance
  letI : IsProbabilityMeasure (IIDStream.measure markLaw) := by
    dsimp [IIDStream.measure]
    infer_instance
  have hmarks : HasLaw marks (IIDStream.measure markLaw) trajectory := by
    simpa [marks, markLaw, trajectory] using
      (manyServerMarkedStateTrajectory_arrivalMarkPath_hasLaw
        (initial := initial) trafficIntensity servers hservers)
  have hlift : Measurable lift := by
    simpa [lift, marks] using
      measurable_manyServerMarkedStateArrivalMarkPath.prodMap measurable_id
  refine ⟨measurable_manyServerMarkedCanonicalDriverFactors.aemeasurable, ?_⟩
  calc
    Measure.map manyServerMarkedCanonicalDriverFactors source =
        Measure.map (Prod.swap ∘ lift) source := by
          rfl
    _ = Measure.map Prod.swap (Measure.map lift source) := by
          exact (Measure.map_map measurable_swap hlift).symm
    _ = Measure.map Prod.swap
          ((Measure.map marks trajectory).prod (Measure.map id gaps)) := by
            rw [show lift = Prod.map marks id by rfl,
              Measure.map_prod_map trajectory gaps
                measurable_manyServerMarkedStateArrivalMarkPath measurable_id]
    _ = Measure.map Prod.swap ((IIDStream.measure markLaw).prod gaps) := by
          rw [hmarks.map_eq, Measure.map_id]
    _ = gaps.prod (IIDStream.measure markLaw) := by
          rw [Measure.prod_swap]

/-- Retain the initial queue length jointly with the canonical exponential
clock path and the complete retained event-mark path. -/
def manyServerMarkedCanonicalInitialDriverFactors :
    ((ℕ → ℕ × Bool) × (ℕ → ℝ)) → ℕ × ((ℕ → ℝ) × (ℕ → Bool)) :=
  fun value => ((value.1 0).1, (value.2, manyServerMarkedStateArrivalMarkPath value.1))

/-- The initial-state/complete-driver factor map is Borel measurable. -/
theorem measurable_manyServerMarkedCanonicalInitialDriverFactors :
    Measurable manyServerMarkedCanonicalInitialDriverFactors := by
  exact ((measurable_fst.comp ((measurable_pi_apply 0).comp measurable_fst)).prodMk
    (measurable_snd.prodMk
      (measurable_manyServerMarkedStateArrivalMarkPath.comp measurable_fst)))

/-- The initial queue length is independent of the complete canonical driver:
the joint law is the product of the initial law, exponential-gap law, and iid
event-mark-stream law. -/
theorem manyServerMarkedCanonicalInitialDriverFactors_hasLaw
    {initial : PMF ℕ} (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers : ℕ) (hservers : 0 < servers) (hserviceRate : 0 < serviceRate) :
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    HasLaw manyServerMarkedCanonicalInitialDriverFactors
      (initial.toMeasure.prod
        ((PoissonProcess.exponentialInterarrivalMeasure rate).prod
          (IIDStream.measure
            (manyServerUniformizationArrivalMark trafficIntensity).toMeasure)))
      ((stationaryTrajMeasure
        (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
        (manyServerMarkedStateUniformizationMeasureKernel
          trafficIntensity servers hservers)).prod
        (PoissonProcess.exponentialInterarrivalMeasure rate)) := by
  dsimp only
  let rate : ℝ := manyServerUniformizationRate
    (trafficIntensity : ℝ) serviceRate servers
  let markLaw : Measure Bool :=
    (manyServerUniformizationArrivalMark trafficIntensity).toMeasure
  let trajectory : Measure (ℕ → (ℕ × Bool)) := stationaryTrajMeasure
    (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
    (manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers)
  let gaps : Measure (ℕ → ℝ) :=
    PoissonProcess.exponentialInterarrivalMeasure rate
  let source : Measure ((ℕ → (ℕ × Bool)) × (ℕ → ℝ)) := trajectory.prod gaps
  let state : (ℕ → (ℕ × Bool)) → ℕ := fun path => (path 0).1
  let marks : (ℕ → (ℕ × Bool)) → ℕ → Bool :=
    manyServerMarkedStateArrivalMarkPath
  let stateMarks : (ℕ → (ℕ × Bool)) → ℕ × (ℕ → Bool) :=
    fun path => (state path, marks path)
  let lift : ((ℕ → (ℕ × Bool)) × (ℕ → ℝ)) →
      (ℕ × (ℕ → Bool)) × (ℕ → ℝ) := Prod.map stateMarks id
  let reorder : (ℕ × (ℕ → Bool)) × (ℕ → ℝ) →
      ℕ × ((ℕ → ℝ) × (ℕ → Bool)) :=
    fun value => (value.1.1, (value.2, value.1.2))
  have hrate : 0 < rate :=
    manyServerUniformizationRate_pos trafficIntensity serviceRate
      servers hservers hserviceRate
  letI : IsProbabilityMeasure initial.toMeasure := by infer_instance
  letI : IsProbabilityMeasure markLaw := by
    dsimp [markLaw]
    infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsProbabilityMeasure gaps := by
    dsimp [gaps]
    exact PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure (IIDStream.measure markLaw) := by
    dsimp [IIDStream.measure]
    infer_instance
  have hstate : Measure.map state trajectory = initial.toMeasure := by
    let markedInitial : Measure (ℕ × Bool) :=
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
    let markedKernel : Kernel (ℕ × Bool) (ℕ × Bool) :=
      manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers
    have hzero : Measure.map (fun path : ℕ → ℕ × Bool => path 0) trajectory =
        markedInitial := by
      simpa [trajectory, markedInitial, markedKernel] using
        (stationaryTrajMeasure_zero_marginal (π := markedInitial) (K := markedKernel))
    calc
      Measure.map state trajectory =
          Measure.map Prod.fst
            (Measure.map (fun path : ℕ → ℕ × Bool => path 0) trajectory) := by
              rw [Measure.map_map measurable_fst (measurable_pi_apply 0)]
              rfl
      _ = Measure.map Prod.fst markedInitial := by rw [hzero]
      _ = initial.toMeasure := by
            rw [show markedInitial = initial.toMeasure.prod markLaw by
              exact manyServerMarkedStatePMF_toMeasure_eq_prod initial trafficIntensity]
            rw [Measure.map_fst_prod, measure_univ, one_smul]
  have hmarks : Measure.map marks trajectory = IIDStream.measure markLaw := by
    simpa [marks, markLaw, trajectory] using
      (manyServerMarkedStateTrajectory_arrivalMarkPath_hasLaw
        (initial := initial) trafficIntensity servers hservers).map_eq
  have hindependent : IndepFun state marks trajectory := by
    simpa [state, marks, trajectory] using
      (manyServerMarkedStateTrajectory_initial_indep_arrivalMarkPath
        (initial := initial) trafficIntensity servers hservers)
  have hstateMarks : Measure.map stateMarks trajectory =
      initial.toMeasure.prod (IIDStream.measure markLaw) := by
    apply (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
      (measurable_fst.comp (measurable_pi_apply 0)).aemeasurable
      measurable_manyServerMarkedStateArrivalMarkPath.aemeasurable).1 at hindependent
    change Measure.map stateMarks trajectory =
      (Measure.map state trajectory).prod (Measure.map marks trajectory) at hindependent
    rw [hstate, hmarks] at hindependent
    exact hindependent
  have hlift : Measurable lift := by
    exact ((measurable_fst.comp (measurable_pi_apply 0)).prodMk
      measurable_manyServerMarkedStateArrivalMarkPath).prodMap measurable_id
  have hassoc : Measure.map MeasurableEquiv.prodAssoc
      ((initial.toMeasure.prod (IIDStream.measure markLaw)).prod gaps) =
      initial.toMeasure.prod ((IIDStream.measure markLaw).prod gaps) := by
    simpa using (measurePreserving_prodAssoc
      initial.toMeasure (IIDStream.measure markLaw) gaps).map_eq
  have hswap : Measure.map (Prod.map id Prod.swap)
      (initial.toMeasure.prod ((IIDStream.measure markLaw).prod gaps)) =
      initial.toMeasure.prod (gaps.prod (IIDStream.measure markLaw)) := by
    rw [← Measure.map_prod_map initial.toMeasure ((IIDStream.measure markLaw).prod gaps)
      measurable_id measurable_swap, Measure.map_id, Measure.prod_swap]
  refine ⟨measurable_manyServerMarkedCanonicalInitialDriverFactors.aemeasurable, ?_⟩
  calc
    Measure.map manyServerMarkedCanonicalInitialDriverFactors source =
        Measure.map reorder (Measure.map lift source) := by
          rw [Measure.map_map (by
            exact (measurable_id.prodMap measurable_swap).comp
              MeasurableEquiv.prodAssoc.measurable) hlift]
          rfl
    _ = Measure.map reorder
        ((Measure.map stateMarks trajectory).prod (Measure.map id gaps)) := by
          congr 1
          change Measure.map (Prod.map stateMarks id) (trajectory.prod gaps) = _
          symm
          exact Measure.map_prod_map trajectory gaps
            ((measurable_fst.comp (measurable_pi_apply 0)).prodMk
              measurable_manyServerMarkedStateArrivalMarkPath) measurable_id
    _ = Measure.map reorder
        ((initial.toMeasure.prod (IIDStream.measure markLaw)).prod gaps) := by
          rw [hstateMarks, Measure.map_id]
    _ = Measure.map (Prod.map id Prod.swap)
        (Measure.map MeasurableEquiv.prodAssoc
          ((initial.toMeasure.prod (IIDStream.measure markLaw)).prod gaps)) := by
            rw [Measure.map_map (measurable_id.prodMap measurable_swap)
              MeasurableEquiv.prodAssoc.measurable]
            rfl
    _ = Measure.map (Prod.map id Prod.swap)
        (initial.toMeasure.prod ((IIDStream.measure markLaw).prod gaps)) := by
          rw [hassoc]
    _ = initial.toMeasure.prod (gaps.prod (IIDStream.measure markLaw)) := by
          rw [hswap]

/-- The initial queue coordinate is independent of the complete canonical
clock-and-mark driver. -/
theorem manyServerMarkedCanonicalInitialQueue_indep_driverFactors
    {initial : PMF ℕ} (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers : ℕ) (hservers : 0 < servers) (hserviceRate : 0 < serviceRate) :
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    IndepFun manyServerMarkedCanonicalInitialQueue
      manyServerMarkedCanonicalDriverFactors
      ((stationaryTrajMeasure
        (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
        (manyServerMarkedStateUniformizationMeasureKernel
          trafficIntensity servers hservers)).prod
        (PoissonProcess.exponentialInterarrivalMeasure rate)) := by
  dsimp only
  let rate : ℝ := manyServerUniformizationRate
    (trafficIntensity : ℝ) serviceRate servers
  let markLaw : Measure Bool :=
    (manyServerUniformizationArrivalMark trafficIntensity).toMeasure
  let trajectory : Measure (ℕ → (ℕ × Bool)) := stationaryTrajMeasure
    (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
    (manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers)
  let gaps : Measure (ℕ → ℝ) :=
    PoissonProcess.exponentialInterarrivalMeasure rate
  let source : Measure ((ℕ → (ℕ × Bool)) × (ℕ → ℝ)) := trajectory.prod gaps
  have hrate : 0 < rate :=
    manyServerUniformizationRate_pos trafficIntensity serviceRate
      servers hservers hserviceRate
  letI : IsProbabilityMeasure initial.toMeasure := by infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsProbabilityMeasure gaps := by
    dsimp [gaps]
    exact PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure markLaw := by
    dsimp [markLaw]
    infer_instance
  letI : IsProbabilityMeasure (IIDStream.measure markLaw) := by
    dsimp [IIDStream.measure]
    infer_instance
  let initialDriver : ((ℕ → (ℕ × Bool)) × (ℕ → ℝ)) →
      ℕ × ((ℕ → ℝ) × (ℕ → Bool)) :=
    fun value => (manyServerMarkedCanonicalInitialQueue value,
      manyServerMarkedCanonicalDriverFactors value)
  have hinitialDriver : Measure.map initialDriver source =
      initial.toMeasure.prod (gaps.prod (IIDStream.measure markLaw)) := by
    simpa [initialDriver, source, trajectory, gaps, markLaw, rate,
      manyServerMarkedCanonicalInitialDriverFactors] using
      (manyServerMarkedCanonicalInitialDriverFactors_hasLaw
        (initial := initial) trafficIntensity serviceRate servers hservers hserviceRate).map_eq
  have hinitialDriver_meas : Measurable initialDriver := by
    exact measurable_manyServerMarkedCanonicalInitialQueue.prodMk
      measurable_manyServerMarkedCanonicalDriverFactors
  have hinitial : Measure.map manyServerMarkedCanonicalInitialQueue source =
      initial.toMeasure := by
    change Measure.map (Prod.fst ∘ initialDriver) source = initial.toMeasure
    rw [← Measure.map_map measurable_fst hinitialDriver_meas, hinitialDriver,
      Measure.map_fst_prod, measure_univ, one_smul]
  have hdrivers : Measure.map manyServerMarkedCanonicalDriverFactors source =
      gaps.prod (IIDStream.measure markLaw) := by
    change Measure.map (Prod.snd ∘ initialDriver) source =
      gaps.prod (IIDStream.measure markLaw)
    rw [← Measure.map_map measurable_snd hinitialDriver_meas, hinitialDriver,
      Measure.map_snd_prod, measure_univ, one_smul]
  apply (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
    measurable_manyServerMarkedCanonicalInitialQueue.aemeasurable
    measurable_manyServerMarkedCanonicalDriverFactors.aemeasurable).2
  change Measure.map initialDriver source =
    (Measure.map manyServerMarkedCanonicalInitialQueue source).prod
      (Measure.map manyServerMarkedCanonicalDriverFactors source)
  rw [hinitialDriver, hinitial, hdrivers]

/-- At a deterministic physical time, retain the fresh residual clock path
and the actual unused mark suffix. -/
def manyServerMarkedCanonicalFutureDriver (start : ℝ) :
    ((ℕ → ℕ × Bool) × (ℕ → ℝ)) → (ℕ → ℝ) × (ℕ → Bool) :=
  fun value =>
    (PoissonProcess.residualTail start value.2,
      IIDStream.externalIndexTail (α := Bool)
        (fun gaps => PoissonProcess.canonicalRenewalCount start gaps)
        (value.2, manyServerMarkedStateArrivalMarkPath value.1))

/-- The deterministic-time future driver is Borel measurable. -/
theorem measurable_manyServerMarkedCanonicalFutureDriver (start : ℝ) :
    Measurable (manyServerMarkedCanonicalFutureDriver start) := by
  apply ((PoissonProcess.measurable_residualTail start).comp measurable_snd).prodMk
  apply (IIDStream.measurable_externalIndexTail (α := Bool)
    (fun gaps => PoissonProcess.canonicalRenewalCount start gaps)
    (PoissonProcess.measurable_canonicalRenewalCount start)).comp
  exact measurable_snd.prodMk
    (measurable_manyServerMarkedStateArrivalMarkPath.comp measurable_fst)

/-- After any nonnegative deterministic time, the actual unused clock and
mark paths have the same independent product law as a fresh marked driver.
This is the deterministic-time restart law needed for interval increments. -/
theorem manyServerMarkedCanonicalFutureDriver_hasLaw
    {initial : PMF ℕ} (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers : ℕ) (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    {start : ℝ} (hstart : 0 ≤ start) :
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    let markLaw : Measure Bool :=
      (manyServerUniformizationArrivalMark trafficIntensity).toMeasure
    HasLaw (manyServerMarkedCanonicalFutureDriver start)
      ((PoissonProcess.exponentialInterarrivalMeasure rate).prod
        (IIDStream.measure markLaw))
      ((stationaryTrajMeasure
        (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
        (manyServerMarkedStateUniformizationMeasureKernel
          trafficIntensity servers hservers)).prod
        (PoissonProcess.exponentialInterarrivalMeasure rate)) := by
  dsimp only
  let rate : ℝ := manyServerUniformizationRate
    (trafficIntensity : ℝ) serviceRate servers
  let markLaw : Measure Bool :=
    (manyServerUniformizationArrivalMark trafficIntensity).toMeasure
  let trajectory : Measure (ℕ → ℕ × Bool) := stationaryTrajMeasure
    (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
    (manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers)
  let gaps : Measure (ℕ → ℝ) :=
    PoissonProcess.exponentialInterarrivalMeasure rate
  let source : Measure ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := trajectory.prod gaps
  let drivers : ((ℕ → ℕ × Bool) × (ℕ → ℝ)) →
      (ℕ → ℝ) × (ℕ → Bool) := manyServerMarkedCanonicalDriverFactors
  let index : (ℕ → ℝ) → ℕ :=
    fun clock => PoissonProcess.canonicalRenewalCount start clock
  let restart : ((ℕ → ℝ) × (ℕ → Bool)) → (ℕ → ℝ) × (ℕ → Bool) :=
    fun value =>
      (PoissonProcess.residualTail start value.1,
        IIDStream.externalIndexTail (α := Bool) index value)
  have hrate : 0 < rate := by
    exact manyServerUniformizationRate_pos trafficIntensity serviceRate
      servers hservers hserviceRate
  letI : IsProbabilityMeasure initial.toMeasure := by infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsProbabilityMeasure gaps :=
    PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure markLaw := by
    dsimp [markLaw]
    infer_instance
  letI : IsProbabilityMeasure (IIDStream.measure markLaw) := by
    dsimp [IIDStream.measure]
    infer_instance
  have hdrivers : HasLaw drivers (gaps.prod (IIDStream.measure markLaw)) source := by
    simpa [drivers, source, trajectory, gaps, markLaw, rate] using
      (manyServerMarkedCanonicalDriverFactors_hasLaw
        (initial := initial) trafficIntensity serviceRate servers hservers hserviceRate)
  have hrestartRaw : HasLaw restart
      ((gaps.map (PoissonProcess.residualTail start)).prod
        (IIDStream.measure markLaw))
      (gaps.prod (IIDStream.measure markLaw)) := by
    simpa [restart, index] using
      (IIDStream.externalIndexTail_joint_hasLaw gaps markLaw index
        (PoissonProcess.measurable_canonicalRenewalCount start)
        (PoissonProcess.residualTail start)
        (PoissonProcess.measurable_residualTail start))
  have hrestart : HasLaw restart
      (gaps.prod (IIDStream.measure markLaw))
      (gaps.prod (IIDStream.measure markLaw)) := by
    refine ⟨hrestartRaw.aemeasurable, ?_⟩
    calc
      Measure.map restart (gaps.prod (IIDStream.measure markLaw)) =
          (gaps.map (PoissonProcess.residualTail start)).prod
            (IIDStream.measure markLaw) := hrestartRaw.map_eq
      _ = gaps.prod (IIDStream.measure markLaw) := by
            rw [(PoissonProcess.residualTail_hasLaw_path hrate hstart).map_eq]
  have hfuture := hrestart.comp hdrivers
  simpa [manyServerMarkedCanonicalFutureDriver, drivers, restart, index,
    Function.comp_def, source, trajectory, gaps, markLaw, rate] using hfuture

/-- Form a literal finite marked-Poisson sample from a clock path and its
independent complete Boolean mark path. -/
def manyServerMarkedFreshHorizonSample (time : ℝ) :
    ((ℕ → ℝ) × (ℕ → Bool)) → FiniteHorizonMarkedPoisson.Sample :=
  fun value =>
    ⟨PoissonProcess.canonicalRenewalCount time value.1, fun i => value.2 i⟩

/-- The number of arrival-mark events up to a horizon, viewed directly as a
function of a fresh exponential-clock/IID-mark driver. -/
def manyServerMarkedFreshArrivalCount (time : ℝ) :
    ((ℕ → ℝ) × (ℕ → Bool)) → ℕ :=
  FiniteHorizonMarkedPoisson.kept ∘ manyServerMarkedFreshHorizonSample time

/-- The number of potential-service-mark events up to a horizon, viewed
directly as a function of a fresh exponential-clock/IID-mark driver. -/
def manyServerMarkedFreshPotentialServiceCount (time : ℝ) :
    ((ℕ → ℝ) × (ℕ → Bool)) → ℕ :=
  FiniteHorizonMarkedPoisson.discarded ∘ manyServerMarkedFreshHorizonSample time

/-- Form a fixed-size marked sample from an IID prefix with exactly the
required number of Boolean coordinates. -/
def manyServerMarkedPrefixSample (n : ℕ) :
    ((ℕ → ℝ) × (Finset.range n → Bool)) →
      FiniteHorizonMarkedPoisson.Sample :=
  fun value => ⟨n, fun i => value.2 ⟨i, Finset.mem_range.mpr i.isLt⟩⟩

/-- The fixed-size prefix sampler is Borel measurable. -/
theorem measurable_manyServerMarkedPrefixSample (n : ℕ) :
    Measurable (manyServerMarkedPrefixSample n) := by
  unfold manyServerMarkedPrefixSample
  apply measurable_to_countable'
  rintro ⟨m, marks⟩
  by_cases hnm : n = m
  · subst m
    have hpreimage :
        (fun value : (ℕ → ℝ) × (Finset.range n → Bool) =>
          FiniteHorizonMarkedPoisson.Sample.mk n
            (fun i => value.2 ⟨i, Finset.mem_range.mpr i.isLt⟩)) ⁻¹'
            ({⟨n, marks⟩} : Set _) =
          {value : (ℕ → ℝ) × (Finset.range n → Bool) |
            ∀ i : Fin n, value.2 ⟨i, Finset.mem_range.mpr i.isLt⟩ = marks i} := by
          ext value
          simp
          constructor
          · intro hvalue i
            exact congr_fun hvalue i
          · intro hvalue
            exact funext hvalue
    rw [hpreimage]
    rw [show {value : (ℕ → ℝ) × (Finset.range n → Bool) |
        ∀ i : Fin n, value.2 ⟨i, Finset.mem_range.mpr i.isLt⟩ = marks i} =
        ⋂ i : Fin n, {value : (ℕ → ℝ) × (Finset.range n → Bool) |
          value.2 ⟨i, Finset.mem_range.mpr i.isLt⟩ = marks i} by
      ext value
      simp]
    apply MeasurableSet.iInter
    intro i
    exact measurableSet_eq.preimage
      ((measurable_pi_apply
        (⟨(i : ℕ), Finset.mem_range.mpr i.isLt⟩ : Finset.range n)).comp measurable_snd)
  · have hempty :
        (fun value : (ℕ → ℝ) × (Finset.range n → Bool) =>
          FiniteHorizonMarkedPoisson.Sample.mk n
            (fun i => value.2 ⟨i, Finset.mem_range.mpr i.isLt⟩)) ⁻¹'
            ({⟨m, marks⟩} : Set _) = ∅ := by
          ext value
          simp [hnm]
    rw [hempty]
    exact MeasurableSet.empty

/-- A fresh marked horizon sample is observable from the external exponential
clock path and exactly the random number of IID marks it consumes. -/
theorem externalIndexPrefixEvent_preimage_manyServerMarkedFreshHorizonSample
    (time : ℝ) (S : Set FiniteHorizonMarkedPoisson.Sample)
    (hS : MeasurableSet S) :
    IIDStream.ExternalIndexPrefixEvent
      (fun gaps : ℕ → ℝ => PoissonProcess.canonicalRenewalCount time gaps)
      (manyServerMarkedFreshHorizonSample time ⁻¹' S) := by
  intro n
  let prefixSample : ((ℕ → ℝ) × (Finset.range n → Bool)) →
      FiniteHorizonMarkedPoisson.Sample := manyServerMarkedPrefixSample n
  refine ⟨prefixSample ⁻¹' S,
    hS.preimage (measurable_manyServerMarkedPrefixSample n), ?_⟩
  ext value
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hvalue, hcount⟩
    refine ⟨?_, hcount⟩
    have hsample : manyServerMarkedFreshHorizonSample time value =
        prefixSample
          (IIDStream.stateInitialPrefix (σ := ℕ → ℝ) (α := Bool) n value) := by
      change FiniteHorizonMarkedPoisson.Sample.mk
          (PoissonProcess.canonicalRenewalCount time value.1)
          (fun i => value.2 i) =
        FiniteHorizonMarkedPoisson.Sample.mk n
          (fun i => value.2 (i : ℕ))
      rw [hcount]
    rw [← hsample]
    exact hvalue
  · rintro ⟨hvalue, hcount⟩
    refine ⟨?_, hcount⟩
    have hsample : manyServerMarkedFreshHorizonSample time value =
        prefixSample
          (IIDStream.stateInitialPrefix (σ := ℕ → ℝ) (α := Bool) n value) := by
      change FiniteHorizonMarkedPoisson.Sample.mk
          (PoissonProcess.canonicalRenewalCount time value.1)
          (fun i => value.2 i) =
        FiniteHorizonMarkedPoisson.Sample.mk n
          (fun i => value.2 (i : ℕ))
      rw [hcount]
    rw [hsample]
    exact hvalue

/-- A marked horizon sample is independent of the complete unused IID mark
tail after its random clock-selected prefix.  The exponential clock remains
part of the first factor, so this is the marked restart identity needed when
constructing successive physical intervals. -/
theorem indepFun_manyServerMarkedFreshHorizonSample_externalIndexTail
    {rate : ℝ} (hrate : 0 < rate) (markLaw : Measure Bool)
    [IsProbabilityMeasure markLaw] (time : ℝ) :
    IndepFun (manyServerMarkedFreshHorizonSample time)
      (IIDStream.externalIndexTail (α := Bool)
        (fun gaps : ℕ → ℝ => PoissonProcess.canonicalRenewalCount time gaps))
      ((PoissonProcess.exponentialInterarrivalMeasure rate).prod
        (IIDStream.measure markLaw)) := by
  let gaps : Measure (ℕ → ℝ) :=
    PoissonProcess.exponentialInterarrivalMeasure rate
  let index : (ℕ → ℝ) → ℕ :=
    fun clock => PoissonProcess.canonicalRenewalCount time clock
  letI : IsProbabilityMeasure gaps :=
    PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure (IIDStream.measure markLaw) := by
    dsimp [IIDStream.measure]
    infer_instance
  simpa [gaps, index] using
    (IIDStream.indepFun_of_externalIndexPrefixEvent_tail gaps markLaw index
      (PoissonProcess.measurable_canonicalRenewalCount time)
      (manyServerMarkedFreshHorizonSample time)
      (fun S hS =>
        externalIndexPrefixEvent_preimage_manyServerMarkedFreshHorizonSample
          time S hS))

/-- The fresh-driver finite marked sample is Borel measurable. -/
theorem measurable_manyServerMarkedFreshHorizonSample (time : ℝ) :
    Measurable (manyServerMarkedFreshHorizonSample time) := by
  classical
  let count : ((ℕ → ℝ) × (ℕ → Bool)) → ℕ :=
    fun value => PoissonProcess.canonicalRenewalCount time value.1
  have hcount : Measurable count :=
    (PoissonProcess.measurable_canonicalRenewalCount time).comp measurable_fst
  refine measurable_to_countable' ?_
  rintro ⟨n, marks⟩
  have hpreimage :
      manyServerMarkedFreshHorizonSample time ⁻¹' ({⟨n, marks⟩} : Set _) =
        (count ⁻¹' ({n} : Set ℕ)) ∩
          ⋂ i : Fin n, {value : (ℕ → ℝ) × (ℕ → Bool) | value.2 i = marks i} := by
    ext value
    simp [manyServerMarkedFreshHorizonSample, count]
    intro hcountValue
    subst n
    constructor
    · intro hvalue i
      exact congr_fun (eq_of_heq hvalue) i
    · intro hvalue
      exact heq_of_eq (funext hvalue)
  rw [hpreimage]
  apply (hcount (measurableSet_singleton _)).inter
  apply MeasurableSet.iInter
  intro i
  exact measurableSet_eq.preimage
    ((measurable_pi_apply (i : ℕ)).comp measurable_snd)

/-- Fresh-driver arrival counts at deterministic horizons are Borel
measurable. -/
theorem measurable_manyServerMarkedFreshArrivalCount (time : ℝ) :
    Measurable (manyServerMarkedFreshArrivalCount time) :=
  Measurable.of_discrete.comp (measurable_manyServerMarkedFreshHorizonSample time)

/-- Fresh-driver potential-service counts at deterministic horizons are Borel
measurable. -/
theorem measurable_manyServerMarkedFreshPotentialServiceCount (time : ℝ) :
    Measurable (manyServerMarkedFreshPotentialServiceCount time) :=
  Measurable.of_discrete.comp (measurable_manyServerMarkedFreshHorizonSample time)

/-- A fresh clock/mark driver has the literal finite marked-Poisson law at a
nonnegative deterministic horizon. -/
theorem manyServerMarkedFreshHorizonSample_hasLaw
    (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers : ℕ) (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    {time : ℝ} (htime : 0 ≤ time) :
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    let mean : ℝ≥0 := ⟨rate * time, mul_nonneg
      (le_of_lt (manyServerUniformizationRate_pos trafficIntensity serviceRate
        servers hservers hserviceRate)) htime⟩
    let arrivalProbability := uniformizedBirthProbability trafficIntensity
    HasLaw (manyServerMarkedFreshHorizonSample time)
      (FiniteHorizonMarkedPoisson.jointPMF mean arrivalProbability
        (uniformizedBirthProbability_le_one trafficIntensity)).toMeasure
      ((PoissonProcess.exponentialInterarrivalMeasure rate).prod
        (IIDStream.measure
          (manyServerUniformizationArrivalMark trafficIntensity).toMeasure)) := by
  dsimp only
  let initial : PMF ℕ := PMF.pure 0
  let rate : ℝ := manyServerUniformizationRate
    (trafficIntensity : ℝ) serviceRate servers
  let mean : ℝ≥0 := ⟨rate * time, mul_nonneg
    (le_of_lt (manyServerUniformizationRate_pos trafficIntensity serviceRate
      servers hservers hserviceRate)) htime⟩
  let arrivalProbability : ℝ≥0 := uniformizedBirthProbability trafficIntensity
  let arrivalProbability_le_one : arrivalProbability ≤ 1 :=
    uniformizedBirthProbability_le_one trafficIntensity
  let markLaw : Measure Bool :=
    (manyServerUniformizationArrivalMark trafficIntensity).toMeasure
  let trajectory : Measure (ℕ → ℕ × Bool) := stationaryTrajMeasure
    (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
    (manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers)
  let gaps : Measure (ℕ → ℝ) :=
    PoissonProcess.exponentialInterarrivalMeasure rate
  let source : Measure ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := trajectory.prod gaps
  let drivers : ((ℕ → ℕ × Bool) × (ℕ → ℝ)) →
      (ℕ → ℝ) × (ℕ → Bool) := manyServerMarkedCanonicalDriverFactors
  let originalSample : ((ℕ → ℕ × Bool) × (ℕ → ℝ)) →
      FiniteHorizonMarkedPoisson.Sample :=
    manyServerMarkedCanonicalHorizonSample time
  let freshSample : ((ℕ → ℝ) × (ℕ → Bool)) →
      FiniteHorizonMarkedPoisson.Sample := manyServerMarkedFreshHorizonSample time
  have hrate : 0 < rate := by
    exact manyServerUniformizationRate_pos trafficIntensity serviceRate
      servers hservers hserviceRate
  letI : IsProbabilityMeasure initial.toMeasure := by infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsProbabilityMeasure gaps :=
    PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure markLaw := by
    dsimp [markLaw]
    infer_instance
  letI : IsProbabilityMeasure (IIDStream.measure markLaw) := by
    dsimp [IIDStream.measure]
    infer_instance
  have hdrivers : HasLaw drivers (gaps.prod (IIDStream.measure markLaw)) source := by
    simpa [drivers, source, trajectory, gaps, markLaw, rate] using
      (manyServerMarkedCanonicalDriverFactors_hasLaw
        (initial := initial) trafficIntensity serviceRate servers hservers hserviceRate)
  have horiginal : HasLaw originalSample
      (FiniteHorizonMarkedPoisson.jointPMF mean arrivalProbability
        arrivalProbability_le_one).toMeasure source := by
    simpa [originalSample, source, trajectory, gaps, rate, mean,
      arrivalProbability, arrivalProbability_le_one] using
      (stationaryManyServerMarkedCanonicalHorizonSample_hasLaw
        (initial := initial) trafficIntensity serviceRate servers hservers hserviceRate htime)
  have hcomposition : originalSample = freshSample ∘ drivers := by
    funext value
    rfl
  refine ⟨(measurable_manyServerMarkedFreshHorizonSample time).aemeasurable, ?_⟩
  calc
    Measure.map freshSample (gaps.prod (IIDStream.measure markLaw)) =
        Measure.map freshSample (Measure.map drivers source) := by
          rw [hdrivers.map_eq]
    _ = Measure.map (freshSample ∘ drivers) source := by
          exact Measure.map_map
            (measurable_manyServerMarkedFreshHorizonSample time)
            measurable_manyServerMarkedCanonicalDriverFactors
    _ = Measure.map originalSample source := by rw [hcomposition]
    _ = (FiniteHorizonMarkedPoisson.jointPMF mean arrivalProbability
          arrivalProbability_le_one).toMeasure := horiginal.map_eq

/-- A fresh marked horizon sample and the unused IID mark suffix have their
literal product law.  This retains the suffix explicitly, rather than only
asserting the one-horizon thinning marginal. -/
theorem manyServerMarkedFreshHorizonSample_tail_hasLaw
    (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers : ℕ) (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    {time : ℝ} (htime : 0 ≤ time) :
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    let mean : ℝ≥0 := ⟨rate * time, mul_nonneg
      (le_of_lt (manyServerUniformizationRate_pos trafficIntensity serviceRate
        servers hservers hserviceRate)) htime⟩
    let arrivalProbability := uniformizedBirthProbability trafficIntensity
    let markLaw := (manyServerUniformizationArrivalMark trafficIntensity).toMeasure
    HasLaw (fun value : (ℕ → ℝ) × (ℕ → Bool) =>
      (manyServerMarkedFreshHorizonSample time value,
        IIDStream.externalIndexTail (α := Bool)
          (fun gaps : ℕ → ℝ => PoissonProcess.canonicalRenewalCount time gaps)
          value))
      (Measure.prod
        (FiniteHorizonMarkedPoisson.jointPMF mean arrivalProbability
          (uniformizedBirthProbability_le_one trafficIntensity)).toMeasure
        (IIDStream.measure markLaw))
      ((PoissonProcess.exponentialInterarrivalMeasure rate).prod
        (IIDStream.measure markLaw)) := by
  dsimp only
  let rate : ℝ := manyServerUniformizationRate
    (trafficIntensity : ℝ) serviceRate servers
  let mean : ℝ≥0 := ⟨rate * time, mul_nonneg
    (le_of_lt (manyServerUniformizationRate_pos trafficIntensity serviceRate
      servers hservers hserviceRate)) htime⟩
  let arrivalProbability : ℝ≥0 := uniformizedBirthProbability trafficIntensity
  let arrivalProbability_le_one : arrivalProbability ≤ 1 :=
    uniformizedBirthProbability_le_one trafficIntensity
  let markLaw : Measure Bool :=
    (manyServerUniformizationArrivalMark trafficIntensity).toMeasure
  let gaps : Measure (ℕ → ℝ) :=
    PoissonProcess.exponentialInterarrivalMeasure rate
  let index : (ℕ → ℝ) → ℕ :=
    fun clock => PoissonProcess.canonicalRenewalCount time clock
  have hrate : 0 < rate := by
    exact manyServerUniformizationRate_pos trafficIntensity serviceRate
      servers hservers hserviceRate
  letI : IsProbabilityMeasure gaps :=
    PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure markLaw := by
    dsimp [markLaw]
    infer_instance
  letI : IsProbabilityMeasure (IIDStream.measure markLaw) := by
    dsimp [IIDStream.measure]
    infer_instance
  have hsample : HasLaw (manyServerMarkedFreshHorizonSample time)
      (FiniteHorizonMarkedPoisson.jointPMF mean arrivalProbability
        arrivalProbability_le_one).toMeasure
      (gaps.prod (IIDStream.measure markLaw)) := by
    simpa [gaps, rate, mean, arrivalProbability, arrivalProbability_le_one,
      markLaw] using
      (manyServerMarkedFreshHorizonSample_hasLaw
        trafficIntensity serviceRate servers hservers hserviceRate htime)
  have htail : HasLaw (IIDStream.externalIndexTail (α := Bool) index)
      (IIDStream.measure markLaw) (gaps.prod (IIDStream.measure markLaw)) := by
    simpa [gaps, index] using
      (IIDStream.externalIndexTail_hasLaw gaps markLaw index
        (PoissonProcess.measurable_canonicalRenewalCount time))
  have hindep : IndepFun (manyServerMarkedFreshHorizonSample time)
      (IIDStream.externalIndexTail (α := Bool) index)
      (gaps.prod (IIDStream.measure markLaw)) := by
    simpa [gaps, index] using
      (indepFun_manyServerMarkedFreshHorizonSample_externalIndexTail
        hrate markLaw time)
  refine ⟨((measurable_manyServerMarkedFreshHorizonSample time).prodMk
    (IIDStream.measurable_externalIndexTail (α := Bool) index
      (PoissonProcess.measurable_canonicalRenewalCount time))).aemeasurable, ?_⟩
  calc
    Measure.map (fun value : (ℕ → ℝ) × (ℕ → Bool) =>
        (manyServerMarkedFreshHorizonSample time value,
          IIDStream.externalIndexTail (α := Bool) index value))
        (gaps.prod (IIDStream.measure markLaw)) =
        (Measure.map (manyServerMarkedFreshHorizonSample time)
          (gaps.prod (IIDStream.measure markLaw))).prod
          (Measure.map (IIDStream.externalIndexTail (α := Bool) index)
            (gaps.prod (IIDStream.measure markLaw))) := by
          exact (indepFun_iff_map_prod_eq_prod_map_map
            (measurable_manyServerMarkedFreshHorizonSample time).aemeasurable
            (IIDStream.measurable_externalIndexTail (α := Bool) index
              (PoissonProcess.measurable_canonicalRenewalCount time)).aemeasurable).mp
            hindep
    _ = (FiniteHorizonMarkedPoisson.jointPMF mean arrivalProbability
          arrivalProbability_le_one).toMeasure.prod (IIDStream.measure markLaw) := by
          rw [hsample.map_eq, htail.map_eq]

/-- The past marked sample at a deterministic clock time is independent of
the complete fresh clock/mark driver thereafter.  This is the finite marked
restart law from which successive physical-interval laws can be constructed. -/
theorem manyServerMarkedFreshHorizonSample_futureDriver_hasLaw
    (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers : ℕ) (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    {time : ℝ} (htime : 0 ≤ time) :
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    let mean : ℝ≥0 := ⟨rate * time, mul_nonneg
      (le_of_lt (manyServerUniformizationRate_pos trafficIntensity serviceRate
        servers hservers hserviceRate)) htime⟩
    let arrivalProbability := uniformizedBirthProbability trafficIntensity
    let markLaw := (manyServerUniformizationArrivalMark trafficIntensity).toMeasure
    HasLaw (fun value : (ℕ → ℝ) × (ℕ → Bool) =>
      (manyServerMarkedFreshHorizonSample time value,
        (PoissonProcess.residualTail time value.1,
          IIDStream.externalIndexTail (α := Bool)
            (fun gaps : ℕ → ℝ => PoissonProcess.canonicalRenewalCount time gaps)
            value)))
      (Measure.prod
        (FiniteHorizonMarkedPoisson.jointPMF mean arrivalProbability
          (uniformizedBirthProbability_le_one trafficIntensity)).toMeasure
        ((PoissonProcess.exponentialInterarrivalMeasure rate).prod
          (IIDStream.measure markLaw)))
      ((PoissonProcess.exponentialInterarrivalMeasure rate).prod
        (IIDStream.measure markLaw)) := by
  dsimp only
  let rate : ℝ := manyServerUniformizationRate
    (trafficIntensity : ℝ) serviceRate servers
  let mean : ℝ≥0 := ⟨rate * time, mul_nonneg
    (le_of_lt (manyServerUniformizationRate_pos trafficIntensity serviceRate
      servers hservers hserviceRate)) htime⟩
  let arrivalProbability : ℝ≥0 := uniformizedBirthProbability trafficIntensity
  let arrivalProbability_le_one : arrivalProbability ≤ 1 :=
    uniformizedBirthProbability_le_one trafficIntensity
  let markLaw : Measure Bool :=
    (manyServerUniformizationArrivalMark trafficIntensity).toMeasure
  let gaps : Measure (ℕ → ℝ) :=
    PoissonProcess.exponentialInterarrivalMeasure rate
  let marks : Measure (ℕ → Bool) := IIDStream.measure markLaw
  let history : (ℕ → ℝ) → ℕ × (ℕ → ℝ) :=
    PoissonProcess.canonicalRenewalPastHistory time
  let historyMeasure : Measure (ℕ × (ℕ → ℝ)) := Measure.map history gaps
  let markedHistory : Measure ((ℕ → Bool) × (ℕ × (ℕ → ℝ))) :=
    marks.prod historyMeasure
  let originalPair : ((ℕ → ℝ) × (ℕ → Bool)) →
      FiniteHorizonMarkedPoisson.Sample × (ℕ → Bool) :=
    fun value =>
      (manyServerMarkedFreshHorizonSample time value,
        IIDStream.externalIndexTail (α := Bool)
          (fun clock : ℕ → ℝ => PoissonProcess.canonicalRenewalCount time clock)
          value)
  let historySample : ((ℕ → Bool) × (ℕ × (ℕ → ℝ))) →
      FiniteHorizonMarkedPoisson.Sample :=
    fun value => ⟨value.2.1, fun i => value.1 i⟩
  let historyTail : ((ℕ → Bool) × (ℕ × (ℕ → ℝ))) → ℕ → Bool :=
    fun value => IIDStream.externalIndexTail (α := Bool) Prod.fst
      (value.2, value.1)
  let historyPair : ((ℕ → Bool) × (ℕ × (ℕ → ℝ))) →
      FiniteHorizonMarkedPoisson.Sample × (ℕ → Bool) :=
    fun value => (historySample value, historyTail value)
  let pastTransform : (ℕ → Bool) × (ℕ → ℝ) →
      (ℕ → Bool) × (ℕ × (ℕ → ℝ)) :=
    fun value => (value.1, history value.2)
  let fullTransform : (ℕ → Bool) × (ℕ → ℝ) →
      ((ℕ → Bool) × (ℕ × (ℕ → ℝ))) × (ℕ → ℝ) :=
    fun value => ((value.1, history value.2),
      PoissonProcess.residualTail time value.2)
  let reorder : (FiniteHorizonMarkedPoisson.Sample × (ℕ → Bool)) × (ℕ → ℝ) →
      FiniteHorizonMarkedPoisson.Sample × ((ℕ → ℝ) × (ℕ → Bool)) :=
    fun value => (value.1.1, (value.2, value.1.2))
  let synthetic : ((ℕ → Bool) × (ℕ × (ℕ → ℝ))) × (ℕ → ℝ) →
      FiniteHorizonMarkedPoisson.Sample × ((ℕ → ℝ) × (ℕ → Bool)) :=
    fun value => (historySample value.1, (value.2, historyTail value.1))
  have hrate : 0 < rate := by
    exact manyServerUniformizationRate_pos trafficIntensity serviceRate
      servers hservers hserviceRate
  letI : IsProbabilityMeasure gaps :=
    PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure markLaw := by
    dsimp [markLaw]
    infer_instance
  letI : IsProbabilityMeasure marks := by
    dsimp [marks, IIDStream.measure]
    infer_instance
  letI : IsProbabilityMeasure historyMeasure :=
    Measure.isProbabilityMeasure_map
      (PoissonProcess.measurable_canonicalRenewalPastHistory time).aemeasurable
  letI : IsProbabilityMeasure markedHistory := by
    dsimp [markedHistory]
    infer_instance
  have hsampleTail : HasLaw originalPair
      (Measure.prod
        (FiniteHorizonMarkedPoisson.jointPMF mean arrivalProbability
          arrivalProbability_le_one).toMeasure marks) (gaps.prod marks) := by
    simpa [originalPair, gaps, marks, rate, mean, arrivalProbability,
      arrivalProbability_le_one, markLaw] using
      (manyServerMarkedFreshHorizonSample_tail_hasLaw
        trafficIntensity serviceRate servers hservers hserviceRate htime)
  have hhistory : Measurable history := by
    simpa [history] using
      PoissonProcess.measurable_canonicalRenewalPastHistory time
  have hpastTransform : Measurable pastTransform := by
    exact measurable_fst.prodMk (hhistory.comp measurable_snd)
  have hfullTransform : Measurable fullTransform := by
    exact (measurable_fst.prodMk (hhistory.comp measurable_snd)).prodMk
      ((PoissonProcess.measurable_residualTail time).comp measurable_snd)
  have hhistorySample : Measurable historySample := by
    classical
    refine measurable_to_countable' ?_
    rintro ⟨n, sampleMarks⟩
    have hpreimage : historySample ⁻¹' ({⟨n, sampleMarks⟩} : Set _) =
        {value : (ℕ → Bool) × (ℕ × (ℕ → ℝ)) | value.2.1 = n} ∩
          ⋂ i : Fin n, {value : (ℕ → Bool) × (ℕ × (ℕ → ℝ)) |
            value.1 i = sampleMarks i} := by
      ext value
      simp [historySample]
      intro hcount
      subst n
      constructor
      · intro hvalue i
        exact congr_fun (eq_of_heq hvalue) i
      · intro hvalue
        exact heq_of_eq (funext hvalue)
    rw [hpreimage]
    apply ((measurable_fst.comp measurable_snd) (measurableSet_singleton _)).inter
    apply MeasurableSet.iInter
    intro i
    exact measurableSet_eq.preimage
      ((measurable_pi_apply (i : ℕ)).comp measurable_fst)
  have hhistoryTail : Measurable historyTail := by
    simpa [historyTail] using
      (IIDStream.measurable_externalIndexTail (α := Bool) Prod.fst measurable_fst).comp
        measurable_swap
  have hhistoryPair : Measurable historyPair :=
    hhistorySample.prodMk hhistoryTail
  have hsynthetic : Measurable synthetic := by
    exact (hhistorySample.comp measurable_fst).prodMk
      ((measurable_snd.prodMk (hhistoryTail.comp measurable_fst)))
  have horiginalPair : Measurable originalPair := by
    exact (measurable_manyServerMarkedFreshHorizonSample time).prodMk
      (IIDStream.measurable_externalIndexTail (α := Bool)
        (fun clock : ℕ → ℝ => PoissonProcess.canonicalRenewalCount time clock)
        (PoissonProcess.measurable_canonicalRenewalCount time))
  have hpast : Measure.map pastTransform (marks.prod gaps) = markedHistory := by
    change Measure.map (Prod.map id history) (marks.prod gaps) =
      marks.prod (Measure.map history gaps)
    calc
      Measure.map (Prod.map id history) (marks.prod gaps) =
          (Measure.map id marks).prod (Measure.map history gaps) :=
        (Measure.map_prod_map marks gaps measurable_id hhistory).symm
      _ = marks.prod (Measure.map history gaps) := by rw [Measure.map_id]
  have hpairHistory : Measure.map historyPair markedHistory =
      Measure.prod (FiniteHorizonMarkedPoisson.jointPMF mean arrivalProbability
        arrivalProbability_le_one).toMeasure marks := by
    calc
      Measure.map historyPair markedHistory =
          Measure.map historyPair (Measure.map pastTransform (marks.prod gaps)) := by
            rw [hpast]
      _ = Measure.map (historyPair ∘ pastTransform) (marks.prod gaps) := by
            rw [Measure.map_map hhistoryPair hpastTransform]
      _ = Measure.map (originalPair ∘ Prod.swap) (marks.prod gaps) := by
            rfl
      _ = Measure.map originalPair (Measure.map Prod.swap (marks.prod gaps)) := by
            exact (Measure.map_map horiginalPair measurable_swap).symm
      _ = Measure.map originalPair (gaps.prod marks) := by
            rw [Measure.prod_swap]
      _ = Measure.prod (FiniteHorizonMarkedPoisson.jointPMF mean arrivalProbability
            arrivalProbability_le_one).toMeasure marks := hsampleTail.map_eq
  have hfull : Measure.map fullTransform (marks.prod gaps) =
      markedHistory.prod gaps := by
    simpa [fullTransform, markedHistory, historyMeasure, history, marks, gaps] using
      (PoissonProcess.map_external_canonicalRenewalPastHistory_residualTail
        marks hrate htime)
  have hpairId : Measurable
      (Prod.map historyPair (id : (ℕ → ℝ) → (ℕ → ℝ))) :=
    hhistoryPair.prodMap measurable_id
  have hreorder : Measurable reorder := by
    exact (measurable_fst.comp measurable_fst).prodMk
      (measurable_snd.prodMk (measurable_snd.comp measurable_fst))
  have hsynthetic_eq : synthetic = reorder ∘ Prod.map historyPair id := by
    rfl
  have hreorderLaw : Measure.map reorder
      ((((FiniteHorizonMarkedPoisson.jointPMF mean arrivalProbability
        arrivalProbability_le_one).toMeasure).prod marks).prod gaps) =
      (FiniteHorizonMarkedPoisson.jointPMF mean arrivalProbability
        arrivalProbability_le_one).toMeasure.prod (gaps.prod marks) := by
    let associate : (FiniteHorizonMarkedPoisson.Sample × (ℕ → Bool)) × (ℕ → ℝ) →
        FiniteHorizonMarkedPoisson.Sample × ((ℕ → Bool) × (ℕ → ℝ)) :=
      MeasurableEquiv.prodAssoc
    let swapTail : FiniteHorizonMarkedPoisson.Sample × ((ℕ → Bool) × (ℕ → ℝ)) →
        FiniteHorizonMarkedPoisson.Sample × ((ℕ → ℝ) × (ℕ → Bool)) :=
      Prod.map id Prod.swap
    have hassociate : Measurable associate := MeasurableEquiv.prodAssoc.measurable
    have hswapTail : Measurable swapTail := measurable_id.prodMap measurable_swap
    calc
      Measure.map reorder
          ((((FiniteHorizonMarkedPoisson.jointPMF mean arrivalProbability
            arrivalProbability_le_one).toMeasure).prod marks).prod gaps) =
          Measure.map swapTail (Measure.map associate
            ((((FiniteHorizonMarkedPoisson.jointPMF mean arrivalProbability
              arrivalProbability_le_one).toMeasure).prod marks).prod gaps)) := by
            rw [Measure.map_map hswapTail hassociate]
            rfl
      _ = Measure.map swapTail
          ((FiniteHorizonMarkedPoisson.jointPMF mean arrivalProbability
            arrivalProbability_le_one).toMeasure.prod (marks.prod gaps)) := by
            rw [(measurePreserving_prodAssoc
              (FiniteHorizonMarkedPoisson.jointPMF mean arrivalProbability
                arrivalProbability_le_one).toMeasure marks gaps).map_eq]
      _ = (FiniteHorizonMarkedPoisson.jointPMF mean arrivalProbability
            arrivalProbability_le_one).toMeasure.prod (gaps.prod marks) := by
            rw [show swapTail = Prod.map id Prod.swap by rfl]
            calc
              Measure.map (Prod.map id Prod.swap)
                  ((FiniteHorizonMarkedPoisson.jointPMF mean arrivalProbability
                    arrivalProbability_le_one).toMeasure.prod (marks.prod gaps)) =
                  (Measure.map id
                    (FiniteHorizonMarkedPoisson.jointPMF mean arrivalProbability
                      arrivalProbability_le_one).toMeasure).prod
                    (Measure.map Prod.swap (marks.prod gaps)) :=
                (Measure.map_prod_map _ _ measurable_id measurable_swap).symm
              _ = (FiniteHorizonMarkedPoisson.jointPMF mean arrivalProbability
                    arrivalProbability_le_one).toMeasure.prod (gaps.prod marks) := by
                rw [Measure.map_id, Measure.prod_swap]
  have horiginalTriple : Measurable (fun value : (ℕ → ℝ) × (ℕ → Bool) =>
      (manyServerMarkedFreshHorizonSample time value,
        (PoissonProcess.residualTail time value.1,
          IIDStream.externalIndexTail (α := Bool)
            (fun clock : ℕ → ℝ => PoissonProcess.canonicalRenewalCount time clock)
            value))) := by
    apply (measurable_manyServerMarkedFreshHorizonSample time).prodMk
    exact ((PoissonProcess.measurable_residualTail time).comp measurable_fst).prodMk
      (IIDStream.measurable_externalIndexTail (α := Bool)
        (fun clock : ℕ → ℝ => PoissonProcess.canonicalRenewalCount time clock)
        (PoissonProcess.measurable_canonicalRenewalCount time))
  refine ⟨horiginalTriple.aemeasurable, ?_⟩
  calc
    Measure.map (fun value : (ℕ → ℝ) × (ℕ → Bool) =>
        (manyServerMarkedFreshHorizonSample time value,
          (PoissonProcess.residualTail time value.1,
            IIDStream.externalIndexTail (α := Bool)
              (fun clock : ℕ → ℝ => PoissonProcess.canonicalRenewalCount time clock)
              value))) (gaps.prod marks) =
        Measure.map (fun value : (ℕ → ℝ) × (ℕ → Bool) =>
          (manyServerMarkedFreshHorizonSample time value,
            (PoissonProcess.residualTail time value.1,
              IIDStream.externalIndexTail (α := Bool)
                (fun clock : ℕ → ℝ => PoissonProcess.canonicalRenewalCount time clock)
                value))) (Measure.map Prod.swap (marks.prod gaps)) := by
          rw [Measure.prod_swap]
    _ = Measure.map (synthetic ∘ fullTransform) (marks.prod gaps) := by
          rw [Measure.map_map horiginalTriple measurable_swap]
          rfl
    _ = Measure.map synthetic (Measure.map fullTransform (marks.prod gaps)) := by
          rw [Measure.map_map hsynthetic hfullTransform]
    _ = Measure.map synthetic (markedHistory.prod gaps) := by rw [hfull]
    _ = Measure.map reorder
        (Measure.map (Prod.map historyPair id) (markedHistory.prod gaps)) := by
          rw [Measure.map_map hreorder hpairId, hsynthetic_eq]
    _ = Measure.map reorder ((Measure.map historyPair markedHistory).prod gaps) := by
          congr 1
          calc
            Measure.map (Prod.map historyPair id) (markedHistory.prod gaps) =
                (Measure.map historyPair markedHistory).prod (Measure.map id gaps) :=
              (Measure.map_prod_map markedHistory gaps hhistoryPair measurable_id).symm
            _ = (Measure.map historyPair markedHistory).prod gaps := by
              rw [Measure.map_id]
    _ = Measure.map reorder
        ((((FiniteHorizonMarkedPoisson.jointPMF mean arrivalProbability
          arrivalProbability_le_one).toMeasure).prod marks).prod gaps) := by
          rw [hpairHistory]
    _ = (FiniteHorizonMarkedPoisson.jointPMF mean arrivalProbability
          arrivalProbability_le_one).toMeasure.prod (gaps.prod marks) := hreorderLaw

/-- The residual clock and the unused mark suffix of a fresh marked driver. -/
def manyServerMarkedFreshFutureDriver (time : ℝ) :
    ((ℕ → ℝ) × (ℕ → Bool)) → (ℕ → ℝ) × (ℕ → Bool) :=
  fun value =>
    (PoissonProcess.residualTail time value.1,
      IIDStream.externalIndexTail (α := Bool)
        (fun gaps : ℕ → ℝ => PoissonProcess.canonicalRenewalCount time gaps)
        value)

/-- The fresh residual clock/mark driver is Borel measurable. -/
theorem measurable_manyServerMarkedFreshFutureDriver (time : ℝ) :
    Measurable (manyServerMarkedFreshFutureDriver time) := by
  exact ((PoissonProcess.measurable_residualTail time).comp measurable_fst).prodMk
    (IIDStream.measurable_externalIndexTail (α := Bool)
      (fun gaps : ℕ → ℝ => PoissonProcess.canonicalRenewalCount time gaps)
      (PoissonProcess.measurable_canonicalRenewalCount time))

/-- Restarting a fresh marked Poisson driver first at s and then after a
further nonnegative duration h agrees almost surely with restarting once at
s + h.  The clock cocycle and the corresponding addition law for the
consumed IID-mark indices are both explicit. -/
theorem ae_manyServerMarkedFreshFutureDriver_add_eq_comp
    {rate s h : ℝ} (hrate : 0 < rate) (hh : 0 ≤ h)
    (markLaw : Measure Bool) [IsProbabilityMeasure markLaw] :
    ∀ᵐ value ∂(PoissonProcess.exponentialInterarrivalMeasure rate).prod
        (IIDStream.measure markLaw),
      manyServerMarkedFreshFutureDriver (s + h) value =
        manyServerMarkedFreshFutureDriver h
          (manyServerMarkedFreshFutureDriver s value) := by
  let gaps := PoissonProcess.exponentialInterarrivalMeasure rate
  let marks := IIDStream.measure markLaw
  letI : IsProbabilityMeasure marks := by
    dsimp [marks, IIDStream.measure]
    infer_instance
  have hclock : ∀ᵐ gap ∂gaps,
      PoissonProcess.residualTail (s + h) gap =
        PoissonProcess.residualTail h (PoissonProcess.residualTail s gap) ∧
      PoissonProcess.canonicalRenewalCount (s + h) gap =
        PoissonProcess.canonicalRenewalCount s gap +
          PoissonProcess.canonicalRenewalCount h
            (PoissonProcess.residualTail s gap) := by
    filter_upwards [PoissonProcess.ae_residualTail_add_eq_residualTail_comp hrate hh,
      PoissonProcess.ae_canonicalRenewalCount_add_eq_residualTailCount hrate s h hh]
      with gap htail hcount
    exact ⟨htail, hcount⟩
  have hclock' : ∀ᵐ value ∂gaps.prod marks,
      PoissonProcess.residualTail (s + h) value.1 =
        PoissonProcess.residualTail h (PoissonProcess.residualTail s value.1) ∧
      PoissonProcess.canonicalRenewalCount (s + h) value.1 =
        PoissonProcess.canonicalRenewalCount s value.1 +
          PoissonProcess.canonicalRenewalCount h
            (PoissonProcess.residualTail s value.1) := by
    refine ae_of_ae_map (μ := gaps.prod marks) (f := Prod.fst)
      (p := fun gap : ℕ → ℝ =>
        PoissonProcess.residualTail (s + h) gap =
          PoissonProcess.residualTail h (PoissonProcess.residualTail s gap) ∧
        PoissonProcess.canonicalRenewalCount (s + h) gap =
          PoissonProcess.canonicalRenewalCount s gap +
            PoissonProcess.canonicalRenewalCount h
              (PoissonProcess.residualTail s gap))
      measurable_fst.aemeasurable ?_
    simpa [gaps, marks] using hclock
  filter_upwards [hclock'] with value hvalue
  rcases hvalue with ⟨htail, hcount⟩
  apply Prod.ext
  · exact htail
  · funext i
    simp only [manyServerMarkedFreshFutureDriver, IIDStream.externalIndexTail,
      IIDStream.coordinate]
    simpa [Nat.add_assoc] using
      congrArg (fun index : ℕ => value.2 (index + i)) hcount

/-- The fresh driver extracted from the canonical marked construction has the
same restart cocycle.  This identifies a successive fresh-block construction
with the literal deterministic-time future driver of the original path. -/
theorem ae_manyServerMarkedCanonicalFutureDriver_add_eq_freshFutureDriver_comp
    {initial : PMF ℕ} (trafficIntensity : ℝ≥0) (servers : ℕ)
    (hservers : 0 < servers) {rate s h : ℝ} (hrate : 0 < rate) (hh : 0 ≤ h) :
    let trajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel trafficIntensity servers hservers)
    let source := trajectory.prod (PoissonProcess.exponentialInterarrivalMeasure rate)
    ∀ᵐ value ∂source,
      manyServerMarkedCanonicalFutureDriver (s + h) value =
        manyServerMarkedFreshFutureDriver h
          (manyServerMarkedCanonicalFutureDriver s value) := by
  dsimp only
  let trajectory := stationaryTrajMeasure
    (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
    (manyServerMarkedStateUniformizationMeasureKernel trafficIntensity servers hservers)
  let gaps := PoissonProcess.exponentialInterarrivalMeasure rate
  let source := trajectory.prod gaps
  letI : IsProbabilityMeasure initial.toMeasure := by infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsProbabilityMeasure gaps :=
    PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  have hclock : ∀ᵐ gap ∂gaps,
      PoissonProcess.residualTail (s + h) gap =
        PoissonProcess.residualTail h (PoissonProcess.residualTail s gap) ∧
      PoissonProcess.canonicalRenewalCount (s + h) gap =
        PoissonProcess.canonicalRenewalCount s gap +
          PoissonProcess.canonicalRenewalCount h
            (PoissonProcess.residualTail s gap) := by
    filter_upwards [PoissonProcess.ae_residualTail_add_eq_residualTail_comp hrate hh,
      PoissonProcess.ae_canonicalRenewalCount_add_eq_residualTailCount hrate s h hh]
      with gap htail hcount
    exact ⟨htail, hcount⟩
  have hclock' : ∀ᵐ value ∂source,
      PoissonProcess.residualTail (s + h) value.2 =
        PoissonProcess.residualTail h (PoissonProcess.residualTail s value.2) ∧
      PoissonProcess.canonicalRenewalCount (s + h) value.2 =
        PoissonProcess.canonicalRenewalCount s value.2 +
          PoissonProcess.canonicalRenewalCount h
            (PoissonProcess.residualTail s value.2) := by
    refine ae_of_ae_map (μ := source) (f := Prod.snd)
      (p := fun gap : ℕ → ℝ =>
        PoissonProcess.residualTail (s + h) gap =
          PoissonProcess.residualTail h (PoissonProcess.residualTail s gap) ∧
        PoissonProcess.canonicalRenewalCount (s + h) gap =
          PoissonProcess.canonicalRenewalCount s gap +
            PoissonProcess.canonicalRenewalCount h
              (PoissonProcess.residualTail s gap))
      measurable_snd.aemeasurable ?_
    have hmap : Measure.map Prod.snd source = gaps := by
      exact (measurePreserving_snd (μ := trajectory) (ν := gaps)).map_eq
    rw [hmap]
    exact hclock
  filter_upwards [hclock'] with value hvalue
  rcases hvalue with ⟨htail, hcount⟩
  apply Prod.ext
  · exact htail
  · funext i
    simp only [manyServerMarkedCanonicalFutureDriver,
      manyServerMarkedFreshFutureDriver, IIDStream.externalIndexTail,
      IIDStream.coordinate]
    simpa [Nat.add_assoc] using
      congrArg (fun index : ℕ =>
        (manyServerMarkedStateArrivalMarkPath value.1) (index + i)) hcount

/-- The literal marked sample in a physical interval, formed from the fresh
clock and mark driver at its left endpoint. -/
def manyServerMarkedCanonicalIntervalSample (start duration : ℝ) :
    ((ℕ → ℕ × Bool) × (ℕ → ℝ)) → FiniteHorizonMarkedPoisson.Sample :=
  manyServerMarkedFreshHorizonSample duration ∘
    manyServerMarkedCanonicalFutureDriver start

/-- On the canonical marked construction, the complete marked sample through
`time` is independent of the actual fresh driver after `time`. -/
theorem manyServerMarkedCanonicalHorizonSample_futureDriver_hasLaw
    {initial : PMF ℕ} (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers : ℕ) (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    {time : ℝ} (htime : 0 ≤ time) :
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    let mean : ℝ≥0 := ⟨rate * time, mul_nonneg
      (le_of_lt (manyServerUniformizationRate_pos trafficIntensity serviceRate
        servers hservers hserviceRate)) htime⟩
    let arrivalProbability := uniformizedBirthProbability trafficIntensity
    let markLaw := (manyServerUniformizationArrivalMark trafficIntensity).toMeasure
    HasLaw (fun value : ((ℕ → ℕ × Bool) × (ℕ → ℝ)) =>
      (manyServerMarkedCanonicalHorizonSample time value,
        manyServerMarkedCanonicalFutureDriver time value))
      (Measure.prod
        (FiniteHorizonMarkedPoisson.jointPMF mean arrivalProbability
          (uniformizedBirthProbability_le_one trafficIntensity)).toMeasure
        ((PoissonProcess.exponentialInterarrivalMeasure rate).prod
          (IIDStream.measure markLaw)))
      ((stationaryTrajMeasure
        (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
        (manyServerMarkedStateUniformizationMeasureKernel
          trafficIntensity servers hservers)).prod
        (PoissonProcess.exponentialInterarrivalMeasure rate)) := by
  dsimp only
  let rate : ℝ := manyServerUniformizationRate
    (trafficIntensity : ℝ) serviceRate servers
  let mean : ℝ≥0 := ⟨rate * time, mul_nonneg
    (le_of_lt (manyServerUniformizationRate_pos trafficIntensity serviceRate
      servers hservers hserviceRate)) htime⟩
  let arrivalProbability : ℝ≥0 := uniformizedBirthProbability trafficIntensity
  let arrivalProbability_le_one : arrivalProbability ≤ 1 :=
    uniformizedBirthProbability_le_one trafficIntensity
  let markLaw : Measure Bool :=
    (manyServerUniformizationArrivalMark trafficIntensity).toMeasure
  let trajectory : Measure (ℕ → ℕ × Bool) := stationaryTrajMeasure
    (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
    (manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers)
  let gaps : Measure (ℕ → ℝ) :=
    PoissonProcess.exponentialInterarrivalMeasure rate
  let source : Measure ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := trajectory.prod gaps
  let drivers : ((ℕ → ℕ × Bool) × (ℕ → ℝ)) →
      (ℕ → ℝ) × (ℕ → Bool) := manyServerMarkedCanonicalDriverFactors
  have hrate : 0 < rate := by
    exact manyServerUniformizationRate_pos trafficIntensity serviceRate
      servers hservers hserviceRate
  letI : IsProbabilityMeasure initial.toMeasure := by infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsProbabilityMeasure gaps :=
    PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure markLaw := by
    dsimp [markLaw]
    infer_instance
  letI : IsProbabilityMeasure (IIDStream.measure markLaw) := by
    dsimp [IIDStream.measure]
    infer_instance
  have hdrivers : HasLaw drivers (gaps.prod (IIDStream.measure markLaw)) source := by
    simpa [drivers, source, trajectory, gaps, markLaw, rate] using
      (manyServerMarkedCanonicalDriverFactors_hasLaw
        (initial := initial) trafficIntensity serviceRate servers hservers hserviceRate)
  have hfresh : HasLaw (fun value : (ℕ → ℝ) × (ℕ → Bool) =>
      (manyServerMarkedFreshHorizonSample time value,
        manyServerMarkedFreshFutureDriver time value))
      (Measure.prod
        (FiniteHorizonMarkedPoisson.jointPMF mean arrivalProbability
          arrivalProbability_le_one).toMeasure
        (gaps.prod (IIDStream.measure markLaw)))
      (gaps.prod (IIDStream.measure markLaw)) := by
    simpa [manyServerMarkedFreshFutureDriver, gaps, rate, mean,
      arrivalProbability, arrivalProbability_le_one, markLaw] using
      (manyServerMarkedFreshHorizonSample_futureDriver_hasLaw
        trafficIntensity serviceRate servers hservers hserviceRate htime)
  have hresult := hfresh.comp hdrivers
  simpa [manyServerMarkedCanonicalHorizonSample,
    manyServerMarkedCanonicalFutureDriver, manyServerMarkedFreshFutureDriver,
    drivers, Function.comp_def, source, trajectory, gaps, rate, mean,
    arrivalProbability, arrivalProbability_le_one, markLaw] using hresult

/-- The marked sample accumulated through `start` and the literal sample in
the following deterministic interval are independent finite marked-Poisson
samples. -/
theorem manyServerMarkedCanonicalHorizon_intervalSample_hasLaw
    {initial : PMF ℕ} (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers : ℕ) (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    {start duration : ℝ} (hstart : 0 ≤ start) (hduration : 0 ≤ duration) :
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    let firstMean : ℝ≥0 := ⟨rate * start, mul_nonneg
      (le_of_lt (manyServerUniformizationRate_pos trafficIntensity serviceRate
        servers hservers hserviceRate)) hstart⟩
    let secondMean : ℝ≥0 := ⟨rate * duration, mul_nonneg
      (le_of_lt (manyServerUniformizationRate_pos trafficIntensity serviceRate
        servers hservers hserviceRate)) hduration⟩
    let arrivalProbability := uniformizedBirthProbability trafficIntensity
    HasLaw (fun value : ((ℕ → ℕ × Bool) × (ℕ → ℝ)) =>
      (manyServerMarkedCanonicalHorizonSample start value,
        manyServerMarkedCanonicalIntervalSample start duration value))
      (Measure.prod
        (FiniteHorizonMarkedPoisson.jointPMF firstMean arrivalProbability
          (uniformizedBirthProbability_le_one trafficIntensity)).toMeasure
        (FiniteHorizonMarkedPoisson.jointPMF secondMean arrivalProbability
          (uniformizedBirthProbability_le_one trafficIntensity)).toMeasure)
      ((stationaryTrajMeasure
        (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
        (manyServerMarkedStateUniformizationMeasureKernel
          trafficIntensity servers hservers)).prod
        (PoissonProcess.exponentialInterarrivalMeasure rate)) := by
  dsimp only
  let rate : ℝ := manyServerUniformizationRate
    (trafficIntensity : ℝ) serviceRate servers
  let firstMean : ℝ≥0 := ⟨rate * start, mul_nonneg
    (le_of_lt (manyServerUniformizationRate_pos trafficIntensity serviceRate
      servers hservers hserviceRate)) hstart⟩
  let secondMean : ℝ≥0 := ⟨rate * duration, mul_nonneg
    (le_of_lt (manyServerUniformizationRate_pos trafficIntensity serviceRate
      servers hservers hserviceRate)) hduration⟩
  let arrivalProbability : ℝ≥0 := uniformizedBirthProbability trafficIntensity
  let arrivalProbability_le_one : arrivalProbability ≤ 1 :=
    uniformizedBirthProbability_le_one trafficIntensity
  let markLaw : Measure Bool :=
    (manyServerUniformizationArrivalMark trafficIntensity).toMeasure
  let trajectory : Measure (ℕ → ℕ × Bool) := stationaryTrajMeasure
    (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
    (manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers)
  let gaps : Measure (ℕ → ℝ) :=
    PoissonProcess.exponentialInterarrivalMeasure rate
  let source : Measure ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := trajectory.prod gaps
  let freshDriver : Measure ((ℕ → ℝ) × (ℕ → Bool)) :=
    gaps.prod (IIDStream.measure markLaw)
  let firstLaw : Measure FiniteHorizonMarkedPoisson.Sample :=
    (FiniteHorizonMarkedPoisson.jointPMF firstMean arrivalProbability
      arrivalProbability_le_one).toMeasure
  let secondLaw : Measure FiniteHorizonMarkedPoisson.Sample :=
    (FiniteHorizonMarkedPoisson.jointPMF secondMean arrivalProbability
      arrivalProbability_le_one).toMeasure
  have hrate : 0 < rate := by
    exact manyServerUniformizationRate_pos trafficIntensity serviceRate
      servers hservers hserviceRate
  letI : IsProbabilityMeasure initial.toMeasure := by infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsProbabilityMeasure gaps :=
    PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure markLaw := by
    dsimp [markLaw]
    infer_instance
  letI : IsProbabilityMeasure (IIDStream.measure markLaw) := by
    dsimp [IIDStream.measure]
    infer_instance
  letI : IsProbabilityMeasure freshDriver := by
    dsimp [freshDriver]
    infer_instance
  letI : IsProbabilityMeasure firstLaw := by
    dsimp [firstLaw]
    infer_instance
  letI : IsProbabilityMeasure secondLaw := by
    dsimp [secondLaw]
    infer_instance
  have hpastFuture : HasLaw (fun value : ((ℕ → ℕ × Bool) × (ℕ → ℝ)) =>
      (manyServerMarkedCanonicalHorizonSample start value,
        manyServerMarkedCanonicalFutureDriver start value))
      (firstLaw.prod freshDriver) source := by
    simpa [firstLaw, freshDriver, source, trajectory, gaps, rate, firstMean,
      arrivalProbability, arrivalProbability_le_one, markLaw] using
      (manyServerMarkedCanonicalHorizonSample_futureDriver_hasLaw
        (initial := initial) trafficIntensity serviceRate servers hservers hserviceRate hstart)
  have hsecond : HasLaw (manyServerMarkedFreshHorizonSample duration)
      secondLaw freshDriver := by
    simpa [secondLaw, freshDriver, gaps, markLaw, rate, secondMean,
      arrivalProbability, arrivalProbability_le_one] using
      (manyServerMarkedFreshHorizonSample_hasLaw
        trafficIntensity serviceRate servers hservers hserviceRate hduration)
  have htransform : HasLaw
      (Prod.map id (manyServerMarkedFreshHorizonSample duration))
      (firstLaw.prod secondLaw) (firstLaw.prod freshDriver) := by
    refine ⟨(measurable_id.prodMap
      (measurable_manyServerMarkedFreshHorizonSample duration)).aemeasurable, ?_⟩
    calc
      Measure.map (Prod.map id (manyServerMarkedFreshHorizonSample duration))
          (firstLaw.prod freshDriver) =
          (Measure.map id firstLaw).prod
            (Measure.map (manyServerMarkedFreshHorizonSample duration) freshDriver) :=
        (Measure.map_prod_map firstLaw freshDriver measurable_id
          (measurable_manyServerMarkedFreshHorizonSample duration)).symm
      _ = firstLaw.prod secondLaw := by rw [Measure.map_id, hsecond.map_eq]
  have hresult := htransform.comp hpastFuture
  simpa [manyServerMarkedCanonicalIntervalSample, Function.comp_def,
    source, trajectory, gaps, rate, firstMean, secondMean, firstLaw, secondLaw,
    freshDriver, arrivalProbability, arrivalProbability_le_one, markLaw] using hresult

/-- The marked sample accumulated through start and the literal marked
samples in the following two deterministic intervals.  This concrete
three-block form is a reusable finite-dimensional restart primitive. -/
def manyServerMarkedCanonicalHorizon_twoIntervalSamples
    (start firstDuration secondDuration : ℝ) :
    ((ℕ → ℕ × Bool) × (ℕ → ℝ)) →
      FiniteHorizonMarkedPoisson.Sample ×
        (FiniteHorizonMarkedPoisson.Sample × FiniteHorizonMarkedPoisson.Sample) :=
  fun value =>
    let driver := manyServerMarkedCanonicalFutureDriver start value
    let futureDriver := manyServerMarkedFreshFutureDriver firstDuration driver
    (manyServerMarkedCanonicalHorizonSample start value,
      (manyServerMarkedFreshHorizonSample firstDuration driver,
        manyServerMarkedFreshHorizonSample secondDuration futureDriver))

/-- Three consecutive deterministic marked-Poisson blocks have the iterated
product law.  The nested form is stable under the standard product-measure
APIs and can be iterated into longer finite partitions. -/
theorem manyServerMarkedCanonicalHorizon_twoIntervalSamples_hasLaw
    {initial : PMF ℕ} (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers : ℕ) (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    {start firstDuration secondDuration : ℝ}
    (hstart : 0 ≤ start) (hfirstDuration : 0 ≤ firstDuration)
    (hsecondDuration : 0 ≤ secondDuration) :
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    let firstMean : ℝ≥0 := ⟨rate * start, mul_nonneg
      (le_of_lt (manyServerUniformizationRate_pos trafficIntensity serviceRate
        servers hservers hserviceRate)) hstart⟩
    let secondMean : ℝ≥0 := ⟨rate * firstDuration, mul_nonneg
      (le_of_lt (manyServerUniformizationRate_pos trafficIntensity serviceRate
        servers hservers hserviceRate)) hfirstDuration⟩
    let thirdMean : ℝ≥0 := ⟨rate * secondDuration, mul_nonneg
      (le_of_lt (manyServerUniformizationRate_pos trafficIntensity serviceRate
        servers hservers hserviceRate)) hsecondDuration⟩
    let arrivalProbability := uniformizedBirthProbability trafficIntensity
    HasLaw
      (manyServerMarkedCanonicalHorizon_twoIntervalSamples
        start firstDuration secondDuration)
      (Measure.prod
        (FiniteHorizonMarkedPoisson.jointPMF firstMean arrivalProbability
          (uniformizedBirthProbability_le_one trafficIntensity)).toMeasure
        (Measure.prod
          (FiniteHorizonMarkedPoisson.jointPMF secondMean arrivalProbability
            (uniformizedBirthProbability_le_one trafficIntensity)).toMeasure
          (FiniteHorizonMarkedPoisson.jointPMF thirdMean arrivalProbability
            (uniformizedBirthProbability_le_one trafficIntensity)).toMeasure))
      ((stationaryTrajMeasure
        (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
        (manyServerMarkedStateUniformizationMeasureKernel
          trafficIntensity servers hservers)).prod
        (PoissonProcess.exponentialInterarrivalMeasure rate)) := by
  dsimp only
  let rate : ℝ := manyServerUniformizationRate
    (trafficIntensity : ℝ) serviceRate servers
  let firstMean : ℝ≥0 := ⟨rate * start, mul_nonneg
    (le_of_lt (manyServerUniformizationRate_pos trafficIntensity serviceRate
      servers hservers hserviceRate)) hstart⟩
  let secondMean : ℝ≥0 := ⟨rate * firstDuration, mul_nonneg
    (le_of_lt (manyServerUniformizationRate_pos trafficIntensity serviceRate
      servers hservers hserviceRate)) hfirstDuration⟩
  let thirdMean : ℝ≥0 := ⟨rate * secondDuration, mul_nonneg
    (le_of_lt (manyServerUniformizationRate_pos trafficIntensity serviceRate
      servers hservers hserviceRate)) hsecondDuration⟩
  let arrivalProbability : ℝ≥0 := uniformizedBirthProbability trafficIntensity
  let arrivalProbability_le_one : arrivalProbability ≤ 1 :=
    uniformizedBirthProbability_le_one trafficIntensity
  let markLaw : Measure Bool :=
    (manyServerUniformizationArrivalMark trafficIntensity).toMeasure
  let trajectory : Measure (ℕ → ℕ × Bool) := stationaryTrajMeasure
    (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
    (manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers)
  let gaps : Measure (ℕ → ℝ) :=
    PoissonProcess.exponentialInterarrivalMeasure rate
  let source : Measure ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := trajectory.prod gaps
  let freshDriver : Measure ((ℕ → ℝ) × (ℕ → Bool)) :=
    gaps.prod (IIDStream.measure markLaw)
  let firstLaw : Measure FiniteHorizonMarkedPoisson.Sample :=
    (FiniteHorizonMarkedPoisson.jointPMF firstMean arrivalProbability
      arrivalProbability_le_one).toMeasure
  let secondLaw : Measure FiniteHorizonMarkedPoisson.Sample :=
    (FiniteHorizonMarkedPoisson.jointPMF secondMean arrivalProbability
      arrivalProbability_le_one).toMeasure
  let thirdLaw : Measure FiniteHorizonMarkedPoisson.Sample :=
    (FiniteHorizonMarkedPoisson.jointPMF thirdMean arrivalProbability
      arrivalProbability_le_one).toMeasure
  have hrate : 0 < rate := by
    exact manyServerUniformizationRate_pos trafficIntensity serviceRate
      servers hservers hserviceRate
  letI : IsProbabilityMeasure initial.toMeasure := by infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsProbabilityMeasure gaps :=
    PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure markLaw := by
    dsimp [markLaw]
    infer_instance
  letI : IsProbabilityMeasure (IIDStream.measure markLaw) := by
    dsimp [IIDStream.measure]
    infer_instance
  letI : IsProbabilityMeasure freshDriver := by
    dsimp [freshDriver]
    infer_instance
  letI : IsProbabilityMeasure firstLaw := by
    dsimp [firstLaw]
    infer_instance
  letI : IsProbabilityMeasure secondLaw := by
    dsimp [secondLaw]
    infer_instance
  letI : IsProbabilityMeasure thirdLaw := by
    dsimp [thirdLaw]
    infer_instance
  have hpastFuture : HasLaw (fun value : ((ℕ → ℕ × Bool) × (ℕ → ℝ)) =>
      (manyServerMarkedCanonicalHorizonSample start value,
        manyServerMarkedCanonicalFutureDriver start value))
      (firstLaw.prod freshDriver) source := by
    simpa [firstLaw, freshDriver, source, trajectory, gaps, rate, firstMean,
      arrivalProbability, arrivalProbability_le_one, markLaw] using
      (manyServerMarkedCanonicalHorizonSample_futureDriver_hasLaw
        (initial := initial) trafficIntensity serviceRate servers hservers hserviceRate hstart)
  have hsecondFuture : HasLaw (fun value : (ℕ → ℝ) × (ℕ → Bool) =>
      (manyServerMarkedFreshHorizonSample firstDuration value,
        manyServerMarkedFreshFutureDriver firstDuration value))
      (secondLaw.prod freshDriver) freshDriver := by
    simpa [secondLaw, freshDriver, gaps, rate, secondMean, arrivalProbability,
      arrivalProbability_le_one, markLaw] using
      (manyServerMarkedFreshHorizonSample_futureDriver_hasLaw
        trafficIntensity serviceRate servers hservers hserviceRate hfirstDuration)
  have hfirstTransform : HasLaw
      (Prod.map id (fun value : (ℕ → ℝ) × (ℕ → Bool) =>
        (manyServerMarkedFreshHorizonSample firstDuration value,
          manyServerMarkedFreshFutureDriver firstDuration value)))
      (firstLaw.prod (secondLaw.prod freshDriver)) (firstLaw.prod freshDriver) := by
    refine ⟨(measurable_id.prodMap
      ((measurable_manyServerMarkedFreshHorizonSample firstDuration).prodMk
        (measurable_manyServerMarkedFreshFutureDriver firstDuration))).aemeasurable, ?_⟩
    calc
      Measure.map (Prod.map id (fun value : (ℕ → ℝ) × (ℕ → Bool) =>
          (manyServerMarkedFreshHorizonSample firstDuration value,
            manyServerMarkedFreshFutureDriver firstDuration value)))
          (firstLaw.prod freshDriver) =
          (Measure.map id firstLaw).prod
            (Measure.map (fun value : (ℕ → ℝ) × (ℕ → Bool) =>
              (manyServerMarkedFreshHorizonSample firstDuration value,
                manyServerMarkedFreshFutureDriver firstDuration value)) freshDriver) :=
        (Measure.map_prod_map firstLaw freshDriver measurable_id
          ((measurable_manyServerMarkedFreshHorizonSample firstDuration).prodMk
            (measurable_manyServerMarkedFreshFutureDriver firstDuration))).symm
      _ = firstLaw.prod (secondLaw.prod freshDriver) := by
        rw [Measure.map_id, hsecondFuture.map_eq]
  have hthird : HasLaw (manyServerMarkedFreshHorizonSample secondDuration)
      thirdLaw freshDriver := by
    simpa [thirdLaw, freshDriver, gaps, markLaw, rate, thirdMean,
      arrivalProbability, arrivalProbability_le_one] using
      (manyServerMarkedFreshHorizonSample_hasLaw
        trafficIntensity serviceRate servers hservers hserviceRate hsecondDuration)
  have hsecondTransform : HasLaw
      (Prod.map id (Prod.map id (manyServerMarkedFreshHorizonSample secondDuration)))
      (firstLaw.prod (secondLaw.prod thirdLaw))
      (firstLaw.prod (secondLaw.prod freshDriver)) := by
    refine ⟨(measurable_id.prodMap
      (measurable_id.prodMap
        (measurable_manyServerMarkedFreshHorizonSample secondDuration))).aemeasurable, ?_⟩
    calc
      Measure.map (Prod.map id (Prod.map id
          (manyServerMarkedFreshHorizonSample secondDuration)))
          (firstLaw.prod (secondLaw.prod freshDriver)) =
          (Measure.map id firstLaw).prod
            (Measure.map (Prod.map id
              (manyServerMarkedFreshHorizonSample secondDuration))
              (secondLaw.prod freshDriver)) := by
            exact (Measure.map_prod_map firstLaw (secondLaw.prod freshDriver)
              measurable_id
              (measurable_id.prodMap
                (measurable_manyServerMarkedFreshHorizonSample secondDuration))).symm
      _ = firstLaw.prod
          ((Measure.map id secondLaw).prod
            (Measure.map (manyServerMarkedFreshHorizonSample secondDuration)
              freshDriver)) := by
            rw [Measure.map_id]
            congr 1
            exact (Measure.map_prod_map secondLaw freshDriver measurable_id
              (measurable_manyServerMarkedFreshHorizonSample secondDuration)).symm
      _ = firstLaw.prod (secondLaw.prod thirdLaw) := by
        rw [Measure.map_id, hthird.map_eq]
  have hresult := hsecondTransform.comp (hfirstTransform.comp hpastFuture)
  simpa [manyServerMarkedCanonicalHorizon_twoIntervalSamples,
    manyServerMarkedCanonicalFutureDriver, manyServerMarkedFreshFutureDriver,
    source, trajectory, gaps, rate, firstMean, secondMean, thirdMean,
    firstLaw, secondLaw, thirdLaw, freshDriver, arrivalProbability,
    arrivalProbability_le_one, markLaw, Function.comp_def] using hresult

/-- The iterated product measure of a finite list of marked-Poisson sample
laws.  The constructor exposes the usual independent-block semantics while
using a plain list as the finite partition carrier. -/
instance : MeasurableSpace (List FiniteHorizonMarkedPoisson.Sample) := ⊤

noncomputable def markedPoissonSampleListMeasure :
    List (Measure FiniteHorizonMarkedPoisson.Sample) →
      Measure (List FiniteHorizonMarkedPoisson.Sample)
  | [] => Measure.dirac []
  | law :: laws =>
      Measure.map
        (fun value : FiniteHorizonMarkedPoisson.Sample ×
          List FiniteHorizonMarkedPoisson.Sample => value.1 :: value.2)
        (law.prod (markedPoissonSampleListMeasure laws))

/-- Successive marked samples emitted from a fresh clock/mark driver over a
finite list of nonnegative durations. -/
def manyServerMarkedFreshSampleList :
    List (ℝ≥0) → ((ℕ → ℝ) × (ℕ → Bool)) →
      List FiniteHorizonMarkedPoisson.Sample
  | [], _ => []
  | duration :: durations, driver =>
      manyServerMarkedFreshHorizonSample (duration : ℝ) driver ::
        manyServerMarkedFreshSampleList durations
          (manyServerMarkedFreshFutureDriver (duration : ℝ) driver)

/-- The fresh finite sample-list map is measurable. -/
theorem measurable_manyServerMarkedFreshSampleList (durations : List (ℝ≥0)) :
    Measurable (manyServerMarkedFreshSampleList durations) := by
  induction durations with
  | nil =>
      exact measurable_const
  | cons duration durations ih =>
      change Measurable (fun driver =>
        manyServerMarkedFreshHorizonSample (duration : ℝ) driver ::
          manyServerMarkedFreshSampleList durations
            (manyServerMarkedFreshFutureDriver (duration : ℝ) driver))
      have hpair : Measurable (fun driver =>
          (manyServerMarkedFreshHorizonSample (duration : ℝ) driver,
            manyServerMarkedFreshSampleList durations
              (manyServerMarkedFreshFutureDriver (duration : ℝ) driver))) :=
        (measurable_manyServerMarkedFreshHorizonSample (duration : ℝ)).prodMk
          (ih.comp (measurable_manyServerMarkedFreshFutureDriver (duration : ℝ)))
      simpa only [Function.comp_apply] using
        (measurable_of_countable
          (fun value : FiniteHorizonMarkedPoisson.Sample ×
            List FiniteHorizonMarkedPoisson.Sample => value.1 :: value.2)).comp hpair

/-- A fresh marked driver factors over every finite deterministic partition:
the complete list of marked samples has the iterated product of its
single-block marked-Poisson laws. -/
theorem manyServerMarkedFreshSampleList_hasLaw
    (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers : ℕ) (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    (durations : List (ℝ≥0)) :
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    let arrivalProbability := uniformizedBirthProbability trafficIntensity
    let markLaw := (manyServerUniformizationArrivalMark trafficIntensity).toMeasure
    let freshDriver :=
      (PoissonProcess.exponentialInterarrivalMeasure rate).prod
        (IIDStream.measure markLaw)
    let sampleLaw : ℝ≥0 → Measure FiniteHorizonMarkedPoisson.Sample :=
      fun duration =>
        (FiniteHorizonMarkedPoisson.jointPMF
          ⟨rate * (duration : ℝ), mul_nonneg
            (le_of_lt (manyServerUniformizationRate_pos trafficIntensity serviceRate
              servers hservers hserviceRate)) duration.2⟩
          arrivalProbability
          (uniformizedBirthProbability_le_one trafficIntensity)).toMeasure
    HasLaw (manyServerMarkedFreshSampleList durations)
      (markedPoissonSampleListMeasure (durations.map sampleLaw)) freshDriver := by
  dsimp only
  let rate : ℝ := manyServerUniformizationRate
    (trafficIntensity : ℝ) serviceRate servers
  let arrivalProbability : ℝ≥0 := uniformizedBirthProbability trafficIntensity
  let arrivalProbability_le_one : arrivalProbability ≤ 1 :=
    uniformizedBirthProbability_le_one trafficIntensity
  let markLaw : Measure Bool :=
    (manyServerUniformizationArrivalMark trafficIntensity).toMeasure
  let freshDriver : Measure ((ℕ → ℝ) × (ℕ → Bool)) :=
    (PoissonProcess.exponentialInterarrivalMeasure rate).prod
      (IIDStream.measure markLaw)
  have hrate : 0 < rate := by
    exact manyServerUniformizationRate_pos trafficIntensity serviceRate
      servers hservers hserviceRate
  let sampleLaw : ℝ≥0 → Measure FiniteHorizonMarkedPoisson.Sample :=
    fun duration =>
      (FiniteHorizonMarkedPoisson.jointPMF
        ⟨rate * (duration : ℝ), mul_nonneg (le_of_lt hrate) duration.2⟩
        arrivalProbability arrivalProbability_le_one).toMeasure
  letI : IsProbabilityMeasure markLaw := by
    dsimp [markLaw]
    infer_instance
  letI : IsProbabilityMeasure (IIDStream.measure markLaw) := by
    dsimp [IIDStream.measure]
    infer_instance
  letI : IsProbabilityMeasure
      (PoissonProcess.exponentialInterarrivalMeasure rate) :=
    PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure freshDriver := by
    dsimp [freshDriver]
    infer_instance
  induction durations with
  | nil =>
      refine ⟨(measurable_manyServerMarkedFreshSampleList []).aemeasurable, ?_⟩
      change Measure.map (fun _ : (ℕ → ℝ) × (ℕ → Bool) => []) freshDriver =
        Measure.dirac []
      rw [Measure.map_const, measure_univ, one_smul]
  | cons duration durations ih =>
      have hheadFuture : HasLaw (fun value : (ℕ → ℝ) × (ℕ → Bool) =>
          (manyServerMarkedFreshHorizonSample (duration : ℝ) value,
            manyServerMarkedFreshFutureDriver (duration : ℝ) value))
          ((sampleLaw duration).prod freshDriver) freshDriver := by
        simpa [sampleLaw, freshDriver, markLaw, rate, arrivalProbability,
          arrivalProbability_le_one] using
          (manyServerMarkedFreshHorizonSample_futureDriver_hasLaw
            trafficIntensity serviceRate servers hservers hserviceRate duration.2)
      have htransform : HasLaw
          (Prod.map id (manyServerMarkedFreshSampleList durations))
          ((sampleLaw duration).prod
            (markedPoissonSampleListMeasure (durations.map sampleLaw)))
          ((sampleLaw duration).prod freshDriver) := by
        refine ⟨(measurable_id.prodMap
          (measurable_manyServerMarkedFreshSampleList durations)).aemeasurable, ?_⟩
        calc
          Measure.map (Prod.map id (manyServerMarkedFreshSampleList durations))
              ((sampleLaw duration).prod freshDriver) =
              (Measure.map id (sampleLaw duration)).prod
                (Measure.map (manyServerMarkedFreshSampleList durations) freshDriver) :=
            (Measure.map_prod_map (sampleLaw duration) freshDriver measurable_id
              (measurable_manyServerMarkedFreshSampleList durations)).symm
          _ = (sampleLaw duration).prod
              (markedPoissonSampleListMeasure (durations.map sampleLaw)) := by
            rw [Measure.map_id, ih.map_eq]
      have hcons : HasLaw
          (fun value : FiniteHorizonMarkedPoisson.Sample ×
            List FiniteHorizonMarkedPoisson.Sample => value.1 :: value.2)
          (markedPoissonSampleListMeasure
            (sampleLaw duration :: durations.map sampleLaw))
          ((sampleLaw duration).prod
            (markedPoissonSampleListMeasure (durations.map sampleLaw))) := by
        refine ⟨(measurable_of_countable
          (fun value : FiniteHorizonMarkedPoisson.Sample ×
            List FiniteHorizonMarkedPoisson.Sample => value.1 :: value.2)).aemeasurable, ?_⟩
        rfl
      have hresult := hcons.comp (htransform.comp hheadFuture)
      simpa [manyServerMarkedFreshSampleList, markedPoissonSampleListMeasure,
        sampleLaw, Function.comp_def] using hresult

/-- The horizon sample and every later block in a finite deterministic
partition of the canonical marked construction. -/
def manyServerMarkedCanonicalHorizon_sampleList
    (start : ℝ) (durations : List (ℝ≥0)) :
    ((ℕ → ℕ × Bool) × (ℕ → ℝ)) →
      FiniteHorizonMarkedPoisson.Sample ×
        List FiniteHorizonMarkedPoisson.Sample :=
  fun value =>
    (manyServerMarkedCanonicalHorizonSample start value,
      manyServerMarkedFreshSampleList durations
        (manyServerMarkedCanonicalFutureDriver start value))

/-- The canonical marked construction factors at a deterministic horizon into
that horizon's marked-Poisson sample and the iterated product law of every
subsequent block in a finite deterministic partition. -/
theorem manyServerMarkedCanonicalHorizon_sampleList_hasLaw
    {initial : PMF ℕ} (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers : ℕ) (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    {start : ℝ} (hstart : 0 ≤ start) (durations : List (ℝ≥0)) :
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    let firstMean : ℝ≥0 := ⟨rate * start, mul_nonneg
      (le_of_lt (manyServerUniformizationRate_pos trafficIntensity serviceRate
        servers hservers hserviceRate)) hstart⟩
    let arrivalProbability := uniformizedBirthProbability trafficIntensity
    let markLaw := (manyServerUniformizationArrivalMark trafficIntensity).toMeasure
    let freshDriver :=
      (PoissonProcess.exponentialInterarrivalMeasure rate).prod
        (IIDStream.measure markLaw)
    let sampleLaw : ℝ≥0 → Measure FiniteHorizonMarkedPoisson.Sample :=
      fun duration =>
        (FiniteHorizonMarkedPoisson.jointPMF
          ⟨rate * (duration : ℝ), mul_nonneg
            (le_of_lt (manyServerUniformizationRate_pos trafficIntensity serviceRate
              servers hservers hserviceRate)) duration.2⟩
          arrivalProbability
          (uniformizedBirthProbability_le_one trafficIntensity)).toMeasure
    HasLaw (manyServerMarkedCanonicalHorizon_sampleList start durations)
      (((FiniteHorizonMarkedPoisson.jointPMF firstMean arrivalProbability
        (uniformizedBirthProbability_le_one trafficIntensity)).toMeasure).prod
          (markedPoissonSampleListMeasure (durations.map sampleLaw)))
      ((stationaryTrajMeasure
        (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
        (manyServerMarkedStateUniformizationMeasureKernel
          trafficIntensity servers hservers)).prod
        (PoissonProcess.exponentialInterarrivalMeasure rate)) := by
  dsimp only
  let rate : ℝ := manyServerUniformizationRate
    (trafficIntensity : ℝ) serviceRate servers
  let firstMean : ℝ≥0 := ⟨rate * start, mul_nonneg
    (le_of_lt (manyServerUniformizationRate_pos trafficIntensity serviceRate
      servers hservers hserviceRate)) hstart⟩
  let arrivalProbability : ℝ≥0 := uniformizedBirthProbability trafficIntensity
  let arrivalProbability_le_one : arrivalProbability ≤ 1 :=
    uniformizedBirthProbability_le_one trafficIntensity
  let markLaw : Measure Bool :=
    (manyServerUniformizationArrivalMark trafficIntensity).toMeasure
  let freshDriver : Measure ((ℕ → ℝ) × (ℕ → Bool)) :=
    (PoissonProcess.exponentialInterarrivalMeasure rate).prod
      (IIDStream.measure markLaw)
  let sampleLaw : ℝ≥0 → Measure FiniteHorizonMarkedPoisson.Sample :=
    fun duration =>
      (FiniteHorizonMarkedPoisson.jointPMF
        ⟨rate * (duration : ℝ), mul_nonneg
          (le_of_lt (manyServerUniformizationRate_pos trafficIntensity serviceRate
            servers hservers hserviceRate)) duration.2⟩
        arrivalProbability arrivalProbability_le_one).toMeasure
  let source : Measure ((ℕ → ℕ × Bool) × (ℕ → ℝ)) :=
    (stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)).prod
      (PoissonProcess.exponentialInterarrivalMeasure rate)
  let firstLaw : Measure FiniteHorizonMarkedPoisson.Sample :=
    (FiniteHorizonMarkedPoisson.jointPMF firstMean arrivalProbability
      arrivalProbability_le_one).toMeasure
  have hrate : 0 < rate := by
    exact manyServerUniformizationRate_pos trafficIntensity serviceRate
      servers hservers hserviceRate
  letI : IsProbabilityMeasure initial.toMeasure := by infer_instance
  letI : IsProbabilityMeasure markLaw := by
    dsimp [markLaw]
    infer_instance
  letI : IsProbabilityMeasure (IIDStream.measure markLaw) := by
    dsimp [IIDStream.measure]
    infer_instance
  letI : IsProbabilityMeasure
      (PoissonProcess.exponentialInterarrivalMeasure rate) :=
    PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure freshDriver := by
    dsimp [freshDriver]
    infer_instance
  have hpastFuture : HasLaw (fun value : ((ℕ → ℕ × Bool) × (ℕ → ℝ)) =>
      (manyServerMarkedCanonicalHorizonSample start value,
        manyServerMarkedCanonicalFutureDriver start value))
      (firstLaw.prod freshDriver) source := by
    simpa [firstLaw, freshDriver, source, rate, firstMean,
      arrivalProbability, arrivalProbability_le_one, markLaw] using
      (manyServerMarkedCanonicalHorizonSample_futureDriver_hasLaw
        (initial := initial) trafficIntensity serviceRate servers hservers hserviceRate hstart)
  have htail : HasLaw (manyServerMarkedFreshSampleList durations)
      (markedPoissonSampleListMeasure (durations.map sampleLaw)) freshDriver := by
    simpa [sampleLaw, freshDriver, markLaw, rate, arrivalProbability,
      arrivalProbability_le_one] using
      (manyServerMarkedFreshSampleList_hasLaw
        trafficIntensity serviceRate servers hservers hserviceRate durations)
  have htransform : HasLaw
      (Prod.map id (manyServerMarkedFreshSampleList durations))
      (firstLaw.prod
        (markedPoissonSampleListMeasure (durations.map sampleLaw)))
      (firstLaw.prod freshDriver) := by
    refine ⟨(measurable_id.prodMap
      (measurable_manyServerMarkedFreshSampleList durations)).aemeasurable, ?_⟩
    calc
      Measure.map (Prod.map id (manyServerMarkedFreshSampleList durations))
          (firstLaw.prod freshDriver) =
          (Measure.map id firstLaw).prod
            (Measure.map (manyServerMarkedFreshSampleList durations) freshDriver) :=
        (Measure.map_prod_map firstLaw freshDriver measurable_id
          (measurable_manyServerMarkedFreshSampleList durations)).symm
      _ = firstLaw.prod
          (markedPoissonSampleListMeasure (durations.map sampleLaw)) := by
        rw [Measure.map_id, htail.map_eq]
  have hresult := htransform.comp hpastFuture
  simpa [manyServerMarkedCanonicalHorizon_sampleList, source,
    firstLaw, freshDriver, sampleLaw, Function.comp_def] using hresult

/-- The literal marked samples in the consecutive intervals determined by a
finite duration list.  The left endpoint of each block is the sum of the
previous durations. -/
noncomputable def manyServerMarkedCanonicalIntervalSampleList (start : ℝ) :
    List (ℝ≥0) → ((ℕ → ℕ × Bool) × (ℕ → ℝ)) →
      List FiniteHorizonMarkedPoisson.Sample
  | [], _ => []
  | duration :: durations, value =>
      manyServerMarkedCanonicalIntervalSample start (duration : ℝ) value ::
        manyServerMarkedCanonicalIntervalSampleList
          (start + (duration : ℝ)) durations value

/-- The successive fresh marked samples after a deterministic canonical
restart agree almost surely with the literal marked samples in the associated
consecutive physical intervals. -/
theorem ae_manyServerMarkedFreshSampleList_canonicalFutureDriver_eq_intervalSampleList
    {initial : PMF ℕ} (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers : ℕ) (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    (start : ℝ) (durations : List (ℝ≥0)) :
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    let source :=
      (stationaryTrajMeasure
        (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
        (manyServerMarkedStateUniformizationMeasureKernel
          trafficIntensity servers hservers)).prod
        (PoissonProcess.exponentialInterarrivalMeasure rate)
    ∀ᵐ value ∂source,
      manyServerMarkedFreshSampleList durations
        (manyServerMarkedCanonicalFutureDriver start value) =
        manyServerMarkedCanonicalIntervalSampleList start durations value := by
  dsimp only
  let rate := manyServerUniformizationRate
    (trafficIntensity : ℝ) serviceRate servers
  let trajectory := stationaryTrajMeasure
    (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
    (manyServerMarkedStateUniformizationMeasureKernel trafficIntensity servers hservers)
  let gaps := PoissonProcess.exponentialInterarrivalMeasure rate
  let source := trajectory.prod gaps
  have hrate : 0 < rate := by
    exact manyServerUniformizationRate_pos trafficIntensity serviceRate
      servers hservers hserviceRate
  induction durations generalizing start with
  | nil =>
      filter_upwards [] with value
      rfl
  | cons duration durations ih =>
      have hrestart : ∀ᵐ value ∂source,
          manyServerMarkedCanonicalFutureDriver (start + (duration : ℝ)) value =
            manyServerMarkedFreshFutureDriver (duration : ℝ)
              (manyServerMarkedCanonicalFutureDriver start value) := by
        simpa [source, trajectory, gaps, rate] using
          (ae_manyServerMarkedCanonicalFutureDriver_add_eq_freshFutureDriver_comp
            (initial := initial) trafficIntensity servers hservers hrate duration.2
            (s := start))
      have htail : ∀ᵐ value ∂source,
          manyServerMarkedFreshSampleList durations
            (manyServerMarkedCanonicalFutureDriver (start + (duration : ℝ)) value) =
            manyServerMarkedCanonicalIntervalSampleList
              (start + (duration : ℝ)) durations value := by
        exact ih (start := start + (duration : ℝ))
      filter_upwards [hrestart, htail] with value hrestartValue htailValue
      change manyServerMarkedFreshHorizonSample (duration : ℝ)
          (manyServerMarkedCanonicalFutureDriver start value) ::
          manyServerMarkedFreshSampleList durations
            (manyServerMarkedFreshFutureDriver (duration : ℝ)
              (manyServerMarkedCanonicalFutureDriver start value)) =
        manyServerMarkedCanonicalIntervalSample start (duration : ℝ) value ::
          manyServerMarkedCanonicalIntervalSampleList
            (start + (duration : ℝ)) durations value
      rw [← hrestartValue, htailValue]
      rfl

/-- The iterated product measure of a finite list of retained/discarded
Poisson count-pair laws. -/
instance : MeasurableSpace (List (ℕ × ℕ)) := ⊤

noncomputable def poissonCountPairListMeasure :
    List (Measure (ℕ × ℕ)) → Measure (List (ℕ × ℕ))
  | [] => Measure.dirac []
  | law :: laws =>
      Measure.map
        (fun value : (ℕ × ℕ) × List (ℕ × ℕ) => value.1 :: value.2)
        (law.prod (poissonCountPairListMeasure laws))

/-- Read a finite list of count pairs as a function on a prescribed finite
index type.  The fallback only acts on lists of the wrong length, which are
outside the support of the iterated product law used below. -/
noncomputable def countPairListToFinFunction
    (length : ℕ) (values : List (ℕ × ℕ)) : Fin length → ℕ × ℕ :=
  fun index => values.getD index (0, 0)

@[simp]
theorem countPairListToFinFunction_zero (values : List (ℕ × ℕ)) :
    countPairListToFinFunction 0 values = fun index => Fin.elim0 index := by
  funext index
  exact Fin.elim0 index

@[simp]
theorem countPairListToFinFunction_cons (value : ℕ × ℕ)
    (values : List (ℕ × ℕ)) (length : ℕ) :
    countPairListToFinFunction (length + 1) (value :: values) =
      fun index => Fin.cases value (fun tailIndex =>
        countPairListToFinFunction length values tailIndex) index := by
  funext index
  refine Fin.cases ?_ ?_ index
  · simp [countPairListToFinFunction]
  · intro tailIndex
    simp [countPairListToFinFunction]

/-- The list-to-finite-function map is measurable because the list domain has
the discrete measurable structure used by the finite partition law. -/
theorem measurable_countPairListToFinFunction (length : ℕ) :
    Measurable (countPairListToFinFunction length) := by
  exact Measurable.of_discrete

/-- Reindex a finite function along an equality of its index cardinalities. -/
noncomputable def finFunctionReindex {α : Type*} {firstLength secondLength : ℕ}
    (h : firstLength = secondLength) :
    (Fin secondLength → α) → Fin firstLength → α :=
  fun values index => values (Fin.cast h index)

/-- The iterated product measure of a finite list of count-pair laws, now
represented on a fixed finite function space rather than a list. -/
noncomputable def poissonCountPairFiniteProductMeasure :
    (laws : List (Measure (ℕ × ℕ))) → Measure (Fin laws.length → ℕ × ℕ)
  | [] => Measure.dirac (fun index => Fin.elim0 index)
  | law :: laws =>
      Measure.map
        (fun value index => Fin.cases value.1 (fun tailIndex => value.2 tailIndex) index)
        (law.prod (poissonCountPairFiniteProductMeasure laws))

/-- Equal finite lists of count-pair laws give equal product laws after their
coordinates are transported to one common finite index type. -/
theorem map_finFunctionReindex_poissonCountPairFiniteProductMeasure_eq_of_eq
    {laws firstLaws : List (Measure (ℕ × ℕ))} {length : ℕ}
    (hlaws : length = laws.length) (hfirstLaws : length = firstLaws.length)
    (h : laws = firstLaws) :
    Measure.map (finFunctionReindex (α := ℕ × ℕ) hlaws)
      (poissonCountPairFiniteProductMeasure laws) =
    Measure.map (finFunctionReindex (α := ℕ × ℕ) hfirstLaws)
      (poissonCountPairFiniteProductMeasure firstLaws) := by
  subst firstLaws
  rfl

/-- The recursive finite product of count-pair laws is the standard finite
product measure indexed by its positions. -/
theorem poissonCountPairFiniteProductMeasure_eq_pi
    (laws : List (Measure (ℕ × ℕ)))
    (hfinite : ∀ law ∈ laws, IsFiniteMeasure law) :
    poissonCountPairFiniteProductMeasure laws =
      Measure.pi (fun index : Fin laws.length => laws.get index) := by
  induction laws with
  | nil =>
      letI : ∀ index : Fin (([] : List (Measure (ℕ × ℕ))).length),
          SigmaFinite (([] : List (Measure (ℕ × ℕ))).get index) :=
        fun index => Fin.elim0 index
      apply (Measure.pi_eq ?_).symm
      intro s hs
      simp [poissonCountPairFiniteProductMeasure]
  | cons law laws ih =>
      letI : ∀ index : Fin (law :: laws).length,
          IsFiniteMeasure ((law :: laws).get index) :=
        fun index => hfinite ((law :: laws).get index) (List.get_mem _ index)
      letI : ∀ index : Fin laws.length, IsFiniteMeasure (laws.get index) :=
        fun index => hfinite (laws.get index) (by simp)
      have htailFinite : ∀ tailLaw ∈ laws, IsFiniteMeasure tailLaw := by
        intro tailLaw htailLaw
        exact hfinite tailLaw (by simp [htailLaw])
      have htail := ih htailFinite
      apply (Measure.pi_eq ?_).symm
      intro s hs
      let merge : (ℕ × ℕ) × (Fin laws.length → ℕ × ℕ) →
          Fin (laws.length + 1) → ℕ × ℕ :=
        fun value index => Fin.cases value.1 (fun tailIndex => value.2 tailIndex) index
      have hmerge : Measurable merge := by
        apply measurable_pi_lambda
        intro index
        refine Fin.cases ?_ ?_ index
        · exact measurable_fst
        · intro tailIndex
          exact (measurable_pi_apply tailIndex).comp measurable_snd
      have hpreimage : merge ⁻¹' Set.univ.pi s =
          s 0 ×ˢ Set.univ.pi (fun index : Fin laws.length => s index.succ) := by
        ext value
        simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_prod]
        rw [Fin.forall_fin_succ]
        rfl
      change Measure.map merge (law.prod (poissonCountPairFiniteProductMeasure laws))
          (Set.univ.pi s) = _
      rw [Measure.map_apply hmerge (MeasurableSet.univ_pi hs), hpreimage,
        Measure.prod_prod, htail, Measure.pi_pi]
      simpa only [List.length_cons, List.get_cons_zero, List.get_cons_succ] using
        (Fin.prod_univ_succ
          (fun index : Fin (laws.length + 1) => (law :: laws).get index (s index))).symm

/-- Transporting a finite product measure along a cardinality equality simply
reindexes its coordinate laws. -/
theorem map_finFunctionReindex_pi_eq
    {length : ℕ} (laws : List (Measure (ℕ × ℕ)))
    (hlength : length = laws.length) :
    Measure.map (finFunctionReindex hlength)
      (Measure.pi (fun index : Fin laws.length => laws.get index)) =
      Measure.pi (fun index : Fin length => laws.get (Fin.cast hlength index)) := by
  subst length
  convert Measure.map_id using 1

/-- Applying `countPairListToFinFunction` to the list product law yields the
corresponding finite-function product law. -/
theorem map_countPairListToFinFunction_poissonCountPairListMeasure
    (laws : List (Measure (ℕ × ℕ))) :
    Measure.map (countPairListToFinFunction laws.length)
      (poissonCountPairListMeasure laws) =
      poissonCountPairFiniteProductMeasure laws := by
  induction laws with
  | nil =>
      simp [poissonCountPairListMeasure, poissonCountPairFiniteProductMeasure]
  | cons law laws ih =>
      let listToFunction := countPairListToFinFunction laws.length
      let productToFunction : (ℕ × ℕ) × (Fin laws.length → ℕ × ℕ) →
          Fin (laws.length + 1) → ℕ × ℕ :=
        fun value index => Fin.cases value.1 (fun tailIndex => value.2 tailIndex) index
      let consMap : (ℕ × ℕ) × List (ℕ × ℕ) → List (ℕ × ℕ) :=
        fun value => value.1 :: value.2
      have hconsMap : Measurable consMap := Measurable.of_discrete
      have hlistToFunction : Measurable listToFunction :=
        measurable_countPairListToFinFunction laws.length
      have hproductToFunction : Measurable productToFunction := by
        exact Measurable.of_discrete
      have hcompose : countPairListToFinFunction (laws.length + 1) ∘ consMap =
          productToFunction ∘ Prod.map id listToFunction := by
        funext value
        simpa [listToFunction, productToFunction, consMap] using
          (countPairListToFinFunction_cons value.1 value.2 laws.length)
      change Measure.map (countPairListToFinFunction (laws.length + 1))
        (Measure.map consMap (law.prod (poissonCountPairListMeasure laws))) = _
      rw [Measure.map_map (measurable_countPairListToFinFunction _) hconsMap, hcompose]
      rw [← Measure.map_map hproductToFunction
        (measurable_id.prodMap hlistToFunction)]
      congr 1
      rw [← Measure.map_prod_map law (poissonCountPairListMeasure laws)
        measurable_id hlistToFunction, ih, Measure.map_id]

/-- A joint horizon-and-partition count law induces the corresponding law of
the finite vector of partition increments. -/
theorem _root_.ProbabilityTheory.HasLaw.snd_countPairListToFinFunction
    {Ω : Type*} [MeasurableSpace Ω] {source : Measure Ω}
    {firstLaw : Measure (ℕ × ℕ)} [IsProbabilityMeasure firstLaw]
    {laws : List (Measure (ℕ × ℕ))}
    {randomValue : Ω → (ℕ × ℕ) × List (ℕ × ℕ)}
    (h : HasLaw randomValue (firstLaw.prod (poissonCountPairListMeasure laws)) source) :
    HasLaw (fun omega => countPairListToFinFunction laws.length (randomValue omega).2)
      (poissonCountPairFiniteProductMeasure laws) source := by
  let transform : (ℕ × ℕ) × List (ℕ × ℕ) → Fin laws.length → ℕ × ℕ :=
    fun value => countPairListToFinFunction laws.length value.2
  have htransform : HasLaw transform (poissonCountPairFiniteProductMeasure laws)
      (firstLaw.prod (poissonCountPairListMeasure laws)) := by
    refine ⟨Measurable.of_discrete.aemeasurable, ?_⟩
    change Measure.map ((countPairListToFinFunction laws.length) ∘ Prod.snd)
      (firstLaw.prod (poissonCountPairListMeasure laws)) =
        poissonCountPairFiniteProductMeasure laws
    rw [← Measure.map_map (measurable_countPairListToFinFunction _) measurable_snd,
      Measure.map_snd_prod, measure_univ, one_smul]
    exact map_countPairListToFinFunction_poissonCountPairListMeasure laws
  simpa [transform] using htransform.comp h

/-- Mapping every marked sample in a finite list to its retained/discarded
counts is measurable. -/
theorem measurable_list_map_markedSplitCounts :
    Measurable
      (List.map (FiniteHorizonMarkedPoisson.splitCounts :
        FiniteHorizonMarkedPoisson.Sample → ℕ × ℕ)) :=
  measurable_of_countable _

/-- Independent finite marked-Poisson samples yield an independent finite
list of retained/discarded Poisson count pairs. -/
theorem markedPoissonSampleListMeasure_splitCounts_hasLaw
    (means : List (ℝ≥0)) (arrivalProbability : ℝ≥0)
    (arrivalProbability_le_one : arrivalProbability ≤ 1) :
    HasLaw
      (List.map (FiniteHorizonMarkedPoisson.splitCounts :
        FiniteHorizonMarkedPoisson.Sample → ℕ × ℕ))
      (poissonCountPairListMeasure
        (means.map fun mean =>
          (ProbabilityTheory.poissonMeasure (mean * arrivalProbability)).prod
            (ProbabilityTheory.poissonMeasure
              (mean * (1 - arrivalProbability)))))
      (markedPoissonSampleListMeasure
        (means.map fun mean =>
          (FiniteHorizonMarkedPoisson.jointPMF mean arrivalProbability
            arrivalProbability_le_one).toMeasure)) := by
  induction means with
  | nil =>
      refine ⟨measurable_list_map_markedSplitCounts.aemeasurable, ?_⟩
      simp [markedPoissonSampleListMeasure, poissonCountPairListMeasure]
  | cons mean means ih =>
      let sampleLaw : Measure FiniteHorizonMarkedPoisson.Sample :=
        (FiniteHorizonMarkedPoisson.jointPMF mean arrivalProbability
          arrivalProbability_le_one).toMeasure
      let countLaw : Measure (ℕ × ℕ) :=
        (ProbabilityTheory.poissonMeasure (mean * arrivalProbability)).prod
          (ProbabilityTheory.poissonMeasure (mean * (1 - arrivalProbability)))
      let tailSampleLaw : Measure (List FiniteHorizonMarkedPoisson.Sample) :=
        markedPoissonSampleListMeasure
          (means.map fun tailMean =>
            (FiniteHorizonMarkedPoisson.jointPMF tailMean arrivalProbability
              arrivalProbability_le_one).toMeasure)
      let tailCountLaw : Measure (List (ℕ × ℕ)) :=
        poissonCountPairListMeasure
          (means.map fun tailMean =>
            (ProbabilityTheory.poissonMeasure (tailMean * arrivalProbability)).prod
              (ProbabilityTheory.poissonMeasure
                (tailMean * (1 - arrivalProbability))))
      have hsourceCons : HasLaw
          (fun value : FiniteHorizonMarkedPoisson.Sample ×
            List FiniteHorizonMarkedPoisson.Sample => value.1 :: value.2)
          (markedPoissonSampleListMeasure
            (sampleLaw ::
              means.map fun tailMean =>
                (FiniteHorizonMarkedPoisson.jointPMF tailMean arrivalProbability
                  arrivalProbability_le_one).toMeasure))
          (sampleLaw.prod tailSampleLaw) := by
        refine ⟨(measurable_of_countable
          (fun value : FiniteHorizonMarkedPoisson.Sample ×
            List FiniteHorizonMarkedPoisson.Sample => value.1 :: value.2)).aemeasurable, ?_⟩
        rfl
      have hhead : HasLaw FiniteHorizonMarkedPoisson.splitCounts countLaw sampleLaw := by
        simpa [sampleLaw, countLaw] using
          (FiniteHorizonMarkedPoisson.splitCounts_hasLaw mean arrivalProbability
            arrivalProbability_le_one)
      have htail : HasLaw
          (List.map (FiniteHorizonMarkedPoisson.splitCounts :
            FiniteHorizonMarkedPoisson.Sample → ℕ × ℕ))
          tailCountLaw tailSampleLaw := by
        simpa [tailSampleLaw, tailCountLaw] using ih
      have htransform : HasLaw
          (Prod.map FiniteHorizonMarkedPoisson.splitCounts
            (List.map (FiniteHorizonMarkedPoisson.splitCounts :
              FiniteHorizonMarkedPoisson.Sample → ℕ × ℕ)))
          (countLaw.prod tailCountLaw) (sampleLaw.prod tailSampleLaw) := by
        refine ⟨(measurable_of_countable
          (Prod.map FiniteHorizonMarkedPoisson.splitCounts
            (List.map (FiniteHorizonMarkedPoisson.splitCounts :
              FiniteHorizonMarkedPoisson.Sample → ℕ × ℕ)))).aemeasurable, ?_⟩
        calc
          Measure.map
              (Prod.map FiniteHorizonMarkedPoisson.splitCounts
                (List.map (FiniteHorizonMarkedPoisson.splitCounts :
                  FiniteHorizonMarkedPoisson.Sample → ℕ × ℕ)))
              (sampleLaw.prod tailSampleLaw) =
              (Measure.map FiniteHorizonMarkedPoisson.splitCounts sampleLaw).prod
                (Measure.map
                  (List.map (FiniteHorizonMarkedPoisson.splitCounts :
                    FiniteHorizonMarkedPoisson.Sample → ℕ × ℕ))
                  tailSampleLaw) :=
            (Measure.map_prod_map sampleLaw tailSampleLaw
              (measurable_of_countable _) measurable_list_map_markedSplitCounts).symm
          _ = countLaw.prod tailCountLaw := by rw [hhead.map_eq, htail.map_eq]
      have htargetCons : HasLaw
          (fun value : (ℕ × ℕ) × List (ℕ × ℕ) => value.1 :: value.2)
          (poissonCountPairListMeasure
            (countLaw ::
              means.map fun tailMean =>
                (ProbabilityTheory.poissonMeasure (tailMean * arrivalProbability)).prod
                  (ProbabilityTheory.poissonMeasure
                    (tailMean * (1 - arrivalProbability)))))
          (countLaw.prod tailCountLaw) := by
        refine ⟨(measurable_of_countable
          (fun value : (ℕ × ℕ) × List (ℕ × ℕ) => value.1 :: value.2)).aemeasurable, ?_⟩
        rfl
      have hconsSampleMeas : Measurable
          (fun value : FiniteHorizonMarkedPoisson.Sample ×
            List FiniteHorizonMarkedPoisson.Sample => value.1 :: value.2) :=
        measurable_of_countable _
      have hpairMapMeas : Measurable
          (Prod.map FiniteHorizonMarkedPoisson.splitCounts
            (List.map (FiniteHorizonMarkedPoisson.splitCounts :
              FiniteHorizonMarkedPoisson.Sample → ℕ × ℕ))) :=
        measurable_of_countable _
      have hconsCountMeas : Measurable
          (fun value : (ℕ × ℕ) × List (ℕ × ℕ) => value.1 :: value.2) :=
        measurable_of_countable _
      refine ⟨measurable_list_map_markedSplitCounts.aemeasurable, ?_⟩
      calc
        Measure.map
            (List.map (FiniteHorizonMarkedPoisson.splitCounts :
              FiniteHorizonMarkedPoisson.Sample → ℕ × ℕ))
            (markedPoissonSampleListMeasure
              (sampleLaw ::
                means.map fun tailMean =>
                  (FiniteHorizonMarkedPoisson.jointPMF tailMean arrivalProbability
                    arrivalProbability_le_one).toMeasure)) =
            Measure.map
              (List.map (FiniteHorizonMarkedPoisson.splitCounts :
                FiniteHorizonMarkedPoisson.Sample → ℕ × ℕ))
              (Measure.map
                (fun value : FiniteHorizonMarkedPoisson.Sample ×
                  List FiniteHorizonMarkedPoisson.Sample => value.1 :: value.2)
                (sampleLaw.prod tailSampleLaw)) := by
              rw [hsourceCons.map_eq]
        _ = Measure.map
            ((List.map (FiniteHorizonMarkedPoisson.splitCounts :
              FiniteHorizonMarkedPoisson.Sample → ℕ × ℕ)) ∘
              (fun value : FiniteHorizonMarkedPoisson.Sample ×
                List FiniteHorizonMarkedPoisson.Sample => value.1 :: value.2))
            (sampleLaw.prod tailSampleLaw) := by
              exact (Measure.map_map measurable_list_map_markedSplitCounts
                hconsSampleMeas)
        _ = Measure.map
            ((fun value : (ℕ × ℕ) × List (ℕ × ℕ) => value.1 :: value.2) ∘
              Prod.map FiniteHorizonMarkedPoisson.splitCounts
                (List.map (FiniteHorizonMarkedPoisson.splitCounts :
                  FiniteHorizonMarkedPoisson.Sample → ℕ × ℕ)))
            (sampleLaw.prod tailSampleLaw) := by
              rfl
        _ = Measure.map
            (fun value : (ℕ × ℕ) × List (ℕ × ℕ) => value.1 :: value.2)
            (Measure.map
              (Prod.map FiniteHorizonMarkedPoisson.splitCounts
                (List.map (FiniteHorizonMarkedPoisson.splitCounts :
                  FiniteHorizonMarkedPoisson.Sample → ℕ × ℕ)))
              (sampleLaw.prod tailSampleLaw)) := by
              exact (Measure.map_map hconsCountMeas hpairMapMeas).symm
        _ = Measure.map
            (fun value : (ℕ × ℕ) × List (ℕ × ℕ) => value.1 :: value.2)
            (countLaw.prod tailCountLaw) := by
              rw [htransform.map_eq]
        _ = poissonCountPairListMeasure
            (countLaw ::
              means.map fun tailMean =>
                (ProbabilityTheory.poissonMeasure (tailMean * arrivalProbability)).prod
                  (ProbabilityTheory.poissonMeasure
                    (tailMean * (1 - arrivalProbability)))) := htargetCons.map_eq

/-- The retained/discarded count pair at a horizon together with the count
pairs in every later block of a finite deterministic partition. -/
def manyServerMarkedCanonicalHorizon_splitCountList
    (start : ℝ) (durations : List (ℝ≥0)) :
    ((ℕ → ℕ × Bool) × (ℕ → ℝ)) →
      (ℕ × ℕ) × List (ℕ × ℕ) :=
  Prod.map FiniteHorizonMarkedPoisson.splitCounts
    (List.map (FiniteHorizonMarkedPoisson.splitCounts :
      FiniteHorizonMarkedPoisson.Sample → ℕ × ℕ)) ∘
    manyServerMarkedCanonicalHorizon_sampleList start durations

/-- The canonical marked count pairs in an arbitrary finite deterministic
partition have the iterated product of their thinned Poisson laws. -/
theorem manyServerMarkedCanonicalHorizon_splitCountList_hasLaw
    {initial : PMF ℕ} (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers : ℕ) (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    {start : ℝ} (hstart : 0 ≤ start) (durations : List (ℝ≥0)) :
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    let firstMean : ℝ≥0 := ⟨rate * start, mul_nonneg
      (le_of_lt (manyServerUniformizationRate_pos trafficIntensity serviceRate
        servers hservers hserviceRate)) hstart⟩
    let arrivalProbability := uniformizedBirthProbability trafficIntensity
    let tailMeans : List (ℝ≥0) :=
      durations.map fun (duration : ℝ≥0) =>
        ⟨rate * (duration : ℝ), mul_nonneg
          (le_of_lt (manyServerUniformizationRate_pos trafficIntensity serviceRate
            servers hservers hserviceRate)) duration.2⟩
    HasLaw (manyServerMarkedCanonicalHorizon_splitCountList start durations)
      ((((ProbabilityTheory.poissonMeasure (firstMean * arrivalProbability)).prod
        (ProbabilityTheory.poissonMeasure
          (firstMean * (1 - arrivalProbability)))).prod
        (poissonCountPairListMeasure
          (tailMeans.map fun mean =>
            (ProbabilityTheory.poissonMeasure (mean * arrivalProbability)).prod
              (ProbabilityTheory.poissonMeasure
                (mean * (1 - arrivalProbability)))))))
      ((stationaryTrajMeasure
        (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
        (manyServerMarkedStateUniformizationMeasureKernel
          trafficIntensity servers hservers)).prod
        (PoissonProcess.exponentialInterarrivalMeasure rate)) := by
  dsimp only
  let rate : ℝ := manyServerUniformizationRate
    (trafficIntensity : ℝ) serviceRate servers
  let firstMean : ℝ≥0 := ⟨rate * start, mul_nonneg
    (le_of_lt (manyServerUniformizationRate_pos trafficIntensity serviceRate
      servers hservers hserviceRate)) hstart⟩
  let arrivalProbability : ℝ≥0 := uniformizedBirthProbability trafficIntensity
  let arrivalProbability_le_one : arrivalProbability ≤ 1 :=
    uniformizedBirthProbability_le_one trafficIntensity
  let tailMeans : List (ℝ≥0) :=
    durations.map fun (duration : ℝ≥0) =>
      ⟨rate * (duration : ℝ), mul_nonneg
        (le_of_lt (manyServerUniformizationRate_pos trafficIntensity serviceRate
          servers hservers hserviceRate)) duration.2⟩
  let sampleLaw : ℝ≥0 → Measure FiniteHorizonMarkedPoisson.Sample :=
    fun duration =>
      (FiniteHorizonMarkedPoisson.jointPMF
        ⟨rate * (duration : ℝ), mul_nonneg
          (le_of_lt (manyServerUniformizationRate_pos trafficIntensity serviceRate
            servers hservers hserviceRate)) duration.2⟩
        arrivalProbability arrivalProbability_le_one).toMeasure
  let firstSampleLaw : Measure FiniteHorizonMarkedPoisson.Sample :=
    (FiniteHorizonMarkedPoisson.jointPMF firstMean arrivalProbability
      arrivalProbability_le_one).toMeasure
  let firstCountLaw : Measure (ℕ × ℕ) :=
    (ProbabilityTheory.poissonMeasure (firstMean * arrivalProbability)).prod
      (ProbabilityTheory.poissonMeasure
        (firstMean * (1 - arrivalProbability)))
  let tailCountLaw : Measure (List (ℕ × ℕ)) :=
    poissonCountPairListMeasure
      (tailMeans.map fun mean =>
        (ProbabilityTheory.poissonMeasure (mean * arrivalProbability)).prod
          (ProbabilityTheory.poissonMeasure
            (mean * (1 - arrivalProbability))))
  let source : Measure ((ℕ → ℕ × Bool) × (ℕ → ℝ)) :=
    (stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)).prod
      (PoissonProcess.exponentialInterarrivalMeasure rate)
  have hsampleList :
      HasLaw (manyServerMarkedCanonicalHorizon_sampleList start durations)
        (firstSampleLaw.prod
          (markedPoissonSampleListMeasure (durations.map sampleLaw))) source := by
    simpa [firstSampleLaw, sampleLaw, source, rate, firstMean,
      arrivalProbability, arrivalProbability_le_one, tailMeans] using
      (manyServerMarkedCanonicalHorizon_sampleList_hasLaw
        (initial := initial) trafficIntensity serviceRate servers hservers hserviceRate
        hstart durations)
  have hfirst : HasLaw FiniteHorizonMarkedPoisson.splitCounts firstCountLaw
      firstSampleLaw := by
    simpa [firstSampleLaw, firstCountLaw] using
      (FiniteHorizonMarkedPoisson.splitCounts_hasLaw firstMean arrivalProbability
        arrivalProbability_le_one)
  have htail : HasLaw
      (List.map (FiniteHorizonMarkedPoisson.splitCounts :
        FiniteHorizonMarkedPoisson.Sample → ℕ × ℕ))
      tailCountLaw
      (markedPoissonSampleListMeasure (durations.map sampleLaw)) := by
    simpa [tailMeans, tailCountLaw, sampleLaw] using
      (markedPoissonSampleListMeasure_splitCounts_hasLaw
        tailMeans arrivalProbability arrivalProbability_le_one)
  have htransform : HasLaw
      (Prod.map FiniteHorizonMarkedPoisson.splitCounts
        (List.map (FiniteHorizonMarkedPoisson.splitCounts :
          FiniteHorizonMarkedPoisson.Sample → ℕ × ℕ)))
      (firstCountLaw.prod tailCountLaw)
      (firstSampleLaw.prod
        (markedPoissonSampleListMeasure (durations.map sampleLaw))) := by
    refine ⟨(measurable_of_countable
      (Prod.map FiniteHorizonMarkedPoisson.splitCounts
        (List.map (FiniteHorizonMarkedPoisson.splitCounts :
          FiniteHorizonMarkedPoisson.Sample → ℕ × ℕ)))).aemeasurable, ?_⟩
    calc
      Measure.map
          (Prod.map FiniteHorizonMarkedPoisson.splitCounts
            (List.map (FiniteHorizonMarkedPoisson.splitCounts :
              FiniteHorizonMarkedPoisson.Sample → ℕ × ℕ)))
          (firstSampleLaw.prod
            (markedPoissonSampleListMeasure (durations.map sampleLaw))) =
          (Measure.map FiniteHorizonMarkedPoisson.splitCounts firstSampleLaw).prod
            (Measure.map
              (List.map (FiniteHorizonMarkedPoisson.splitCounts :
                FiniteHorizonMarkedPoisson.Sample → ℕ × ℕ))
              (markedPoissonSampleListMeasure (durations.map sampleLaw))) :=
        (Measure.map_prod_map firstSampleLaw
          (markedPoissonSampleListMeasure (durations.map sampleLaw))
          (measurable_of_countable _) measurable_list_map_markedSplitCounts).symm
      _ = firstCountLaw.prod tailCountLaw := by rw [hfirst.map_eq, htail.map_eq]
  have hresult := htransform.comp hsampleList
  simpa [manyServerMarkedCanonicalHorizon_splitCountList, Function.comp_def,
    firstCountLaw, tailCountLaw, source, tailMeans, firstMean, rate,
    arrivalProbability] using hresult

/-- The two disjoint marked samples have independent thinned split counts.
This is the two-interval finite-dimensional increment law before translating
the thinning means to their physical arrival and potential-service rates. -/
theorem manyServerMarkedCanonicalHorizon_intervalSplitCounts_hasLaw
    {initial : PMF ℕ} (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers : ℕ) (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    {start duration : ℝ} (hstart : 0 ≤ start) (hduration : 0 ≤ duration) :
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    let firstMean : ℝ≥0 := ⟨rate * start, mul_nonneg
      (le_of_lt (manyServerUniformizationRate_pos trafficIntensity serviceRate
        servers hservers hserviceRate)) hstart⟩
    let secondMean : ℝ≥0 := ⟨rate * duration, mul_nonneg
      (le_of_lt (manyServerUniformizationRate_pos trafficIntensity serviceRate
        servers hservers hserviceRate)) hduration⟩
    let arrivalProbability := uniformizedBirthProbability trafficIntensity
    HasLaw (fun value : ((ℕ → ℕ × Bool) × (ℕ → ℝ)) =>
      (FiniteHorizonMarkedPoisson.splitCounts
        (manyServerMarkedCanonicalHorizonSample start value),
        FiniteHorizonMarkedPoisson.splitCounts
          (manyServerMarkedCanonicalIntervalSample start duration value)))
      (Measure.prod
        ((ProbabilityTheory.poissonMeasure (firstMean * arrivalProbability)).prod
          (ProbabilityTheory.poissonMeasure (firstMean * (1 - arrivalProbability))))
        ((ProbabilityTheory.poissonMeasure (secondMean * arrivalProbability)).prod
          (ProbabilityTheory.poissonMeasure (secondMean * (1 - arrivalProbability)))))
      ((stationaryTrajMeasure
        (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
        (manyServerMarkedStateUniformizationMeasureKernel
          trafficIntensity servers hservers)).prod
        (PoissonProcess.exponentialInterarrivalMeasure rate)) := by
  dsimp only
  let rate : ℝ := manyServerUniformizationRate
    (trafficIntensity : ℝ) serviceRate servers
  let firstMean : ℝ≥0 := ⟨rate * start, mul_nonneg
    (le_of_lt (manyServerUniformizationRate_pos trafficIntensity serviceRate
      servers hservers hserviceRate)) hstart⟩
  let secondMean : ℝ≥0 := ⟨rate * duration, mul_nonneg
    (le_of_lt (manyServerUniformizationRate_pos trafficIntensity serviceRate
      servers hservers hserviceRate)) hduration⟩
  let arrivalProbability : ℝ≥0 := uniformizedBirthProbability trafficIntensity
  let arrivalProbability_le_one : arrivalProbability ≤ 1 :=
    uniformizedBirthProbability_le_one trafficIntensity
  let firstLaw : Measure FiniteHorizonMarkedPoisson.Sample :=
    (FiniteHorizonMarkedPoisson.jointPMF firstMean arrivalProbability
      arrivalProbability_le_one).toMeasure
  let secondLaw : Measure FiniteHorizonMarkedPoisson.Sample :=
    (FiniteHorizonMarkedPoisson.jointPMF secondMean arrivalProbability
      arrivalProbability_le_one).toMeasure
  let firstSplitLaw : Measure (ℕ × ℕ) :=
    (ProbabilityTheory.poissonMeasure (firstMean * arrivalProbability)).prod
      (ProbabilityTheory.poissonMeasure (firstMean * (1 - arrivalProbability)));
  let secondSplitLaw : Measure (ℕ × ℕ) :=
    (ProbabilityTheory.poissonMeasure (secondMean * arrivalProbability)).prod
      (ProbabilityTheory.poissonMeasure (secondMean * (1 - arrivalProbability)));
  let rateSource : Measure ((ℕ → ℕ × Bool) × (ℕ → ℝ)) :=
    (stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)).prod
      (PoissonProcess.exponentialInterarrivalMeasure rate)
  have hsamples : HasLaw (fun value : ((ℕ → ℕ × Bool) × (ℕ → ℝ)) =>
      (manyServerMarkedCanonicalHorizonSample start value,
        manyServerMarkedCanonicalIntervalSample start duration value))
      (firstLaw.prod secondLaw) rateSource := by
    simpa [firstLaw, secondLaw, rateSource, rate, firstMean, secondMean,
      arrivalProbability, arrivalProbability_le_one] using
      (manyServerMarkedCanonicalHorizon_intervalSample_hasLaw
        (initial := initial) trafficIntensity serviceRate servers hservers hserviceRate
        hstart hduration)
  have hfirst : HasLaw FiniteHorizonMarkedPoisson.splitCounts firstSplitLaw firstLaw := by
    simpa [firstSplitLaw, firstLaw] using
      (FiniteHorizonMarkedPoisson.splitCounts_hasLaw firstMean arrivalProbability
        arrivalProbability_le_one)
  have hsecond : HasLaw FiniteHorizonMarkedPoisson.splitCounts secondSplitLaw secondLaw := by
    simpa [secondSplitLaw, secondLaw] using
      (FiniteHorizonMarkedPoisson.splitCounts_hasLaw secondMean arrivalProbability
        arrivalProbability_le_one)
  have htransform : HasLaw
      (Prod.map FiniteHorizonMarkedPoisson.splitCounts
        FiniteHorizonMarkedPoisson.splitCounts)
      (firstSplitLaw.prod secondSplitLaw) (firstLaw.prod secondLaw) := by
    refine ⟨(measurable_of_countable FiniteHorizonMarkedPoisson.splitCounts).prodMap
      (measurable_of_countable FiniteHorizonMarkedPoisson.splitCounts) |>.aemeasurable, ?_⟩
    calc
      Measure.map (Prod.map FiniteHorizonMarkedPoisson.splitCounts
          FiniteHorizonMarkedPoisson.splitCounts) (firstLaw.prod secondLaw) =
          (Measure.map FiniteHorizonMarkedPoisson.splitCounts firstLaw).prod
            (Measure.map FiniteHorizonMarkedPoisson.splitCounts secondLaw) :=
        (Measure.map_prod_map firstLaw secondLaw
          (measurable_of_countable FiniteHorizonMarkedPoisson.splitCounts)
          (measurable_of_countable FiniteHorizonMarkedPoisson.splitCounts)).symm
      _ = firstSplitLaw.prod secondSplitLaw := by rw [hfirst.map_eq, hsecond.map_eq]
  have hresult := htransform.comp hsamples
  simpa [firstSplitLaw, secondSplitLaw, rateSource, rate, firstMean, secondMean,
    arrivalProbability, arrivalProbability_le_one] using hresult

/-- The physical-interval marked sample is Borel measurable. -/
theorem measurable_manyServerMarkedCanonicalIntervalSample
    (start duration : ℝ) :
    Measurable (manyServerMarkedCanonicalIntervalSample start duration) := by
  exact (measurable_manyServerMarkedFreshHorizonSample duration).comp
    (measurable_manyServerMarkedCanonicalFutureDriver start)

/-- Every nonnegative deterministic physical interval has the literal marked
Poisson sample law with the actual arrival-versus-potential-service marks. -/
theorem manyServerMarkedCanonicalIntervalSample_hasLaw
    {initial : PMF ℕ} (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers : ℕ) (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    {start duration : ℝ} (hstart : 0 ≤ start) (hduration : 0 ≤ duration) :
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    let mean : ℝ≥0 := ⟨rate * duration, mul_nonneg
      (le_of_lt (manyServerUniformizationRate_pos trafficIntensity serviceRate
        servers hservers hserviceRate)) hduration⟩
    let arrivalProbability := uniformizedBirthProbability trafficIntensity
    HasLaw (manyServerMarkedCanonicalIntervalSample start duration)
      (FiniteHorizonMarkedPoisson.jointPMF mean arrivalProbability
        (uniformizedBirthProbability_le_one trafficIntensity)).toMeasure
      ((stationaryTrajMeasure
        (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
        (manyServerMarkedStateUniformizationMeasureKernel
          trafficIntensity servers hservers)).prod
        (PoissonProcess.exponentialInterarrivalMeasure rate)) := by
  dsimp only
  let rate : ℝ := manyServerUniformizationRate
    (trafficIntensity : ℝ) serviceRate servers
  let mean : ℝ≥0 := ⟨rate * duration, mul_nonneg
    (le_of_lt (manyServerUniformizationRate_pos trafficIntensity serviceRate
      servers hservers hserviceRate)) hduration⟩
  let arrivalProbability : ℝ≥0 := uniformizedBirthProbability trafficIntensity
  let arrivalProbability_le_one : arrivalProbability ≤ 1 :=
    uniformizedBirthProbability_le_one trafficIntensity
  let markLaw : Measure Bool :=
    (manyServerUniformizationArrivalMark trafficIntensity).toMeasure
  let trajectory : Measure (ℕ → ℕ × Bool) := stationaryTrajMeasure
    (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
    (manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers)
  let gaps : Measure (ℕ → ℝ) :=
    PoissonProcess.exponentialInterarrivalMeasure rate
  let source : Measure ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := trajectory.prod gaps
  have hfuture : HasLaw (manyServerMarkedCanonicalFutureDriver start)
      (gaps.prod (IIDStream.measure markLaw)) source := by
    simpa [source, trajectory, gaps, markLaw, rate] using
      (manyServerMarkedCanonicalFutureDriver_hasLaw
        (initial := initial) trafficIntensity serviceRate servers hservers hserviceRate hstart)
  have hsample : HasLaw (manyServerMarkedFreshHorizonSample duration)
      (FiniteHorizonMarkedPoisson.jointPMF mean arrivalProbability
        arrivalProbability_le_one).toMeasure
      (gaps.prod (IIDStream.measure markLaw)) := by
    simpa [gaps, markLaw, rate, mean, arrivalProbability,
      arrivalProbability_le_one] using
      (manyServerMarkedFreshHorizonSample_hasLaw
        trafficIntensity serviceRate servers hservers hserviceRate hduration)
  simpa [manyServerMarkedCanonicalIntervalSample, Function.comp_def,
    source, trajectory, gaps, markLaw, rate, mean, arrivalProbability,
    arrivalProbability_le_one] using hsample.comp hfuture

/-- The total-event coordinate of the actual interval sample is the literal
increment of the original canonical potential-event clock, outside a null
set.  The marks do not enter this identity; they remain available in the same
sample for the subsequent marked-event decomposition. -/
theorem ae_manyServerMarkedCanonicalIntervalSample_total_eq_clockIncrement
    {initial : PMF ℕ} (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers : ℕ) (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    {start duration : ℝ} (hduration : 0 ≤ duration) :
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    ∀ᵐ value ∂((stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)).prod
      (PoissonProcess.exponentialInterarrivalMeasure rate)),
      FiniteHorizonMarkedPoisson.total
        (manyServerMarkedCanonicalIntervalSample start duration value) =
        PoissonProcess.canonicalRenewalCount (start + duration) value.2 -
          PoissonProcess.canonicalRenewalCount start value.2 := by
  dsimp only
  let rate : ℝ := manyServerUniformizationRate
    (trafficIntensity : ℝ) serviceRate servers
  let trajectory : Measure (ℕ → ℕ × Bool) := stationaryTrajMeasure
    (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
    (manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers)
  let gaps : Measure (ℕ → ℝ) :=
    PoissonProcess.exponentialInterarrivalMeasure rate
  let source : Measure ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := trajectory.prod gaps
  have hrate : 0 < rate := by
    exact manyServerUniformizationRate_pos trafficIntensity serviceRate
      servers hservers hserviceRate
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsProbabilityMeasure gaps :=
    PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  change ∀ᵐ value ∂source,
    FiniteHorizonMarkedPoisson.total
      (manyServerMarkedCanonicalIntervalSample start duration value) =
      PoissonProcess.canonicalRenewalCount (start + duration) value.2 -
        PoissonProcess.canonicalRenewalCount start value.2
  refine ae_of_ae_map (μ := source) (f := Prod.snd)
    (p := fun gaps : ℕ → ℝ =>
      PoissonProcess.canonicalRenewalCount duration
        (PoissonProcess.residualTail start gaps) =
        PoissonProcess.canonicalRenewalCount (start + duration) gaps -
          PoissonProcess.canonicalRenewalCount start gaps)
    measurable_snd.aemeasurable ?_
  rw [show Measure.map Prod.snd source = gaps by
    dsimp [source]
    rw [Measure.map_snd_prod, measure_univ, one_smul]]
  filter_upwards [PoissonProcess.ae_canonicalRenewalCount_increment_eq_residualTailCount
    hrate start duration hduration] with gaps hgaps
  simpa [manyServerMarkedCanonicalIntervalSample,
    manyServerMarkedFreshHorizonSample, manyServerMarkedCanonicalFutureDriver,
    FiniteHorizonMarkedPoisson.total] using hgaps.symm

/-- The number of arrival-mark events up to a canonical clock horizon. -/
def manyServerMarkedCanonicalArrivalCount (time : ℝ) :
    ((ℕ → ℕ × Bool) × (ℕ → ℝ)) → ℕ :=
  FiniteHorizonMarkedPoisson.kept ∘
    manyServerMarkedCanonicalHorizonSample time

/-- The number of potential-service-mark events up to a canonical clock
horizon. -/
def manyServerMarkedCanonicalPotentialServiceCount (time : ℝ) :
    ((ℕ → ℕ × Bool) × (ℕ → ℝ)) → ℕ :=
  FiniteHorizonMarkedPoisson.discarded ∘
    manyServerMarkedCanonicalHorizonSample time

/-- Canonical arrival counts use only the exponential clock and retained mark
stream, not the queue-state coordinate. -/
theorem manyServerMarkedCanonicalArrivalCount_eq_fresh_comp_driverFactors
    (time : ℝ) :
    manyServerMarkedCanonicalArrivalCount time =
      manyServerMarkedFreshArrivalCount time ∘ manyServerMarkedCanonicalDriverFactors := by
  rfl

/-- Canonical potential-service counts use only the exponential clock and
retained mark stream, not the queue-state coordinate. -/
theorem manyServerMarkedCanonicalPotentialServiceCount_eq_fresh_comp_driverFactors
    (time : ℝ) :
    manyServerMarkedCanonicalPotentialServiceCount time =
      manyServerMarkedFreshPotentialServiceCount time ∘
        manyServerMarkedCanonicalDriverFactors := by
  rfl

/-- The canonical arrival count is the arrival-mark prefix evaluated at the
canonical renewal-clock index. -/
theorem manyServerMarkedCanonicalArrivalCount_eq_prefix
    (time : ℝ) (value : (ℕ → ℕ × Bool) × (ℕ → ℝ)) :
    manyServerMarkedCanonicalArrivalCount time value =
      manyServerMarkedStateArrivalPrefix value.1
        (PoissonProcess.canonicalRenewalCount time value.2) := by
  unfold manyServerMarkedCanonicalArrivalCount
    manyServerMarkedCanonicalHorizonSample Function.comp
  simpa [FiniteHorizonMarkedPoisson.kept] using
    (manyServerMarkedStateArrivalPrefix_eq_keptInMarks value.1 _).symm

/-- The canonical potential-service count is the potential-service-mark
prefix evaluated at the canonical renewal-clock index. -/
theorem manyServerMarkedCanonicalPotentialServiceCount_eq_prefix
    (time : ℝ) (value : (ℕ → ℕ × Bool) × (ℕ → ℝ)) :
    manyServerMarkedCanonicalPotentialServiceCount time value =
      manyServerMarkedStatePotentialServicePrefix value.1
        (PoissonProcess.canonicalRenewalCount time value.2) := by
  unfold manyServerMarkedCanonicalPotentialServiceCount
    manyServerMarkedCanonicalHorizonSample Function.comp
  simpa [FiniteHorizonMarkedPoisson.discarded] using
    (manyServerMarkedStatePotentialServicePrefix_eq_discardedInMarks value.1 _).symm

/-- Almost surely, the marked arrival count is monotone in physical time.
This combines the pathwise monotonicity of finite arrival prefixes with the
canonical renewal clock's monotonicity. -/
theorem ae_forall_monotone_manyServerMarkedCanonicalArrivalCount_from_initial
    {initial : PMF ℕ} (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers : ℕ) (hservers : 0 < servers) (hserviceRate : 0 < serviceRate) :
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    ∀ᵐ value ∂((stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)).prod
      (PoissonProcess.exponentialInterarrivalMeasure rate)),
      Monotone (fun time : ℝ =>
        manyServerMarkedCanonicalArrivalCount time value) := by
  dsimp only
  let rate : ℝ := manyServerUniformizationRate
    (trafficIntensity : ℝ) serviceRate servers
  let trajectory : Measure (ℕ → ℕ × Bool) := stationaryTrajMeasure
    (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
    (manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers)
  let gaps : Measure (ℕ → ℝ) :=
    PoissonProcess.exponentialInterarrivalMeasure rate
  let source : Measure ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := trajectory.prod gaps
  have hrate : 0 < rate :=
    manyServerUniformizationRate_pos trafficIntensity serviceRate servers hservers hserviceRate
  letI : IsProbabilityMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure := by
    infer_instance
  letI : IsMarkovKernel
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers) := by
    infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsProbabilityMeasure gaps := by
    dsimp [gaps]
    exact PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  have hclock : ∀ᵐ value ∂source,
      Monotone (fun time : ℝ =>
        PoissonProcess.canonicalRenewalCount time value.2) := by
    refine ae_of_ae_map (μ := source) (f := Prod.snd)
      (p := fun gap : ℕ → ℝ => Monotone (fun time : ℝ =>
        PoissonProcess.canonicalRenewalCount time gap))
      measurable_snd.aemeasurable ?_
    rw [Measure.map_snd_prod, measure_univ, one_smul]
    simpa [gaps] using PoissonProcess.ae_canonicalRenewalCount_monotone hrate
  change ∀ᵐ value ∂source,
    Monotone (fun time : ℝ => manyServerMarkedCanonicalArrivalCount time value)
  filter_upwards [hclock] with value hclockValue
  intro first second hfirstsecond
  change manyServerMarkedCanonicalArrivalCount first value ≤
    manyServerMarkedCanonicalArrivalCount second value
  rw [manyServerMarkedCanonicalArrivalCount_eq_prefix,
    manyServerMarkedCanonicalArrivalCount_eq_prefix]
  exact monotone_manyServerMarkedStateArrivalPrefix value.1
    (hclockValue hfirstsecond)

/-- Almost surely, the marked potential-service count is monotone in physical
time.  This combines the pathwise monotonicity of finite potential-service
prefixes with the canonical renewal clock's monotonicity. -/
theorem ae_forall_monotone_manyServerMarkedCanonicalPotentialServiceCount_from_initial
    {initial : PMF ℕ} (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers : ℕ) (hservers : 0 < servers) (hserviceRate : 0 < serviceRate) :
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    ∀ᵐ value ∂((stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)).prod
      (PoissonProcess.exponentialInterarrivalMeasure rate)),
      Monotone (fun time : ℝ =>
        manyServerMarkedCanonicalPotentialServiceCount time value) := by
  dsimp only
  let rate : ℝ := manyServerUniformizationRate
    (trafficIntensity : ℝ) serviceRate servers
  let trajectory : Measure (ℕ → ℕ × Bool) := stationaryTrajMeasure
    (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
    (manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers)
  let gaps : Measure (ℕ → ℝ) :=
    PoissonProcess.exponentialInterarrivalMeasure rate
  let source : Measure ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := trajectory.prod gaps
  have hrate : 0 < rate :=
    manyServerUniformizationRate_pos trafficIntensity serviceRate servers hservers hserviceRate
  letI : IsProbabilityMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure := by
    infer_instance
  letI : IsMarkovKernel
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers) := by
    infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsProbabilityMeasure gaps := by
    dsimp [gaps]
    exact PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  have hclock : ∀ᵐ value ∂source,
      Monotone (fun time : ℝ =>
        PoissonProcess.canonicalRenewalCount time value.2) := by
    refine ae_of_ae_map (μ := source) (f := Prod.snd)
      (p := fun gap : ℕ → ℝ => Monotone (fun time : ℝ =>
        PoissonProcess.canonicalRenewalCount time gap))
      measurable_snd.aemeasurable ?_
    rw [Measure.map_snd_prod, measure_univ, one_smul]
    simpa [gaps] using PoissonProcess.ae_canonicalRenewalCount_monotone hrate
  change ∀ᵐ value ∂source,
    Monotone (fun time : ℝ => manyServerMarkedCanonicalPotentialServiceCount time value)
  filter_upwards [hclock] with value hclockValue
  intro first second hfirstsecond
  change manyServerMarkedCanonicalPotentialServiceCount first value ≤
    manyServerMarkedCanonicalPotentialServiceCount second value
  rw [manyServerMarkedCanonicalPotentialServiceCount_eq_prefix,
    manyServerMarkedCanonicalPotentialServiceCount_eq_prefix]
  exact monotone_manyServerMarkedStatePotentialServicePrefix value.1
    (hclockValue hfirstsecond)

/-- The pair of marked arrival and potential-service counts as a function of
physical time. -/
noncomputable def manyServerMarkedCanonicalArrivalPotentialCountOnReal
    (value : (ℕ → ℕ × Bool) × (ℕ → ℝ)) : ℝ → ℕ × ℕ :=
  fun time =>
    (manyServerMarkedCanonicalArrivalCount time value,
      manyServerMarkedCanonicalPotentialServiceCount time value)

/-- The marked arrival/potential-service count pair has an almost surely
càdlàg physical-time trajectory. -/
theorem ae_isCadlagPath_manyServerMarkedCanonicalArrivalPotentialCountOnReal
    {initial : PMF ℕ} (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers : ℕ) (hservers : 0 < servers) (hserviceRate : 0 < serviceRate) :
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    let trajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    let gaps := PoissonProcess.exponentialInterarrivalMeasure rate
    ∀ᵐ value ∂trajectory.prod gaps,
      IsCadlagPath
        (manyServerMarkedCanonicalArrivalPotentialCountOnReal value) := by
  let rate : ℝ := manyServerUniformizationRate
    (trafficIntensity : ℝ) serviceRate servers
  let trajectory : Measure (ℕ → ℕ × Bool) := stationaryTrajMeasure
    (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
    (manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers)
  let gaps : Measure (ℕ → ℝ) :=
    PoissonProcess.exponentialInterarrivalMeasure rate
  let source : Measure ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := trajectory.prod gaps
  have hrate : 0 < rate := by
    exact manyServerUniformizationRate_pos trafficIntensity serviceRate
      servers hservers hserviceRate
  letI : IsProbabilityMeasure (manyServerMarkedStatePMF initial trafficIntensity).toMeasure := by
    unfold manyServerMarkedStatePMF
    infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsProbabilityMeasure gaps :=
    PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  have hclock : ∀ᵐ gap ∂gaps,
      IsCadlagPath (fun time : ℝ =>
        PoissonProcess.canonicalRenewalCount time gap) :=
    PoissonProcess.ae_isCadlagPath_canonicalRenewalCount hrate
  have hlift : ∀ᵐ value ∂source,
      IsCadlagPath (fun time : ℝ =>
        PoissonProcess.canonicalRenewalCount time value.2) := by
    refine ae_of_ae_map
      (μ := source) (f := Prod.snd)
      (p := fun gap => IsCadlagPath (fun time : ℝ =>
        PoissonProcess.canonicalRenewalCount time gap))
      measurable_snd.aemeasurable ?_
    rw [Measure.map_snd_prod, measure_univ, one_smul]
    exact hclock
  filter_upwards [hlift] with value hvalue
  have hpair := IsCadlagPath.continuous_comp hvalue
    (continuous_of_discreteTopology : Continuous (fun index : ℕ =>
      (FiniteHorizonMarkedPoisson.kept ⟨index, fun i => (value.1 i).2⟩,
        FiniteHorizonMarkedPoisson.discarded ⟨index, fun i => (value.1 i).2⟩)))
  simpa [manyServerMarkedCanonicalArrivalPotentialCountOnReal,
    manyServerMarkedCanonicalArrivalCount,
    manyServerMarkedCanonicalPotentialServiceCount,
    manyServerMarkedCanonicalHorizonSample, Function.comp_def] using hpair

/-- The completed-service count of the actual marked embedded path up to a
canonical clock horizon.  Unlike potential-service marks, this counts only
events that find a busy server. -/
def manyServerMarkedCanonicalDepartureCount (time : ℝ) :
    ((ℕ → ℕ × Bool) × (ℕ → ℝ)) → ℕ :=
  fun value => manyServerMarkedStateDeparturePrefix value.1
    (PoissonProcess.canonicalRenewalCount time value.2)

/-- Potential-service events that do not produce a completed service. -/
def manyServerMarkedCanonicalUnrealizedPotentialServiceCount (time : ℝ) :
    ((ℕ → ℕ × Bool) × (ℕ → ℝ)) → ℕ :=
  fun value => manyServerMarkedCanonicalPotentialServiceCount time value -
    manyServerMarkedCanonicalDepartureCount time value

/-- The centered unrealized-potential-service correction evaluated at the
independent canonical Poisson-clock index. -/
def manyServerMarkedCanonicalCenteredUnrealizedPotentialServiceCorrection
    (servers : ℕ) (time : ℝ) :
    ((ℕ → ℕ × Bool) × (ℕ → ℝ)) → ℝ :=
  fun value => manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum
    servers (PoissonProcess.canonicalRenewalCount time value.2) value.1

/-- The centered unrealized-potential-service correction stopped when the
predictable arrival-minus-potential-service lower barrier is first reached. -/
def manyServerMarkedCanonicalStoppedUnrealizedPotentialServiceCorrection
    (servers lowerThreshold : ℕ) (time : ℝ) :
    ((ℕ → ℕ × Bool) × (ℕ → ℝ)) → ℝ :=
  fun value => manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum
    servers lowerThreshold (PoissonProcess.canonicalRenewalCount time value.2) value.1

/-- Before the embedded lower-barrier exit, the stopped canonical correction
is exactly the original canonical correction. -/
theorem manyServerMarkedCanonicalStoppedUnrealizedPotentialServiceCorrection_eq_centered_of_clock_count_le_lowerExit
    (servers lowerThreshold : ℕ) (time : ℝ)
    (value : (ℕ → ℕ × Bool) × (ℕ → ℝ))
    (hbefore : (PoissonProcess.canonicalRenewalCount time value.2 : ENat) ≤
      manyServerMarkedStateArrivalPotentialLowerExitTime lowerThreshold value.1) :
    manyServerMarkedCanonicalStoppedUnrealizedPotentialServiceCorrection
      servers lowerThreshold time value =
      manyServerMarkedCanonicalCenteredUnrealizedPotentialServiceCorrection
        servers time value := by
  exact manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum_eq_centered_of_le_lowerExit
    servers lowerThreshold (PoissonProcess.canonicalRenewalCount time value.2) value.1 hbefore

/-- The embedded-chain predictable compensator of unrealized potential
service, evaluated at the independent canonical clock index.  This is not by
itself identified with the continuous-time compensator (an integral against
physical time); that comparison requires a separate clock-residual argument.
-/
def manyServerMarkedCanonicalUnrealizedPotentialServiceCompensator
    (servers : ℕ) (time : ℝ) :
    ((ℕ → ℕ × Bool) × (ℕ → ℝ)) → ℝ :=
  fun value => manyServerMarkedStateUnrealizedPotentialServiceCompensatorPrefix
    servers value.1 (PoissonProcess.canonicalRenewalCount time value.2)

/-- Time-changing an arbitrary embedded marked-path observable by the
independent canonical renewal clock gives an almost surely càdlàg physical-time
path.  This is a regularity statement only; it supplies neither a Markov nor a
martingale assertion for the time-changed observable. -/
theorem ae_isCadlagPath_manyServerMarkedCanonical_clock_comp
    {Target : Type*} [TopologicalSpace Target]
    {initial : PMF ℕ} (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers : ℕ) (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    (observable : (ℕ → ℕ × Bool) → ℕ → Target) :
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    let trajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    let gaps := PoissonProcess.exponentialInterarrivalMeasure rate
    ∀ᵐ value ∂trajectory.prod gaps,
      IsCadlagPath (fun time : ℝ =>
        observable value.1 (PoissonProcess.canonicalRenewalCount time value.2)) := by
  let rate : ℝ := manyServerUniformizationRate
    (trafficIntensity : ℝ) serviceRate servers
  let trajectory : Measure (ℕ → ℕ × Bool) := stationaryTrajMeasure
    (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
    (manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers)
  let gaps : Measure (ℕ → ℝ) := PoissonProcess.exponentialInterarrivalMeasure rate
  let source : Measure ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := trajectory.prod gaps
  have hrate : 0 < rate := by
    exact manyServerUniformizationRate_pos trafficIntensity serviceRate
      servers hservers hserviceRate
  letI : IsProbabilityMeasure (manyServerMarkedStatePMF initial trafficIntensity).toMeasure := by
    unfold manyServerMarkedStatePMF
    infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsProbabilityMeasure gaps :=
    PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  have hclock : ∀ᵐ gap ∂gaps,
      IsCadlagPath (fun time : ℝ =>
        PoissonProcess.canonicalRenewalCount time gap) :=
    PoissonProcess.ae_isCadlagPath_canonicalRenewalCount hrate
  have hlift : ∀ᵐ value ∂source,
      IsCadlagPath (fun time : ℝ =>
        PoissonProcess.canonicalRenewalCount time value.2) := by
    refine ae_of_ae_map (μ := source) (f := Prod.snd)
      (p := fun gap => IsCadlagPath (fun time : ℝ =>
        PoissonProcess.canonicalRenewalCount time gap))
      measurable_snd.aemeasurable ?_
    rw [Measure.map_snd_prod, measure_univ, one_smul]
    exact hclock
  filter_upwards [hlift] with value hvalue
  exact IsCadlagPath.continuous_comp hvalue
    (continuous_of_discreteTopology : Continuous (fun index => observable value.1 index))

/-- The all-real-time canonical embedded compensator, obtained by
time-changing the embedded unrealized-service compensator. -/
noncomputable def manyServerMarkedCanonicalUnrealizedPotentialServiceCompensatorOnReal
    (servers : ℕ) (value : (ℕ → ℕ × Bool) × (ℕ → ℝ)) : ℝ → ℝ :=
  fun time => manyServerMarkedCanonicalUnrealizedPotentialServiceCompensator
    servers time value

/-- The time-changed embedded compensator has almost surely càdlàg
physical-time paths. -/
theorem ae_isCadlagPath_manyServerMarkedCanonicalUnrealizedPotentialServiceCompensatorOnReal
    {initial : PMF ℕ} (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers : ℕ) (hservers : 0 < servers) (hserviceRate : 0 < serviceRate) :
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    let trajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    let gaps := PoissonProcess.exponentialInterarrivalMeasure rate
    ∀ᵐ value ∂trajectory.prod gaps,
      IsCadlagPath
        (manyServerMarkedCanonicalUnrealizedPotentialServiceCompensatorOnReal
          servers value) := by
  simpa [manyServerMarkedCanonicalUnrealizedPotentialServiceCompensatorOnReal,
    manyServerMarkedCanonicalUnrealizedPotentialServiceCompensator] using
    (ae_isCadlagPath_manyServerMarkedCanonical_clock_comp
      (initial := initial) trafficIntensity serviceRate servers hservers hserviceRate
      (fun path index =>
        manyServerMarkedStateUnrealizedPotentialServiceCompensatorPrefix
          servers path index))

/-- The all-real-time version of the centered unrealized-potential-service
correction, obtained by time-changing its embedded partial sums with the
canonical renewal count. -/
noncomputable def manyServerMarkedCanonicalCenteredUnrealizedPotentialServiceCorrectionOnReal
    (servers : ℕ) (value : (ℕ → ℕ × Bool) × (ℕ → ℝ)) : ℝ → ℝ :=
  fun time => manyServerMarkedCanonicalCenteredUnrealizedPotentialServiceCorrection
    servers time value

/-- The all-real-time lower-barrier-stopped centered correction. -/
noncomputable def manyServerMarkedCanonicalStoppedUnrealizedPotentialServiceCorrectionOnReal
    (servers lowerThreshold : ℕ) (value : (ℕ → ℕ × Bool) × (ℕ → ℝ)) : ℝ → ℝ :=
  fun time => manyServerMarkedCanonicalStoppedUnrealizedPotentialServiceCorrection
    servers lowerThreshold time value

/-- The lower-barrier-stopped centered correction has almost surely càdlàg
physical-time paths. -/
theorem ae_isCadlagPath_manyServerMarkedCanonicalStoppedUnrealizedPotentialServiceCorrectionOnReal
    {initial : PMF ℕ} (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers lowerThreshold : ℕ) (hservers : 0 < servers) (hserviceRate : 0 < serviceRate) :
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    let trajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    let gaps := PoissonProcess.exponentialInterarrivalMeasure rate
    ∀ᵐ value ∂trajectory.prod gaps,
      IsCadlagPath
        (manyServerMarkedCanonicalStoppedUnrealizedPotentialServiceCorrectionOnReal
          servers lowerThreshold value) := by
  simpa [manyServerMarkedCanonicalStoppedUnrealizedPotentialServiceCorrectionOnReal,
    manyServerMarkedCanonicalStoppedUnrealizedPotentialServiceCorrection] using
    (ae_isCadlagPath_manyServerMarkedCanonical_clock_comp
      (initial := initial) trafficIntensity serviceRate servers hservers hserviceRate
      (fun path index =>
        manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum
          servers lowerThreshold index path))

/-- The centered unrealized-potential-service correction has almost surely
càdlàg real-time paths. -/
theorem ae_isCadlagPath_manyServerMarkedCanonicalCenteredUnrealizedPotentialServiceCorrectionOnReal
    {initial : PMF ℕ} (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers : ℕ) (hservers : 0 < servers) (hserviceRate : 0 < serviceRate) :
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    let trajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    let gaps := PoissonProcess.exponentialInterarrivalMeasure rate
    ∀ᵐ value ∂trajectory.prod gaps,
      IsCadlagPath
        (manyServerMarkedCanonicalCenteredUnrealizedPotentialServiceCorrectionOnReal
          servers value) := by
  let rate : ℝ := manyServerUniformizationRate
    (trafficIntensity : ℝ) serviceRate servers
  let trajectory : Measure (ℕ → ℕ × Bool) := stationaryTrajMeasure
    (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
    (manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers)
  let gaps : Measure (ℕ → ℝ) :=
    PoissonProcess.exponentialInterarrivalMeasure rate
  let source : Measure ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := trajectory.prod gaps
  have hrate : 0 < rate := by
    exact manyServerUniformizationRate_pos trafficIntensity serviceRate
      servers hservers hserviceRate
  letI : IsProbabilityMeasure (manyServerMarkedStatePMF initial trafficIntensity).toMeasure := by
    unfold manyServerMarkedStatePMF
    infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsProbabilityMeasure gaps :=
    PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  have hclock : ∀ᵐ gap ∂gaps,
      IsCadlagPath (fun time : ℝ =>
        PoissonProcess.canonicalRenewalCount time gap) :=
    PoissonProcess.ae_isCadlagPath_canonicalRenewalCount hrate
  have hlift : ∀ᵐ value ∂source,
      IsCadlagPath (fun time : ℝ =>
        PoissonProcess.canonicalRenewalCount time value.2) := by
    refine ae_of_ae_map
      (μ := source) (f := Prod.snd)
      (p := fun gap => IsCadlagPath (fun time : ℝ =>
        PoissonProcess.canonicalRenewalCount time gap))
      measurable_snd.aemeasurable ?_
    rw [Measure.map_snd_prod, measure_univ, one_smul]
    exact hclock
  filter_upwards [hlift] with value hvalue
  have hcorrection := IsCadlagPath.continuous_comp hvalue
    (continuous_of_discreteTopology : Continuous (fun index =>
      manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum
        servers index value.1))
  simpa [manyServerMarkedCanonicalCenteredUnrealizedPotentialServiceCorrectionOnReal,
    manyServerMarkedCanonicalCenteredUnrealizedPotentialServiceCorrection,
    Function.comp_def] using hcorrection

/-- A total càdlàg-path version of the centered unrealized-potential-service
correction. Outside its càdlàg event it is the zero path. -/
noncomputable def manyServerMarkedCanonicalCenteredUnrealizedPotentialServiceCorrectionCadlagPath
    (servers : ℕ) (value : (ℕ → ℕ × Bool) × (ℕ → ℝ)) :
    CadlagPathOn ℝ ℝ (Set.Ici (0 : ℝ)) := by
  classical
  exact if hcadlag : IsCadlagOn (Set.Ici (0 : ℝ))
      (manyServerMarkedCanonicalCenteredUnrealizedPotentialServiceCorrectionOnReal
        servers value) then
    IsCadlagOn.toCadlagPathOn hcadlag
  else
    CadlagPathOn.constant (Set.Ici (0 : ℝ)) 0

/-- The total càdlàg-path version agrees almost surely with the concrete
centered correction at every real time. -/
theorem ae_forall_manyServerMarkedCanonicalCenteredUnrealizedPotentialServiceCorrectionCadlagPath_eq
    {initial : PMF ℕ} (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers : ℕ) (hservers : 0 < servers) (hserviceRate : 0 < serviceRate) :
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    let trajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    let gaps := PoissonProcess.exponentialInterarrivalMeasure rate
    ∀ᵐ value ∂trajectory.prod gaps, ∀ time : ℝ,
      manyServerMarkedCanonicalCenteredUnrealizedPotentialServiceCorrectionCadlagPath
        servers value time =
      manyServerMarkedCanonicalCenteredUnrealizedPotentialServiceCorrectionOnReal
        servers value time := by
  have hcadlag :=
    ae_isCadlagPath_manyServerMarkedCanonicalCenteredUnrealizedPotentialServiceCorrectionOnReal
      (initial := initial) trafficIntensity serviceRate servers hservers hserviceRate
  filter_upwards [hcadlag] with value hvalue
  intro time
  have hcadlagOn : IsCadlagOn (Set.Ici (0 : ℝ))
      (manyServerMarkedCanonicalCenteredUnrealizedPotentialServiceCorrectionOnReal
        servers value) := hvalue.on_of_isCadlagPath (Set.Ici 0)
  simp [manyServerMarkedCanonicalCenteredUnrealizedPotentialServiceCorrectionCadlagPath,
    hcadlagOn, IsCadlagOn.toCadlagPathOn]

/-- On a clock path whose count remains below `n` up to a horizon, every
centered correction coordinate before that horizon is bounded by the maximum
of the first `n` embedded partial sums. -/
theorem manyServerMarkedCanonicalCenteredUnrealizedPotentialServiceCorrection_sq_le_embeddedMaximum_of_clock_count_le
    (servers : ℕ) (value : (ℕ → ℕ × Bool) × (ℕ → ℝ)) (n : ℕ)
    {time horizon : ℝ}
    (hclock_mono : Monotone (fun u : ℝ =>
      PoissonProcess.canonicalRenewalCount u value.2))
    (htime : time ≤ horizon)
    (hcount : PoissonProcess.canonicalRenewalCount horizon value.2 ≤ n) :
    (manyServerMarkedCanonicalCenteredUnrealizedPotentialServiceCorrection
      servers time value) ^ 2 ≤
      (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun index =>
          (manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum
            servers index value.1) ^ 2) := by
  have hindex : PoissonProcess.canonicalRenewalCount time value.2 ≤ n :=
    (hclock_mono htime).trans hcount
  unfold manyServerMarkedCanonicalCenteredUnrealizedPotentialServiceCorrection
  exact Finset.le_sup'
    (s := Finset.range (n + 1))
    (f := fun index =>
      (manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum
        servers index value.1) ^ 2)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hindex))

/-- If the predictable lower barrier remains unhit through an embedded clock
cutoff, the original correction up to that physical-time cutoff is controlled
by the stopped embedded correction maximum. -/
theorem manyServerMarkedCanonicalCenteredUnrealizedPotentialServiceCorrection_sq_le_stoppedEmbeddedMaximum_of_clock_count_le_no_lowerExit
    (servers lowerThreshold : ℕ) (value : (ℕ → ℕ × Bool) × (ℕ → ℝ)) (n : ℕ)
    {time horizon : ℝ}
    (hclock_mono : Monotone (fun u : ℝ =>
      PoissonProcess.canonicalRenewalCount u value.2))
    (htime : time ≤ horizon)
    (hcount : PoissonProcess.canonicalRenewalCount horizon value.2 ≤ n)
    (hbefore : (n : ENat) ≤
      manyServerMarkedStateArrivalPotentialLowerExitTime lowerThreshold value.1) :
    (manyServerMarkedCanonicalCenteredUnrealizedPotentialServiceCorrection
      servers time value) ^ 2 ≤
      (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun index =>
          (manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum
            servers lowerThreshold index value.1) ^ 2) := by
  calc
    (manyServerMarkedCanonicalCenteredUnrealizedPotentialServiceCorrection
      servers time value) ^ 2 ≤
        (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          (fun index =>
            (manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum
              servers index value.1) ^ 2) :=
      manyServerMarkedCanonicalCenteredUnrealizedPotentialServiceCorrection_sq_le_embeddedMaximum_of_clock_count_le
        servers value n hclock_mono htime hcount
    _ = (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          (fun index =>
            (manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum
              servers lowerThreshold index value.1) ^ 2) :=
      maximalCenteredUnrealizedPotentialServicePartialSum_eq_stopped_of_le_lowerExit
        servers lowerThreshold n value.1 hbefore

/-- If the predictable lower barrier has not been reached by the *actual*
canonical clock count at a physical horizon, then every earlier original
correction coordinate is controlled by the stopped embedded maximum through
any deterministic cutoff above that clock count.  This is weaker, and more
useful for physical-time localization, than requiring the barrier to remain
unhit all the way through the deterministic cutoff. -/
theorem manyServerMarkedCanonicalCenteredUnrealizedPotentialServiceCorrection_sq_le_stoppedEmbeddedMaximum_of_clock_count_lt_lowerExit
    (servers lowerThreshold : ℕ) (value : (ℕ → ℕ × Bool) × (ℕ → ℝ)) (n : ℕ)
    {time horizon : ℝ}
    (hclock_mono : Monotone (fun u : ℝ =>
      PoissonProcess.canonicalRenewalCount u value.2))
    (htime : time ≤ horizon)
    (hcount : PoissonProcess.canonicalRenewalCount horizon value.2 ≤ n)
    (hbefore : (PoissonProcess.canonicalRenewalCount horizon value.2 : ENat) <
      manyServerMarkedStateArrivalPotentialLowerExitTime lowerThreshold value.1) :
    (manyServerMarkedCanonicalCenteredUnrealizedPotentialServiceCorrection
      servers time value) ^ 2 ≤
      (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun index =>
          (manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum
            servers lowerThreshold index value.1) ^ 2) := by
  have htime_count : PoissonProcess.canonicalRenewalCount time value.2 ≤
      PoissonProcess.canonicalRenewalCount horizon value.2 := hclock_mono htime
  have htime_exit : (PoissonProcess.canonicalRenewalCount time value.2 : ENat) ≤
      manyServerMarkedStateArrivalPotentialLowerExitTime lowerThreshold value.1 := by
    exact (show (PoissonProcess.canonicalRenewalCount time value.2 : ENat) ≤
      (PoissonProcess.canonicalRenewalCount horizon value.2 : ENat) from
      ENat.coe_le_coe.mpr htime_count).trans hbefore.le
  rw [← manyServerMarkedCanonicalStoppedUnrealizedPotentialServiceCorrection_eq_centered_of_clock_count_le_lowerExit
    servers lowerThreshold time value htime_exit]
  unfold manyServerMarkedCanonicalStoppedUnrealizedPotentialServiceCorrection
  exact Finset.le_sup'
    (s := Finset.range (n + 1))
    (f := fun index =>
      (manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum
        servers lowerThreshold index value.1) ^ 2)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le (htime_count.trans hcount)))

/-- Outside a null set of canonical clock paths, a deterministic clock cutoff
controls the centered correction simultaneously at every time up to the
horizon.  The statement is pathwise and makes no claim yet about the
probability of the cutoff event. -/
theorem ae_forall_manyServerMarkedCanonicalCenteredUnrealizedPotentialServiceCorrection_sq_le_embeddedMaximum_of_clock_count_le
    {initial : PMF ℕ} (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers : ℕ) (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    (horizon : ℝ) (n : ℕ) :
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    let trajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    let gaps := PoissonProcess.exponentialInterarrivalMeasure rate
    ∀ᵐ value ∂trajectory.prod gaps,
      PoissonProcess.canonicalRenewalCount horizon value.2 ≤ n →
        ∀ time : ℝ, time ≤ horizon →
          (manyServerMarkedCanonicalCenteredUnrealizedPotentialServiceCorrection
            servers time value) ^ 2 ≤
            (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
              (fun index =>
                (manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum
                  servers index value.1) ^ 2) := by
  dsimp only
  let rate : ℝ := manyServerUniformizationRate
    (trafficIntensity : ℝ) serviceRate servers
  let trajectory : Measure (ℕ → ℕ × Bool) := stationaryTrajMeasure
    (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
    (manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers)
  let gaps : Measure (ℕ → ℝ) :=
    PoissonProcess.exponentialInterarrivalMeasure rate
  have hrate : 0 < rate :=
    manyServerUniformizationRate_pos trafficIntensity serviceRate servers hservers hserviceRate
  letI : IsProbabilityMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure := by
    infer_instance
  letI : IsMarkovKernel
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers) := by
    infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsProbabilityMeasure gaps := by
    dsimp [gaps]
    exact PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsFiniteMeasure gaps := by infer_instance
  have hmono_gaps : ∀ᵐ gap ∂gaps,
      Monotone (fun time : ℝ => PoissonProcess.canonicalRenewalCount time gap) := by
    simpa [gaps] using PoissonProcess.ae_canonicalRenewalCount_monotone hrate
  have hmono : ∀ᵐ value ∂trajectory.prod gaps,
      Monotone (fun time : ℝ => PoissonProcess.canonicalRenewalCount time value.2) := by
    refine ae_of_ae_map (μ := trajectory.prod gaps) (f := Prod.snd)
      (p := fun gap : ℕ → ℝ =>
        Monotone (fun time : ℝ => PoissonProcess.canonicalRenewalCount time gap))
      measurable_snd.aemeasurable ?_
    rw [Measure.map_snd_prod, measure_univ, one_smul]
    exact hmono_gaps
  filter_upwards [hmono] with value hvalue hcount time htime
  exact manyServerMarkedCanonicalCenteredUnrealizedPotentialServiceCorrection_sq_le_embeddedMaximum_of_clock_count_le
    servers value n hvalue htime hcount

/-- Outside the canonical clock's null exceptional set, a clock cutoff and an
unhit embedded lower barrier jointly control every original correction
coordinate by the stopped embedded maximum. -/
theorem ae_forall_manyServerMarkedCanonicalCenteredUnrealizedPotentialServiceCorrection_sq_le_stoppedEmbeddedMaximum_of_clock_count_le_no_lowerExit
    {initial : PMF ℕ} (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers lowerThreshold : ℕ) (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    (horizon : ℝ) (n : ℕ) :
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    let trajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    let gaps := PoissonProcess.exponentialInterarrivalMeasure rate
    ∀ᵐ value ∂trajectory.prod gaps,
      PoissonProcess.canonicalRenewalCount horizon value.2 ≤ n →
        (n : ENat) ≤
          manyServerMarkedStateArrivalPotentialLowerExitTime lowerThreshold value.1 →
        ∀ time : ℝ, time ≤ horizon →
          (manyServerMarkedCanonicalCenteredUnrealizedPotentialServiceCorrection
            servers time value) ^ 2 ≤
            (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
              (fun index =>
                (manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum
                  servers lowerThreshold index value.1) ^ 2) := by
  dsimp only
  have hbase :=
    ae_forall_manyServerMarkedCanonicalCenteredUnrealizedPotentialServiceCorrection_sq_le_embeddedMaximum_of_clock_count_le
      (initial := initial) trafficIntensity serviceRate servers hservers hserviceRate horizon n
  filter_upwards [hbase] with value hbaseValue hcount hbefore time htime
  calc
    (manyServerMarkedCanonicalCenteredUnrealizedPotentialServiceCorrection
      servers time value) ^ 2 ≤
        (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          (fun index =>
            (manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum
              servers index value.1) ^ 2) := hbaseValue hcount time htime
    _ = (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          (fun index =>
            (manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum
              servers lowerThreshold index value.1) ^ 2) :=
      maximalCenteredUnrealizedPotentialServicePartialSum_eq_stopped_of_le_lowerExit
        servers lowerThreshold n value.1 hbefore

/-- The independent canonical potential-event clock has the first-moment
tail bound at every nonnegative physical horizon, also after coupling it to an
arbitrary marked embedded queue trajectory. -/
theorem real_mul_measure_manyServerMarkedCanonicalClockCount_ge_le
    {initial : PMF ℕ} (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers : ℕ) (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    {horizon threshold : ℝ} (hhorizon : 0 ≤ horizon) (hthreshold : 0 ≤ threshold) :
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    let trajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    let gaps := PoissonProcess.exponentialInterarrivalMeasure rate
    threshold * (trajectory.prod gaps).real
      {value | threshold ≤ (PoissonProcess.canonicalRenewalCount horizon value.2 : ℝ)} ≤
      rate * horizon := by
  dsimp only
  let rate : ℝ := manyServerUniformizationRate
    (trafficIntensity : ℝ) serviceRate servers
  let trajectory : Measure (ℕ → ℕ × Bool) := stationaryTrajMeasure
    (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
    (manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers)
  let gaps : Measure (ℕ → ℝ) :=
    PoissonProcess.exponentialInterarrivalMeasure rate
  let source : Measure ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := trajectory.prod gaps
  let event : Set (ℕ → ℝ) :=
    {gap | threshold ≤ (PoissonProcess.canonicalRenewalCount horizon gap : ℝ)}
  have hrate : 0 < rate :=
    manyServerUniformizationRate_pos trafficIntensity serviceRate servers hservers hserviceRate
  letI : IsProbabilityMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure := by
    infer_instance
  letI : IsMarkovKernel
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers) := by
    infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsProbabilityMeasure gaps := by
    dsimp [gaps]
    exact PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  have hevent_meas : MeasurableSet event := by
    dsimp [event]
    exact ((measurable_of_countable fun n : ℕ => (n : ℝ)).comp
      (PoissonProcess.measurable_canonicalRenewalCount horizon)) measurableSet_Ici
  have hpreserve : MeasurePreserving Prod.snd source gaps := by
    dsimp [source]
    exact measurePreserving_snd
  have hmeasure : source.real (Prod.snd ⁻¹' event) = gaps.real event := by
    rw [← hpreserve.map_eq]
    simp only [measureReal_def]
    rw [Measure.map_apply measurable_snd hevent_meas]
  have htail := PoissonProcess.real_mul_measure_canonicalRenewalCount_ge_le
    hrate hhorizon hthreshold
  change threshold * source.real (Prod.snd ⁻¹' event) ≤ rate * horizon
  rw [hmeasure]
  simpa [gaps, event] using htail

/-- The arbitrary-initial embedded Doob estimate transfers unchanged through
the independent canonical clock.  This controls the finite maximum of marked
embedded correction increments before it is combined with a clock cutoff. -/
theorem real_mul_measure_manyServerMarkedCanonicalEmbeddedMaximum_le_from_initial
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (serviceRate : ℝ) (servers : ℕ)
    (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    (threshold : ℝ≥0) (n : ℕ) :
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    let trajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    let gaps := PoissonProcess.exponentialInterarrivalMeasure rate
    (threshold : ℝ) * (trajectory.prod gaps).real {value | (threshold : ℝ) ≤
      (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun index =>
          (manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum
            servers index value.1) ^ 2)} ≤ n := by
  dsimp only
  let rate : ℝ := manyServerUniformizationRate
    (trafficIntensity : ℝ) serviceRate servers
  let trajectory : Measure (ℕ → ℕ × Bool) := stationaryTrajMeasure
    (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
    (manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers)
  let gaps : Measure (ℕ → ℝ) := PoissonProcess.exponentialInterarrivalMeasure rate
  let source : Measure ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := trajectory.prod gaps
  let event : Set (ℕ → ℕ × Bool) := {path | (threshold : ℝ) ≤
    (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      (fun index =>
        (manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum
          servers index path) ^ 2)}
  have hrate : 0 < rate :=
    manyServerUniformizationRate_pos trafficIntensity serviceRate servers hservers hserviceRate
  letI : IsProbabilityMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure := by
    infer_instance
  letI : IsMarkovKernel
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers) := by
    infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsProbabilityMeasure gaps := by
    dsimp [gaps]
    exact PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  have hevent_meas : MeasurableSet event := by
    dsimp [event]
    exact measurable_maximalCenteredUnrealizedPotentialServicePartialSum
      servers n measurableSet_Ici
  have hpreserve : MeasurePreserving Prod.fst source trajectory := by
    dsimp [source]
    exact measurePreserving_fst
  have hmeasure : source.real (Prod.fst ⁻¹' event) = trajectory.real event := by
    rw [← hpreserve.map_eq]
    simp only [measureReal_def]
    rw [Measure.map_apply measurable_fst hevent_meas]
  have hbase := ennreal_mul_measure_maximalCenteredUnrealizedPotentialServicePartialSum_le_from_initial
    initial trafficIntensity servers hservers threshold n
  have hbase_real : (threshold : ℝ) * trajectory.real event ≤ n := by
    have hbase_toReal := (ENNReal.toReal_le_toReal
      (ENNReal.mul_ne_top ENNReal.coe_ne_top (measure_ne_top _ _))
      ENNReal.ofReal_ne_top).mpr hbase
    simpa only [Measure.real, ENNReal.toReal_mul, ENNReal.coe_toReal,
      ENNReal.toReal_ofReal (Nat.cast_nonneg _)] using hbase_toReal
  change (threshold : ℝ) * source.real (Prod.fst ⁻¹' event) ≤ n
  rw [hmeasure]
  exact hbase_real

/-- The finite embedded arrival-versus-potential-service lower-exit estimate
transfers unchanged through the independent canonical clock.  This packages
the lower-barrier localization event as a physical construction while keeping
the cutoff in embedded-event units. -/
theorem real_mul_measure_manyServerMarkedCanonicalArrivalPotentialLowerExit_le_from_initial
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers initialLower lowerThreshold n : ℕ)
    (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    (margin : ℝ) (threshold : ℝ≥0)
    (hmargin_nonneg : 0 ≤ margin) (hthreshold : (threshold : ℝ) ≤ margin ^ 2)
    (hmargin : ∀ steps ≤ n,
      (lowerThreshold : ℝ) - (initialLower : ℝ) -
          (2 * (uniformizedBirthProbability trafficIntensity : ℝ) - 1) *
            (steps : ℝ) + 2 ≤ -2 * margin) :
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    let trajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    let gaps := PoissonProcess.exponentialInterarrivalMeasure rate
    (threshold : ℝ) * (trajectory.prod gaps).real {value |
      initialLower ≤ (value.1 0).1 ∧
      manyServerMarkedStateArrivalPotentialLowerExitTime
        lowerThreshold value.1 ≤ (n : ℕ∞)} ≤ n := by
  dsimp only
  let rate : ℝ := manyServerUniformizationRate
    (trafficIntensity : ℝ) serviceRate servers
  let trajectory : Measure (ℕ → ℕ × Bool) := stationaryTrajMeasure
    (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
    (manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers)
  let gaps : Measure (ℕ → ℝ) := PoissonProcess.exponentialInterarrivalMeasure rate
  let source : Measure ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := trajectory.prod gaps
  let event : Set (ℕ → ℕ × Bool) := {path |
    initialLower ≤ (path 0).1 ∧
    manyServerMarkedStateArrivalPotentialLowerExitTime lowerThreshold path ≤ (n : ℕ∞)}
  have hrate : 0 < rate :=
    manyServerUniformizationRate_pos trafficIntensity serviceRate servers hservers hserviceRate
  letI : IsProbabilityMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure := by
    infer_instance
  letI : IsMarkovKernel
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers) := by
    infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsProbabilityMeasure gaps := by
    dsimp [gaps]
    exact PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  have hinitial_meas : MeasurableSet {path : ℕ → ℕ × Bool |
      initialLower ≤ (path 0).1} := by
    exact (measurable_fst.comp (measurable_pi_apply 0)) measurableSet_Ici
  have hexit_meas : MeasurableSet {path : ℕ → ℕ × Bool |
      manyServerMarkedStateArrivalPotentialLowerExitTime lowerThreshold path ≤ (n : ℕ∞)} := by
    have heq : {path : ℕ → ℕ × Bool |
        manyServerMarkedStateArrivalPotentialLowerExitTime lowerThreshold path ≤ (n : ℕ∞)} =
        ⋃ steps ∈ Set.Iic n, {path | manyServerMarkedStateArrivalPotentialLowerBound
          path steps ≤ lowerThreshold} := by
      ext path
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_Iic]
      constructor
      · intro h
        rcases (manyServerMarkedStateArrivalPotentialLowerExitTime_le_iff
          lowerThreshold n path).mp h with ⟨steps, hsteps, hbound⟩
        exact ⟨steps, hsteps, hbound⟩
      · rintro ⟨steps, hsteps, hbound⟩
        exact (manyServerMarkedStateArrivalPotentialLowerExitTime_le_iff
          lowerThreshold n path).mpr ⟨steps, hsteps, hbound⟩
    rw [heq]
    refine MeasurableSet.biUnion (Set.to_countable _) fun steps hsteps => ?_
    have hbound_meas : Measurable
        (fun path => manyServerMarkedStateArrivalPotentialLowerBound path steps) :=
      (manyServerMarkedStateArrivalPotentialLowerBound_stronglyAdapted steps).mono
        (Filtration.piLE.le steps) |>.measurable
    exact hbound_meas measurableSet_Iic
  have hevent_meas : MeasurableSet event := by
    exact hinitial_meas.inter hexit_meas
  have hpreserve : MeasurePreserving Prod.fst source trajectory := by
    dsimp [source]
    exact measurePreserving_fst
  have hmeasure : source.real (Prod.fst ⁻¹' event) = trajectory.real event := by
    rw [← hpreserve.map_eq]
    simp only [measureReal_def]
    rw [Measure.map_apply measurable_fst hevent_meas]
  have hbase := ennreal_mul_measure_manyServerMarkedStateArrivalPotentialLowerExit_le_from_initial
    initial trafficIntensity servers initialLower lowerThreshold n hservers margin threshold
      hmargin_nonneg hthreshold hmargin
  have hbase_real : (threshold : ℝ) * trajectory.real event ≤ n := by
    have hbase_toReal := (ENNReal.toReal_le_toReal
      (ENNReal.mul_ne_top ENNReal.coe_ne_top (measure_ne_top _ _))
      ENNReal.ofReal_ne_top).mpr hbase
    simpa only [Measure.real, ENNReal.toReal_mul, ENNReal.coe_toReal,
      ENNReal.toReal_ofReal (Nat.cast_nonneg _)] using hbase_toReal
  change (threshold : ℝ) * source.real (Prod.fst ⁻¹' event) ≤ n
  rw [hmeasure]
  exact hbase_real

/-- A lower-barrier exit that has occurred by a fixed canonical physical
horizon is covered by either a renewal-clock overflow or the corresponding
finite embedded lower exit.  Combining their two estimates yields an explicit
two-cutoff localization bound for arbitrary initial laws. -/
theorem real_measure_manyServerMarkedCanonicalArrivalPotentialLowerExit_le_from_initial
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers initialLower lowerThreshold : ℕ)
    (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    {horizon : ℝ} (hhorizon : 0 ≤ horizon) (n : ℕ)
    (margin : ℝ) (threshold : ℝ≥0)
    (hmargin_nonneg : 0 ≤ margin) (hthreshold_le : (threshold : ℝ) ≤ margin ^ 2)
    (hthreshold_pos : 0 < threshold)
    (hmargin : ∀ steps ≤ n,
      (lowerThreshold : ℝ) - (initialLower : ℝ) -
          (2 * (uniformizedBirthProbability trafficIntensity : ℝ) - 1) *
            (steps : ℝ) + 2 ≤ -2 * margin) :
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    let trajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    let gaps := PoissonProcess.exponentialInterarrivalMeasure rate
    let source := trajectory.prod gaps
    source.real {value |
      initialLower ≤ (value.1 0).1 ∧
      manyServerMarkedStateArrivalPotentialLowerExitTime lowerThreshold value.1 ≤
        (PoissonProcess.canonicalRenewalCount horizon value.2 : ℕ∞)} ≤
      (rate * horizon) / (n + 1 : ℝ) + (n : ℝ) / threshold := by
  dsimp only
  let rate : ℝ := manyServerUniformizationRate
    (trafficIntensity : ℝ) serviceRate servers
  let trajectory : Measure (ℕ → ℕ × Bool) := stationaryTrajMeasure
    (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
    (manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers)
  let gaps : Measure (ℕ → ℝ) := PoissonProcess.exponentialInterarrivalMeasure rate
  let source : Measure ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := trajectory.prod gaps
  let physicalEvent : Set ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := {value |
    initialLower ≤ (value.1 0).1 ∧
    manyServerMarkedStateArrivalPotentialLowerExitTime lowerThreshold value.1 ≤
      (PoissonProcess.canonicalRenewalCount horizon value.2 : ℕ∞)}
  let clockEvent : Set ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := {value |
    (n + 1 : ℝ) ≤ (PoissonProcess.canonicalRenewalCount horizon value.2 : ℝ)}
  let embeddedEvent : Set ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := {value |
    initialLower ≤ (value.1 0).1 ∧
    manyServerMarkedStateArrivalPotentialLowerExitTime lowerThreshold value.1 ≤ (n : ℕ∞)}
  have hrate : 0 < rate :=
    manyServerUniformizationRate_pos trafficIntensity serviceRate servers hservers hserviceRate
  letI : IsProbabilityMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure := by
    infer_instance
  letI : IsMarkovKernel
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers) := by
    infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsProbabilityMeasure gaps := by
    dsimp [gaps]
    exact PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure source := by
    dsimp [source]
    infer_instance
  have hsubset : physicalEvent ⊆ clockEvent ∪ embeddedEvent := by
    intro value hvalue
    by_cases hclock : value ∈ clockEvent
    · exact Or.inl hclock
    · right
      have hclock_lt_real :
          (PoissonProcess.canonicalRenewalCount horizon value.2 : ℝ) < (n + 1 : ℝ) :=
        lt_of_not_ge hclock
      have hclock_lt_nat : PoissonProcess.canonicalRenewalCount horizon value.2 < n + 1 := by
        exact_mod_cast hclock_lt_real
      have hclock_le : PoissonProcess.canonicalRenewalCount horizon value.2 ≤ n :=
        Nat.lt_succ_iff.mp hclock_lt_nat
      exact ⟨hvalue.1, hvalue.2.trans (by exact_mod_cast hclock_le)⟩
  have hsplit : source.real physicalEvent ≤ source.real clockEvent + source.real embeddedEvent := by
    calc
      source.real physicalEvent ≤ source.real (clockEvent ∪ embeddedEvent) :=
        measureReal_mono hsubset
      _ ≤ source.real clockEvent + source.real embeddedEvent := measureReal_union_le _ _
  have hclock := real_mul_measure_manyServerMarkedCanonicalClockCount_ge_le
    (initial := initial) trafficIntensity serviceRate servers hservers hserviceRate
      hhorizon (show 0 ≤ (n + 1 : ℝ) by positivity)
  have hclock' : (n + 1 : ℝ) * source.real clockEvent ≤ rate * horizon := by
    simpa [rate, trajectory, gaps, source, clockEvent] using hclock
  have hclock_div : source.real clockEvent ≤ (rate * horizon) / (n + 1 : ℝ) := by
    apply (le_div_iff₀ (Nat.cast_add_one_pos n)).mpr
    simpa [mul_comm] using hclock'
  have hembedded :=
    real_mul_measure_manyServerMarkedCanonicalArrivalPotentialLowerExit_le_from_initial
      initial trafficIntensity serviceRate servers initialLower lowerThreshold n
        hservers hserviceRate margin threshold hmargin_nonneg hthreshold_le hmargin
  have hembedded' : (threshold : ℝ) * source.real embeddedEvent ≤ n := by
    simpa [rate, trajectory, gaps, source, embeddedEvent] using hembedded
  have hembedded_div : source.real embeddedEvent ≤ (n : ℝ) / threshold := by
    apply (le_div_iff₀ (by exact_mod_cast hthreshold_pos)).mpr
    simpa [mul_comm] using hembedded'
  change source.real physicalEvent ≤ (rate * horizon) / (n + 1 : ℝ) + (n : ℝ) / threshold
  exact hsplit.trans (add_le_add hclock_div hembedded_div)

/-- The lower-barrier-stopped embedded maximum has the same explicit
barrier-sensitive Doob bound after coupling to the independent canonical
clock. -/
theorem real_mul_measure_manyServerMarkedCanonicalStoppedEmbeddedMaximum_le_lowerThreshold_idleFraction_from_initial
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers lowerThreshold : ℕ) (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    (threshold : ℝ≥0) (n : ℕ) :
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    let trajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    let gaps := PoissonProcess.exponentialInterarrivalMeasure rate
    (threshold : ℝ) * (trajectory.prod gaps).real {value | (threshold : ℝ) ≤
      (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun index =>
          (manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum
            servers lowerThreshold index value.1) ^ 2)} ≤
      (n : ℝ) * (1 - (manyServerBusyFraction servers lowerThreshold : ℝ)) := by
  dsimp only
  let rate : ℝ := manyServerUniformizationRate
    (trafficIntensity : ℝ) serviceRate servers
  let trajectory : Measure (ℕ → ℕ × Bool) := stationaryTrajMeasure
    (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
    (manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers)
  let gaps : Measure (ℕ → ℝ) := PoissonProcess.exponentialInterarrivalMeasure rate
  let source : Measure ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := trajectory.prod gaps
  let event : Set (ℕ → ℕ × Bool) := {path | (threshold : ℝ) ≤
    (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      (fun index =>
        (manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum
          servers lowerThreshold index path) ^ 2)}
  have hrate : 0 < rate :=
    manyServerUniformizationRate_pos trafficIntensity serviceRate servers hservers hserviceRate
  letI : IsProbabilityMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure := by
    infer_instance
  letI : IsMarkovKernel
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers) := by
    infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsProbabilityMeasure gaps := by
    dsimp [gaps]
    exact PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  have hevent_meas : MeasurableSet event := by
    dsimp [event]
    exact measurable_maximalStoppedUnrealizedPotentialServicePartialSum
      servers lowerThreshold n measurableSet_Ici
  have hpreserve : MeasurePreserving Prod.fst source trajectory := by
    dsimp [source]
    exact measurePreserving_fst
  have hmeasure : source.real (Prod.fst ⁻¹' event) = trajectory.real event := by
    rw [← hpreserve.map_eq]
    simp only [measureReal_def]
    rw [Measure.map_apply measurable_fst hevent_meas]
  have hbase :=
    ennreal_mul_measure_maximalStoppedUnrealizedPotentialServicePartialSum_le_lowerThreshold_idleFraction_from_initial
      initial trafficIntensity servers lowerThreshold hservers threshold n
  have hidle_nonneg : 0 ≤ 1 - (manyServerBusyFraction servers lowerThreshold : ℝ) := by
    have hbusy_le : (manyServerBusyFraction servers lowerThreshold : ℝ) ≤ 1 := by
      exact_mod_cast manyServerBusyFraction_le_one servers lowerThreshold hservers
    linarith
  have hright_nonneg : 0 ≤ (n : ℝ) *
      (1 - (manyServerBusyFraction servers lowerThreshold : ℝ)) :=
    mul_nonneg (Nat.cast_nonneg n) hidle_nonneg
  have hbase_real : (threshold : ℝ) * trajectory.real event ≤
      (n : ℝ) * (1 - (manyServerBusyFraction servers lowerThreshold : ℝ)) := by
    have hbase_toReal := (ENNReal.toReal_le_toReal
      (ENNReal.mul_ne_top ENNReal.coe_ne_top (measure_ne_top _ _))
      ENNReal.ofReal_ne_top).mpr hbase
    simpa only [Measure.real, ENNReal.toReal_mul, ENNReal.coe_toReal,
      ENNReal.toReal_ofReal hright_nonneg] using hbase_toReal
  change (threshold : ℝ) * source.real (Prod.fst ⁻¹' event) ≤ _
  rw [hmeasure]
  exact hbase_real

/-- An arbitrary-initial physical-time excursion of the centered
unrealized-potential-service correction is controlled by three transparent
localization events: a canonical-clock overflow, a lower-barrier exit, or a
large stopped embedded martingale maximum.  The lower-exit estimate and the
stopped maximum use separate thresholds, so applications may optimize the
two cutoffs independently. -/
theorem real_measure_manyServerMarkedCanonicalCorrectionExcursion_le_from_initial_lowerBarrier
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers initialLower lowerThreshold : ℕ)
    (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    {horizon : ℝ} (hhorizon : 0 ≤ horizon) (n : ℕ) (margin : ℝ)
    (exitThreshold correctionThreshold : ℝ≥0)
    (hmargin_nonneg : 0 ≤ margin)
    (hexitThreshold_le : (exitThreshold : ℝ) ≤ margin ^ 2)
    (hexitThreshold_pos : 0 < exitThreshold)
    (hmargin : ∀ steps ≤ n,
      (lowerThreshold : ℝ) - (initialLower : ℝ) -
          (2 * (uniformizedBirthProbability trafficIntensity : ℝ) - 1) *
            (steps : ℝ) + 2 ≤ -2 * margin)
    (hcorrectionThreshold_pos : 0 < correctionThreshold) :
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    let trajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    let gaps := PoissonProcess.exponentialInterarrivalMeasure rate
    let source := trajectory.prod gaps
    source.real {value |
      initialLower ≤ (value.1 0).1 ∧
        ∃ time : ℝ, time ≤ horizon ∧ (correctionThreshold : ℝ) ≤
          (manyServerMarkedCanonicalCenteredUnrealizedPotentialServiceCorrection
            servers time value) ^ 2} ≤
      (rate * horizon) / (n + 1 : ℝ) + (n : ℝ) / exitThreshold +
        ((n : ℝ) * (1 - (manyServerBusyFraction servers lowerThreshold : ℝ))) /
          correctionThreshold := by
  dsimp only
  let rate : ℝ := manyServerUniformizationRate
    (trafficIntensity : ℝ) serviceRate servers
  let trajectory : Measure (ℕ → ℕ × Bool) := stationaryTrajMeasure
    (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
    (manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers)
  let gaps : Measure (ℕ → ℝ) := PoissonProcess.exponentialInterarrivalMeasure rate
  let source : Measure ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := trajectory.prod gaps
  let bad : Set ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := {value |
    initialLower ≤ (value.1 0).1 ∧
      ∃ time : ℝ, time ≤ horizon ∧ (correctionThreshold : ℝ) ≤
        (manyServerMarkedCanonicalCenteredUnrealizedPotentialServiceCorrection
          servers time value) ^ 2}
  let clockEvent : Set ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := {value |
    (n + 1 : ℝ) ≤ (PoissonProcess.canonicalRenewalCount horizon value.2 : ℝ)}
  let exitEvent : Set ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := {value |
    initialLower ≤ (value.1 0).1 ∧
      manyServerMarkedStateArrivalPotentialLowerExitTime lowerThreshold value.1 ≤
        (n : ℕ∞)}
  let stoppedEvent : Set ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := {value |
    (correctionThreshold : ℝ) ≤
      (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun index =>
          (manyServerMarkedStateStoppedUnrealizedPotentialServicePartialSum
            servers lowerThreshold index value.1) ^ 2)}
  let good : Set ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := {value |
    Monotone (fun time : ℝ => PoissonProcess.canonicalRenewalCount time value.2)}
  have hrate : 0 < rate :=
    manyServerUniformizationRate_pos trafficIntensity serviceRate servers hservers hserviceRate
  letI : IsProbabilityMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure := by
    infer_instance
  letI : IsMarkovKernel
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers) := by
    infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsProbabilityMeasure gaps := by
    dsimp [gaps]
    exact PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure source := by
    dsimp [source]
    infer_instance
  have hmono_gaps : ∀ᵐ gap ∂gaps,
      Monotone (fun time : ℝ => PoissonProcess.canonicalRenewalCount time gap) := by
    simpa [gaps] using PoissonProcess.ae_canonicalRenewalCount_monotone hrate
  have hmono : ∀ᵐ value ∂source,
      Monotone (fun time : ℝ => PoissonProcess.canonicalRenewalCount time value.2) := by
    refine ae_of_ae_map (μ := source) (f := Prod.snd)
      (p := fun gap : ℕ → ℝ =>
        Monotone (fun time : ℝ => PoissonProcess.canonicalRenewalCount time gap))
      measurable_snd.aemeasurable ?_
    rw [Measure.map_snd_prod, measure_univ, one_smul]
    exact hmono_gaps
  have hbad_eq : (fun value => value ∈ bad) =ᵐ[source]
      (fun value => value ∈ bad ∩ good) := by
    filter_upwards [hmono] with value hvalue
    simp [good, hvalue]
  have hbad_measure : source.real bad = source.real (bad ∩ good) := by
    exact MeasureTheory.measureReal_congr hbad_eq
  have hsubset : bad ∩ good ⊆
      (clockEvent ∪ exitEvent) ∪ stoppedEvent := by
    intro value hvalue
    rcases hvalue.1 with ⟨hinitial, time, htime, hlarge⟩
    have hclock_mono := hvalue.2
    by_cases hclock : value ∈ clockEvent
    · exact Or.inl (Or.inl hclock)
    by_cases hexit : value ∈ exitEvent
    · exact Or.inl (Or.inr hexit)
    right
    have hcount_lt_real :
        (PoissonProcess.canonicalRenewalCount horizon value.2 : ℝ) < (n + 1 : ℝ) :=
      lt_of_not_ge hclock
    have hcount_lt_nat : PoissonProcess.canonicalRenewalCount horizon value.2 < n + 1 := by
      exact_mod_cast hcount_lt_real
    have hcount : PoissonProcess.canonicalRenewalCount horizon value.2 ≤ n :=
      Nat.lt_succ_iff.mp hcount_lt_nat
    have hbefore : (PoissonProcess.canonicalRenewalCount horizon value.2 : ENat) <
        manyServerMarkedStateArrivalPotentialLowerExitTime lowerThreshold value.1 := by
      apply lt_of_not_ge
      intro hle
      apply hexit
      exact ⟨hinitial, hle.trans (ENat.coe_le_coe.mpr hcount)⟩
    exact hlarge.trans
      (manyServerMarkedCanonicalCenteredUnrealizedPotentialServiceCorrection_sq_le_stoppedEmbeddedMaximum_of_clock_count_lt_lowerExit
        servers lowerThreshold value n hclock_mono htime hcount hbefore)
  have hsplit : source.real bad ≤
      source.real clockEvent + source.real exitEvent + source.real stoppedEvent := by
    calc
      source.real bad = source.real (bad ∩ good) :=
        hbad_measure
      _ ≤ source.real ((clockEvent ∪ exitEvent) ∪ stoppedEvent) :=
        measureReal_mono hsubset (measure_ne_top _ _)
      _ ≤ source.real (clockEvent ∪ exitEvent) + source.real stoppedEvent :=
        measureReal_union_le _ _
      _ ≤ source.real clockEvent + source.real exitEvent + source.real stoppedEvent := by
        gcongr
        exact measureReal_union_le _ _
  have hclock := real_mul_measure_manyServerMarkedCanonicalClockCount_ge_le
    (initial := initial) trafficIntensity serviceRate servers hservers hserviceRate
      hhorizon (show 0 ≤ (n + 1 : ℝ) by positivity)
  have hclock' : (n + 1 : ℝ) * source.real clockEvent ≤ rate * horizon := by
    simpa [rate, trajectory, gaps, source, clockEvent] using hclock
  have hclock_div : source.real clockEvent ≤ (rate * horizon) / (n + 1 : ℝ) := by
    apply (le_div_iff₀ (Nat.cast_add_one_pos n)).mpr
    simpa [mul_comm] using hclock'
  have hexit_bound :=
    real_mul_measure_manyServerMarkedCanonicalArrivalPotentialLowerExit_le_from_initial
      initial trafficIntensity serviceRate servers initialLower lowerThreshold n hservers hserviceRate
        margin exitThreshold hmargin_nonneg hexitThreshold_le hmargin
  have hexit_div : source.real exitEvent ≤ (n : ℝ) / exitThreshold := by
    have hexit' : (exitThreshold : ℝ) * source.real exitEvent ≤ n := by
      simpa [rate, trajectory, gaps, source, exitEvent] using hexit_bound
    apply (le_div_iff₀ (by exact_mod_cast hexitThreshold_pos)).mpr
    simpa [mul_comm] using hexit'
  have hstopped :=
    real_mul_measure_manyServerMarkedCanonicalStoppedEmbeddedMaximum_le_lowerThreshold_idleFraction_from_initial
      initial trafficIntensity serviceRate servers lowerThreshold hservers hserviceRate
        correctionThreshold n
  have hstopped' : (correctionThreshold : ℝ) * source.real stoppedEvent ≤
      (n : ℝ) * (1 - (manyServerBusyFraction servers lowerThreshold : ℝ)) := by
    simpa [rate, trajectory, gaps, source, stoppedEvent] using hstopped
  have hstopped_div : source.real stoppedEvent ≤
      ((n : ℝ) * (1 - (manyServerBusyFraction servers lowerThreshold : ℝ))) /
        correctionThreshold := by
    apply (le_div_iff₀ (by exact_mod_cast hcorrectionThreshold_pos)).mpr
    simpa [mul_comm] using hstopped'
  change source.real bad ≤
    (rate * horizon) / (n + 1 : ℝ) + (n : ℝ) / exitThreshold +
      ((n : ℝ) * (1 - (manyServerBusyFraction servers lowerThreshold : ℝ))) /
        correctionThreshold
  exact hsplit.trans (add_le_add (add_le_add hclock_div hexit_div) hstopped_div)

/-- The lower-barrier correction estimate with its initial-condition event
made explicit as the exact lower tail of the supplied initial PMF.  This is
the form that combines directly with weak tightness of centered initial queue
coordinates. -/
theorem real_measure_manyServerMarkedCanonicalCorrectionExcursion_le_from_initial_lowerBarrier_withInitialTail
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers initialLower lowerThreshold : ℕ)
    (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    {horizon : ℝ} (hhorizon : 0 ≤ horizon) (n : ℕ) (margin : ℝ)
    (exitThreshold correctionThreshold : ℝ≥0)
    (hmargin_nonneg : 0 ≤ margin)
    (hexitThreshold_le : (exitThreshold : ℝ) ≤ margin ^ 2)
    (hexitThreshold_pos : 0 < exitThreshold)
    (hmargin : ∀ steps ≤ n,
      (lowerThreshold : ℝ) - (initialLower : ℝ) -
          (2 * (uniformizedBirthProbability trafficIntensity : ℝ) - 1) *
            (steps : ℝ) + 2 ≤ -2 * margin)
    (hcorrectionThreshold_pos : 0 < correctionThreshold) :
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    let trajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    let gaps := PoissonProcess.exponentialInterarrivalMeasure rate
    let source := trajectory.prod gaps
    source.real {value | ∃ time : ℝ, time ≤ horizon ∧ (correctionThreshold : ℝ) ≤
      (manyServerMarkedCanonicalCenteredUnrealizedPotentialServiceCorrection
        servers time value) ^ 2} ≤
      initial.toMeasure.real (Set.Iio initialLower) +
        (rate * horizon) / (n + 1 : ℝ) + (n : ℝ) / exitThreshold +
          ((n : ℝ) * (1 - (manyServerBusyFraction servers lowerThreshold : ℝ))) /
            correctionThreshold := by
  dsimp only
  let rate : ℝ := manyServerUniformizationRate
    (trafficIntensity : ℝ) serviceRate servers
  let trajectory : Measure (ℕ → ℕ × Bool) := stationaryTrajMeasure
    (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
    (manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers)
  let gaps : Measure (ℕ → ℝ) := PoissonProcess.exponentialInterarrivalMeasure rate
  let source : Measure ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := trajectory.prod gaps
  let initialBad : Set ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := {value |
    (value.1 0).1 < initialLower}
  let localizedBad : Set ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := {value |
    initialLower ≤ (value.1 0).1 ∧
      ∃ time : ℝ, time ≤ horizon ∧ (correctionThreshold : ℝ) ≤
        (manyServerMarkedCanonicalCenteredUnrealizedPotentialServiceCorrection
          servers time value) ^ 2}
  let correctionEvent : Set ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := {value |
    ∃ time : ℝ, time ≤ horizon ∧ (correctionThreshold : ℝ) ≤
      (manyServerMarkedCanonicalCenteredUnrealizedPotentialServiceCorrection
        servers time value) ^ 2}
  have hrate : 0 < rate :=
    manyServerUniformizationRate_pos trafficIntensity serviceRate servers hservers hserviceRate
  letI : IsProbabilityMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure := by
    infer_instance
  letI : IsMarkovKernel
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers) := by
    infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsProbabilityMeasure gaps := by
    dsimp [gaps]
    exact PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure source := by
    dsimp [source]
    infer_instance
  have hsubset : correctionEvent ⊆ initialBad ∪ localizedBad := by
    intro value hvalue
    by_cases hinitial : initialLower ≤ (value.1 0).1
    · exact Or.inr ⟨hinitial, hvalue⟩
    · exact Or.inl (Nat.lt_of_not_ge hinitial)
  have htail_measure : source initialBad = initial.toMeasure (Set.Iio initialLower) := by
    simpa [source, initialBad, manyServerMarkedCanonicalInitialQueue] using
      (measure_manyServerMarkedCanonicalInitialQueue_preimage
        initial trafficIntensity serviceRate servers hservers hserviceRate (Set.Iio initialLower))
  have htail : source.real initialBad = initial.toMeasure.real (Set.Iio initialLower) := by
    simp only [Measure.real]
    rw [htail_measure]
  have hlocalized :=
    real_measure_manyServerMarkedCanonicalCorrectionExcursion_le_from_initial_lowerBarrier
      initial trafficIntensity serviceRate servers initialLower lowerThreshold
        hservers hserviceRate hhorizon n margin exitThreshold correctionThreshold
        hmargin_nonneg hexitThreshold_le hexitThreshold_pos hmargin
        hcorrectionThreshold_pos
  have hlocalized' : source.real localizedBad ≤
      (rate * horizon) / (n + 1 : ℝ) + (n : ℝ) / exitThreshold +
        ((n : ℝ) * (1 - (manyServerBusyFraction servers lowerThreshold : ℝ))) /
          correctionThreshold := by
    simpa [source, localizedBad] using hlocalized
  calc
    source.real correctionEvent ≤ source.real (initialBad ∪ localizedBad) :=
      measureReal_mono hsubset (measure_ne_top _ _)
    _ ≤ source.real initialBad + source.real localizedBad :=
      measureReal_union_le _ _
    _ ≤ initial.toMeasure.real (Set.Iio initialLower) +
        ((rate * horizon) / (n + 1 : ℝ) + (n : ℝ) / exitThreshold +
          ((n : ℝ) * (1 - (manyServerBusyFraction servers lowerThreshold : ℝ))) /
            correctionThreshold) := by
        rw [htail]
        gcongr
    _ = initial.toMeasure.real (Set.Iio initialLower) +
        (rate * horizon) / (n + 1 : ℝ) + (n : ℝ) / exitThreshold +
          ((n : ℝ) * (1 - (manyServerBusyFraction servers lowerThreshold : ℝ))) /
            correctionThreshold := by ring

/-- The stationary embedded Doob estimate transfers unchanged through the
independent canonical clock.  It retains the stationary spare-capacity factor
that sharpens the arbitrary-initial estimate. -/
theorem real_mul_measure_manyServerMarkedCanonicalEmbeddedMaximum_stationary_le
    (trafficIntensity : ℝ≥0) (serviceRate : ℝ) (servers : ℕ)
    (hservers : 0 < servers) (htraffic_pos : 0 < trafficIntensity)
    (htraffic_lt_one : trafficIntensity < 1) (hserviceRate : 0 < serviceRate)
    (threshold : ℝ≥0) (n : ℕ) :
    let initial := manyServerStationaryPMF (trafficIntensity : ℝ) servers
      (by positivity) (by exact_mod_cast htraffic_lt_one)
    let trajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    let gaps := PoissonProcess.exponentialInterarrivalMeasure
      (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers)
    (threshold : ℝ) * (trajectory.prod gaps).real {value | (threshold : ℝ) ≤
      (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun index =>
          (manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum
            servers index value.1) ^ 2)} ≤
      (n : ℝ) * ((1 - uniformizedBirthProbability trafficIntensity : ℝ≥0) : ℝ) *
        (1 - (trafficIntensity : ℝ)) := by
  dsimp only
  let initial : PMF ℕ := manyServerStationaryPMF (trafficIntensity : ℝ) servers
    (by positivity) (by exact_mod_cast htraffic_lt_one)
  let trajectory : Measure (ℕ → ℕ × Bool) := stationaryTrajMeasure
    (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
    (manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers)
  let gaps : Measure (ℕ → ℝ) := PoissonProcess.exponentialInterarrivalMeasure
    (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers)
  let source : Measure ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := trajectory.prod gaps
  let event : Set (ℕ → ℕ × Bool) := {path | (threshold : ℝ) ≤
    (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      (fun index =>
        (manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum
          servers index path) ^ 2)}
  have hrate : 0 < manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers :=
    manyServerUniformizationRate_pos trafficIntensity serviceRate servers hservers hserviceRate
  letI : IsProbabilityMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure := by
    infer_instance
  letI : IsMarkovKernel
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers) := by
    infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsProbabilityMeasure gaps := by
    dsimp [gaps]
    exact PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  have hevent_meas : MeasurableSet event := by
    dsimp [event]
    exact measurable_maximalCenteredUnrealizedPotentialServicePartialSum
      servers n measurableSet_Ici
  have hpreserve : MeasurePreserving Prod.fst source trajectory := by
    dsimp [source]
    exact measurePreserving_fst
  have hmeasure : source.real (Prod.fst ⁻¹' event) = trajectory.real event := by
    rw [← hpreserve.map_eq]
    simp only [measureReal_def]
    rw [Measure.map_apply measurable_fst hevent_meas]
  have hbase := real_mul_measure_maximalCenteredUnrealizedPotentialServicePartialSum_stationary_le
    trafficIntensity servers hservers htraffic_pos htraffic_lt_one threshold n
  change (threshold : ℝ) * source.real (Prod.fst ⁻¹' event) ≤ _
  rw [hmeasure]
  simpa [initial, trajectory, event] using hbase

/-- A physical-time excursion of the centered unrealized-service correction
is covered by one of two finite events: the canonical clock exceeds its
embedded cutoff, or the finite embedded martingale maximum exceeds the same
threshold.  The monotonicity failure of the renewal clock is null and has
already been removed from the real-probability bound. -/
theorem real_measure_manyServerMarkedCanonicalCorrectionExcursion_le_clock_add_embeddedMaximum
    {initial : PMF ℕ} (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers : ℕ) (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    {horizon : ℝ} (n : ℕ) (threshold : ℝ) :
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    let trajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    let gaps := PoissonProcess.exponentialInterarrivalMeasure rate
    let source := trajectory.prod gaps
    source.real {value | ∃ time : ℝ, time ≤ horizon ∧ threshold ≤
      (manyServerMarkedCanonicalCenteredUnrealizedPotentialServiceCorrection
        servers time value) ^ 2} ≤
      source.real {value | (n + 1 : ℝ) ≤
        (PoissonProcess.canonicalRenewalCount horizon value.2 : ℝ)} +
      source.real {value | threshold ≤
        (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          (fun index =>
            (manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum
              servers index value.1) ^ 2)} := by
  dsimp only
  let rate : ℝ := manyServerUniformizationRate
    (trafficIntensity : ℝ) serviceRate servers
  let trajectory : Measure (ℕ → ℕ × Bool) := stationaryTrajMeasure
    (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
    (manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers)
  let gaps : Measure (ℕ → ℝ) :=
    PoissonProcess.exponentialInterarrivalMeasure rate
  let source : Measure ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := trajectory.prod gaps
  let physicalEvent : Set ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := {value | ∃ time : ℝ,
    time ≤ horizon ∧ threshold ≤
      (manyServerMarkedCanonicalCenteredUnrealizedPotentialServiceCorrection
        servers time value) ^ 2}
  let clockEvent : Set ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := {value |
    (n + 1 : ℝ) ≤ (PoissonProcess.canonicalRenewalCount horizon value.2 : ℝ)}
  let embeddedEvent : Set ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := {value | threshold ≤
    (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      (fun index =>
        (manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum
          servers index value.1) ^ 2)}
  let exceptionalEvent : Set ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := {value |
    ¬ Monotone (fun time : ℝ =>
      PoissonProcess.canonicalRenewalCount time value.2)}
  have hrate : 0 < rate :=
    manyServerUniformizationRate_pos trafficIntensity serviceRate servers hservers hserviceRate
  letI : IsProbabilityMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure := by
    infer_instance
  letI : IsMarkovKernel
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers) := by
    infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsProbabilityMeasure gaps := by
    dsimp [gaps]
    exact PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure source := by
    dsimp [source]
    infer_instance
  have hmono : ∀ᵐ value ∂source,
      Monotone (fun time : ℝ =>
        PoissonProcess.canonicalRenewalCount time value.2) := by
    have hmono_gaps : ∀ᵐ gap ∂gaps,
        Monotone (fun time : ℝ => PoissonProcess.canonicalRenewalCount time gap) := by
      simpa [gaps] using PoissonProcess.ae_canonicalRenewalCount_monotone hrate
    refine ae_of_ae_map (μ := source) (f := Prod.snd)
      (p := fun gap : ℕ → ℝ =>
        Monotone (fun time : ℝ => PoissonProcess.canonicalRenewalCount time gap))
      measurable_snd.aemeasurable ?_
    rw [Measure.map_snd_prod, measure_univ, one_smul]
    exact hmono_gaps
  have hnull : source exceptionalEvent = 0 := by
    exact ae_iff.mp hmono
  have hnull_real : source.real exceptionalEvent = 0 := by
    simp only [measureReal_def, hnull, ENNReal.toReal_zero]
  have hsubset : physicalEvent ⊆ clockEvent ∪ (embeddedEvent ∪ exceptionalEvent) := by
    intro value hvalue
    rcases hvalue with ⟨time, htime, hthreshold⟩
    by_cases hclock : value ∈ clockEvent
    · exact Or.inl hclock
    by_cases hembedded : value ∈ embeddedEvent
    · exact Or.inr (Or.inl hembedded)
    right
    right
    change ¬ Monotone (fun time : ℝ =>
      PoissonProcess.canonicalRenewalCount time value.2)
    intro hmono_value
    have hclock_lt_real :
        (PoissonProcess.canonicalRenewalCount horizon value.2 : ℝ) < (n + 1 : ℝ) :=
      lt_of_not_ge hclock
    have hclock_lt_nat : PoissonProcess.canonicalRenewalCount horizon value.2 < n + 1 := by
      exact_mod_cast hclock_lt_real
    have hclock_le : PoissonProcess.canonicalRenewalCount horizon value.2 ≤ n :=
      Nat.lt_succ_iff.mp hclock_lt_nat
    have hbound :=
      manyServerMarkedCanonicalCenteredUnrealizedPotentialServiceCorrection_sq_le_embeddedMaximum_of_clock_count_le
        servers value n hmono_value htime hclock_le
    exact hembedded (hthreshold.trans hbound)
  change source.real physicalEvent ≤ source.real clockEvent + source.real embeddedEvent
  calc
    source.real physicalEvent ≤ source.real (clockEvent ∪ (embeddedEvent ∪ exceptionalEvent)) :=
      measureReal_mono hsubset
    _ ≤ source.real clockEvent + source.real (embeddedEvent ∪ exceptionalEvent) :=
      measureReal_union_le _ _
    _ ≤ source.real clockEvent +
        (source.real embeddedEvent + source.real exceptionalEvent) := by
      gcongr
      exact measureReal_union_le _ _
    _ = source.real clockEvent + source.real embeddedEvent := by
      rw [hnull_real, add_zero]

/-- A finite-time correction-excursion bound for an arbitrary initial queue
law.  It combines the canonical-clock overflow estimate with the embedded
Doob estimate for the marked correction martingale. -/
theorem real_measure_manyServerMarkedCanonicalCorrectionExcursion_le_from_initial
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers : ℕ) (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    {horizon : ℝ} (hhorizon : 0 ≤ horizon) (n : ℕ) (threshold : ℝ≥0)
    (hthreshold : 0 < threshold) :
    let trajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    let gaps := PoissonProcess.exponentialInterarrivalMeasure
      (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers)
    let source := trajectory.prod gaps
    source.real {value | ∃ time : ℝ, time ≤ horizon ∧ (threshold : ℝ) ≤
      (manyServerMarkedCanonicalCenteredUnrealizedPotentialServiceCorrection
        servers time value) ^ 2} ≤
      (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers * horizon) /
        (n + 1 : ℝ) + (n : ℝ) / threshold := by
  dsimp only
  let trajectory : Measure (ℕ → ℕ × Bool) := stationaryTrajMeasure
    (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
    (manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers)
  let gaps : Measure (ℕ → ℝ) := PoissonProcess.exponentialInterarrivalMeasure
    (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers)
  let source : Measure ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := trajectory.prod gaps
  let clockEvent : Set ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := {value |
    (n + 1 : ℝ) ≤ (PoissonProcess.canonicalRenewalCount horizon value.2 : ℝ)}
  let embeddedEvent : Set ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := {value | (threshold : ℝ) ≤
    (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      (fun index =>
        (manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum
          servers index value.1) ^ 2)}
  have hsplit :=
    real_measure_manyServerMarkedCanonicalCorrectionExcursion_le_clock_add_embeddedMaximum
      (initial := initial) trafficIntensity serviceRate servers hservers hserviceRate
      (horizon := horizon) n (threshold : ℝ)
  have hclock := real_mul_measure_manyServerMarkedCanonicalClockCount_ge_le
    (initial := initial) trafficIntensity serviceRate servers hservers hserviceRate
    hhorizon (show 0 ≤ (n + 1 : ℝ) by positivity)
  have hclock' : (n + 1 : ℝ) * source.real clockEvent ≤
      manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers * horizon := by
    simpa [trajectory, gaps, source, clockEvent] using hclock
  have hclock_div : source.real clockEvent ≤
      (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers * horizon) /
        (n + 1 : ℝ) := by
    apply (le_div_iff₀ (Nat.cast_add_one_pos n)).mpr
    simpa [mul_comm] using hclock'
  have hembedded := real_mul_measure_manyServerMarkedCanonicalEmbeddedMaximum_le_from_initial
    initial trafficIntensity serviceRate servers hservers hserviceRate threshold n
  have hembedded' : (threshold : ℝ) * source.real embeddedEvent ≤ n := by
    simpa [trajectory, gaps, source, embeddedEvent] using hembedded
  have hembedded_div : source.real embeddedEvent ≤ (n : ℝ) / threshold := by
    apply (le_div_iff₀ (by exact_mod_cast hthreshold)).mpr
    simpa [mul_comm] using hembedded'
  change source.real {value | ∃ time : ℝ, time ≤ horizon ∧ (threshold : ℝ) ≤
    (manyServerMarkedCanonicalCenteredUnrealizedPotentialServiceCorrection
      servers time value) ^ 2} ≤ _
  calc
    source.real {value | ∃ time : ℝ, time ≤ horizon ∧ (threshold : ℝ) ≤
        (manyServerMarkedCanonicalCenteredUnrealizedPotentialServiceCorrection
          servers time value) ^ 2} ≤ source.real clockEvent + source.real embeddedEvent := by
            simpa [trajectory, gaps, source, clockEvent, embeddedEvent] using hsplit
    _ ≤ (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers * horizon) /
          (n + 1 : ℝ) + (n : ℝ) / threshold :=
      add_le_add hclock_div hembedded_div

/-- In the stationary underloaded regime, the physical-time correction
excursion has an explicit two-cutoff probability bound.  The first term is
the canonical-clock overflow bound and the second is the spare-capacity
embedded Doob bound. -/
theorem real_measure_manyServerMarkedCanonicalCorrectionExcursion_stationary_le
    (trafficIntensity : ℝ≥0) (serviceRate : ℝ) (servers : ℕ)
    (hservers : 0 < servers) (htraffic_pos : 0 < trafficIntensity)
    (htraffic_lt_one : trafficIntensity < 1) (hserviceRate : 0 < serviceRate)
    {horizon : ℝ} (hhorizon : 0 ≤ horizon) (n : ℕ) (threshold : ℝ≥0)
    (hthreshold : 0 < threshold) :
    let initial := manyServerStationaryPMF (trafficIntensity : ℝ) servers
      (by positivity) (by exact_mod_cast htraffic_lt_one)
    let trajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    let gaps := PoissonProcess.exponentialInterarrivalMeasure
      (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers)
    let source := trajectory.prod gaps
    source.real {value | ∃ time : ℝ, time ≤ horizon ∧ (threshold : ℝ) ≤
      (manyServerMarkedCanonicalCenteredUnrealizedPotentialServiceCorrection
        servers time value) ^ 2} ≤
      (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers * horizon) /
        (n + 1 : ℝ) +
      ((n : ℝ) * ((1 - uniformizedBirthProbability trafficIntensity : ℝ≥0) : ℝ) *
        (1 - (trafficIntensity : ℝ))) / threshold := by
  dsimp only
  let initial : PMF ℕ := manyServerStationaryPMF (trafficIntensity : ℝ) servers
    (by positivity) (by exact_mod_cast htraffic_lt_one)
  let trajectory : Measure (ℕ → ℕ × Bool) := stationaryTrajMeasure
    (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
    (manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers)
  let gaps : Measure (ℕ → ℝ) := PoissonProcess.exponentialInterarrivalMeasure
    (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers)
  let source : Measure ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := trajectory.prod gaps
  let clockEvent : Set ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := {value |
    (n + 1 : ℝ) ≤ (PoissonProcess.canonicalRenewalCount horizon value.2 : ℝ)}
  let embeddedEvent : Set ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := {value | (threshold : ℝ) ≤
    (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      (fun index =>
        (manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum
          servers index value.1) ^ 2)}
  have hrate : 0 < manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers :=
    manyServerUniformizationRate_pos trafficIntensity serviceRate servers hservers hserviceRate
  letI : IsProbabilityMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure := by
    infer_instance
  letI : IsMarkovKernel
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers) := by
    infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsProbabilityMeasure gaps := by
    dsimp [gaps]
    exact PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure source := by
    dsimp [source]
    infer_instance
  have hsplit :=
    real_measure_manyServerMarkedCanonicalCorrectionExcursion_le_clock_add_embeddedMaximum
      (initial := initial) trafficIntensity serviceRate servers hservers hserviceRate
      (horizon := horizon) n (threshold : ℝ)
  have hclock := real_mul_measure_manyServerMarkedCanonicalClockCount_ge_le
    (initial := initial) trafficIntensity serviceRate servers hservers hserviceRate
    hhorizon (show 0 ≤ (n + 1 : ℝ) by positivity)
  have hclock' : (n + 1 : ℝ) * source.real clockEvent ≤
      manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers * horizon := by
    simpa [trajectory, gaps, source, clockEvent] using hclock
  have hclock_div : source.real clockEvent ≤
      (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers * horizon) /
        (n + 1 : ℝ) := by
    apply (le_div_iff₀ (Nat.cast_add_one_pos n)).mpr
    simpa [mul_comm] using hclock'
  have hembedded := real_mul_measure_manyServerMarkedCanonicalEmbeddedMaximum_stationary_le
    trafficIntensity serviceRate servers hservers htraffic_pos htraffic_lt_one hserviceRate threshold n
  have hembedded' : (threshold : ℝ) * source.real embeddedEvent ≤
      (n : ℝ) * ((1 - uniformizedBirthProbability trafficIntensity : ℝ≥0) : ℝ) *
        (1 - (trafficIntensity : ℝ)) := by
    simpa [initial, trajectory, gaps, source, embeddedEvent] using hembedded
  have hembedded_div : source.real embeddedEvent ≤
      ((n : ℝ) * ((1 - uniformizedBirthProbability trafficIntensity : ℝ≥0) : ℝ) *
        (1 - (trafficIntensity : ℝ))) / threshold := by
    apply (le_div_iff₀ (by exact_mod_cast hthreshold)).mpr
    simpa [mul_comm] using hembedded'
  change source.real {value | ∃ time : ℝ, time ≤ horizon ∧ (threshold : ℝ) ≤
    (manyServerMarkedCanonicalCenteredUnrealizedPotentialServiceCorrection
      servers time value) ^ 2} ≤ _
  calc
    source.real {value | ∃ time : ℝ, time ≤ horizon ∧ (threshold : ℝ) ≤
        (manyServerMarkedCanonicalCenteredUnrealizedPotentialServiceCorrection
          servers time value) ^ 2} ≤ source.real clockEvent + source.real embeddedEvent := by
            simpa [trajectory, gaps, source, clockEvent, embeddedEvent] using hsplit
    _ ≤ (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers * horizon) /
          (n + 1 : ℝ) +
        ((n : ℝ) * ((1 - uniformizedBirthProbability trafficIntensity : ℝ≥0) : ℝ) *
          (1 - (trafficIntensity : ℝ))) / threshold :=
      add_le_add hclock_div hembedded_div

/-- The centered canonical correction is measurable. -/
theorem measurable_manyServerMarkedCanonicalCenteredUnrealizedPotentialServiceCorrection
    (servers : ℕ) (time : ℝ) :
    Measurable
      (manyServerMarkedCanonicalCenteredUnrealizedPotentialServiceCorrection
        servers time) := by
  unfold manyServerMarkedCanonicalCenteredUnrealizedPotentialServiceCorrection
  let embeddedSum : (ℕ → ℕ × Bool) × ℕ → ℝ := fun value =>
    manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum
      servers value.2 value.1
  have hembeddedSum : Measurable embeddedSum := by
    apply measurable_from_prod_countable_left
    intro index
    exact
      measurable_manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum
        servers index
  let clockIndex : ((ℕ → ℕ × Bool) × (ℕ → ℝ)) →
      (ℕ → ℕ × Bool) × ℕ := fun value =>
    (value.1, PoissonProcess.canonicalRenewalCount time value.2)
  have hclockIndex : Measurable clockIndex :=
    measurable_fst.prodMk
      ((PoissonProcess.measurable_canonicalRenewalCount time).comp measurable_snd)
  change Measurable (embeddedSum ∘ clockIndex)
  exact hembeddedSum.comp hclockIndex

/-- The canonical-clock embedded idle-fraction compensator is measurable. -/
theorem measurable_manyServerMarkedCanonicalUnrealizedPotentialServiceCompensator
    (servers : ℕ) (time : ℝ) :
    Measurable
      (manyServerMarkedCanonicalUnrealizedPotentialServiceCompensator
        servers time) := by
  unfold manyServerMarkedCanonicalUnrealizedPotentialServiceCompensator
  let embeddedCompensator : (ℕ → ℕ × Bool) × ℕ → ℝ := fun value =>
    manyServerMarkedStateUnrealizedPotentialServiceCompensatorPrefix
      servers value.1 value.2
  have hembeddedCompensator : Measurable embeddedCompensator := by
    apply measurable_from_prod_countable_left
    intro index
    exact
      measurable_manyServerMarkedStateUnrealizedPotentialServiceCompensatorPrefix
        servers index
  let clockIndex : ((ℕ → ℕ × Bool) × (ℕ → ℝ)) →
      (ℕ → ℕ × Bool) × ℕ := fun value =>
    (value.1, PoissonProcess.canonicalRenewalCount time value.2)
  have hclockIndex : Measurable clockIndex :=
    measurable_fst.prodMk
      ((PoissonProcess.measurable_canonicalRenewalCount time).comp measurable_snd)
  change Measurable (embeddedCompensator ∘ clockIndex)
  exact hembeddedCompensator.comp hclockIndex

/-- The canonical embedded idle-fraction compensator is nonnegative and
bounded by the number of elapsed potential events. -/
theorem manyServerMarkedCanonicalUnrealizedPotentialServiceCompensator_nonneg_le_clock
    (servers : ℕ) (hservers : 0 < servers)
    (time : ℝ) (value : (ℕ → ℕ × Bool) × (ℕ → ℝ)) :
    0 ≤ manyServerMarkedCanonicalUnrealizedPotentialServiceCompensator
      servers time value ∧
    manyServerMarkedCanonicalUnrealizedPotentialServiceCompensator
      servers time value ≤ PoissonProcess.canonicalRenewalCount time value.2 := by
  unfold manyServerMarkedCanonicalUnrealizedPotentialServiceCompensator
  exact manyServerMarkedStateUnrealizedPotentialServiceCompensatorPrefix_nonneg_le
    servers hservers value.1 (PoissonProcess.canonicalRenewalCount time value.2)

/-- In the stable stationary M/M/n construction, the expected unrealized
potential-service compensator over a physical interval is exactly the total
spare service capacity times the interval length. -/
theorem integral_stationaryManyServerMarkedCanonical_unrealizedPotentialServiceCompensator
    (trafficIntensity : ℝ≥0) (serviceRate : ℝ) (servers : ℕ)
    (hservers : 0 < servers) (htraffic_pos : 0 < trafficIntensity)
    (htraffic_lt_one : trafficIntensity < 1) (hserviceRate : 0 < serviceRate)
    (time : ℝ) (htime : 0 ≤ time) :
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    let initial := manyServerStationaryPMF (trafficIntensity : ℝ) servers
      (by positivity) (by exact_mod_cast htraffic_lt_one)
    let trajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    let gaps := PoissonProcess.exponentialInterarrivalMeasure rate
    (∫ value,
      manyServerMarkedCanonicalUnrealizedPotentialServiceCompensator
        servers time value ∂trajectory.prod gaps) =
      (servers : ℝ) * serviceRate * time * (1 - (trafficIntensity : ℝ)) := by
  let rate : ℝ := manyServerUniformizationRate
    (trafficIntensity : ℝ) serviceRate servers
  let initial : PMF ℕ := manyServerStationaryPMF (trafficIntensity : ℝ) servers
    (by positivity) (by exact_mod_cast htraffic_lt_one)
  let trajectory : Measure (ℕ → ℕ × Bool) := stationaryTrajMeasure
    (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
    (manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers)
  let gaps : Measure (ℕ → ℝ) :=
    PoissonProcess.exponentialInterarrivalMeasure rate
  let source : Measure ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := trajectory.prod gaps
  let compensator : ((ℕ → ℕ × Bool) × (ℕ → ℝ)) → ℝ :=
    manyServerMarkedCanonicalUnrealizedPotentialServiceCompensator servers time
  let idle : ℕ → (ℕ → ℕ × Bool) → ℝ := fun index path =>
    if (path index).2 then 0 else
      1 - (manyServerBusyFraction servers (path index).1 : ℝ)
  have hrate : 0 < rate := by
    exact manyServerUniformizationRate_pos trafficIntensity serviceRate servers hservers hserviceRate
  letI : IsProbabilityMeasure (manyServerMarkedStatePMF initial trafficIntensity).toMeasure := by
    unfold manyServerMarkedStatePMF
    infer_instance
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsProbabilityMeasure gaps :=
    PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure source := by
    dsimp [source]
    infer_instance
  letI : IsFiniteMeasure source := by infer_instance
  have hcompensator_meas : Measurable compensator :=
    measurable_manyServerMarkedCanonicalUnrealizedPotentialServiceCompensator servers time
  have hcount : Integrable (fun value : (ℕ → ℕ × Bool) × (ℕ → ℝ) =>
      (PoissonProcess.canonicalRenewalCount time value.2 : ℝ)) source := by
    have hcount_gaps := PoissonProcess.integrable_canonicalRenewalCount hrate htime
    have hpreserve : MeasurePreserving Prod.snd (trajectory.prod gaps) gaps :=
      measurePreserving_snd
    simpa [source, Function.comp_def] using
      (hpreserve.integrable_comp hcount_gaps.aestronglyMeasurable).mpr hcount_gaps
  have hcompensator_int : Integrable compensator source := by
    apply hcount.mono' hcompensator_meas.aestronglyMeasurable
    filter_upwards [] with value
    rcases manyServerMarkedCanonicalUnrealizedPotentialServiceCompensator_nonneg_le_clock
      servers hservers time value with ⟨hnonneg, hle⟩
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    exact hle
  have hidle_int : ∀ index, Integrable (idle index) trajectory := by
    intro index
    have hmeas : Measurable (idle index) := by
      dsimp [idle]
      exact (measurable_of_countable (fun current : ℕ × Bool =>
        if current.2 then 0 else 1 - (manyServerBusyFraction servers current.1 : ℝ))).comp
          (measurable_pi_apply index)
    apply Integrable.of_bound hmeas.aestronglyMeasurable 1
    filter_upwards [] with path
    cases hmark : (path index).2 with
    | true => simp [idle, hmark]
    | false =>
        have hbusy_nonneg : 0 ≤ (manyServerBusyFraction servers (path index).1 : ℝ) := by
          positivity
        have hbusy_le : (manyServerBusyFraction servers (path index).1 : ℝ) ≤ 1 := by
          exact_mod_cast manyServerBusyFraction_le_one servers (path index).1 hservers
        rw [show idle index path = 1 - (manyServerBusyFraction servers (path index).1 : ℝ) by
          simp [idle, hmark], Real.norm_eq_abs, abs_of_nonneg (by linarith)]
        linarith
  have hidle_expect : ∀ index,
      (∫ path, idle index path ∂trajectory) =
        ((1 - uniformizedBirthProbability trafficIntensity : ℝ≥0) : ℝ) *
          (1 - (trafficIntensity : ℝ)) := by
    intro index
    dsimp [idle, trajectory, initial]
    exact integral_stationaryManyServerMarkedStateTrajectory_idleFraction
      trafficIntensity servers hservers htraffic_pos htraffic_lt_one index
  have hinner : ∀ gap : ℕ → ℝ,
      (∫ path, compensator (path, gap) ∂trajectory) =
        (PoissonProcess.canonicalRenewalCount time gap : ℝ) *
          (((1 - uniformizedBirthProbability trafficIntensity : ℝ≥0) : ℝ) *
            (1 - (trafficIntensity : ℝ))) := by
    intro gap
    let count : ℕ := PoissonProcess.canonicalRenewalCount time gap
    change (∫ path, (∑ index ∈ Finset.range count, idle index path) ∂trajectory) = _
    rw [integral_finset_sum]
    · simp_rw [hidle_expect]
      simp [count]
    · intro index _
      exact hidle_int index
  change (∫ value, compensator value ∂source) = _
  calc
    (∫ value, compensator value ∂source) =
        ∫ gap, ∫ path, compensator (path, gap) ∂trajectory ∂gaps := by
          exact MeasureTheory.integral_prod_symm _ hcompensator_int
    _ = ∫ gap, (PoissonProcess.canonicalRenewalCount time gap : ℝ) *
          (((1 - uniformizedBirthProbability trafficIntensity : ℝ≥0) : ℝ) *
            (1 - (trafficIntensity : ℝ))) ∂gaps := by
          apply integral_congr_ae
          filter_upwards [] with gap
          exact hinner gap
    _ = (rate * time) *
          (((1 - uniformizedBirthProbability trafficIntensity : ℝ≥0) : ℝ) *
            (1 - (trafficIntensity : ℝ))) := by
          have hrewrite : (fun gap : ℕ → ℝ =>
            (PoissonProcess.canonicalRenewalCount time gap : ℝ) *
              (((1 - uniformizedBirthProbability trafficIntensity : ℝ≥0) : ℝ) *
                (1 - (trafficIntensity : ℝ)))) =
              (fun gap => (((1 - uniformizedBirthProbability trafficIntensity : ℝ≥0) : ℝ) *
                (1 - (trafficIntensity : ℝ))) *
                  (PoissonProcess.canonicalRenewalCount time gap : ℝ)) := by
                    funext gap
                    ring
          rw [hrewrite,
            MeasureTheory.integral_const_mul,
            PoissonProcess.integral_canonicalRenewalCount hrate htime]
          ring
    _ = (servers : ℝ) * serviceRate * time * (1 - (trafficIntensity : ℝ)) := by
          have hpotentialRate : rate *
              ((1 - uniformizedBirthProbability trafficIntensity : ℝ≥0) : ℝ) =
              (servers : ℝ) * serviceRate := by
                exact manyServerUniformizationRate_potentialService
                  trafficIntensity serviceRate servers
          calc
            (rate * time) *
                (((1 - uniformizedBirthProbability trafficIntensity : ℝ≥0) : ℝ) *
                  (1 - (trafficIntensity : ℝ))) =
                (rate * ((1 - uniformizedBirthProbability trafficIntensity : ℝ≥0) : ℝ)) *
                  time * (1 - (trafficIntensity : ℝ)) := by ring
            _ = (servers : ℝ) * serviceRate * time * (1 - (trafficIntensity : ℝ)) := by
              rw [hpotentialRate]

/-- The canonical centered correction has second moment at most the expected
time-changed embedded idle-fraction compensator.  This is the physical-time,
random-clock form of the embedded predictable-variance bound; the coarser
clock-count estimate is a corollary. -/
theorem manyServerMarkedCanonicalCenteredUnrealizedPotentialServiceCorrection_secondMoment_le_integral_compensator
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers : ℕ) (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    (time : ℝ) (htime : 0 ≤ time) :
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    let trajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    let gaps := PoissonProcess.exponentialInterarrivalMeasure rate
    (∫ value,
      (manyServerMarkedCanonicalCenteredUnrealizedPotentialServiceCorrection
        servers time value) ^ 2 ∂trajectory.prod gaps) ≤
      ∫ value, manyServerMarkedCanonicalUnrealizedPotentialServiceCompensator
        servers time value ∂trajectory.prod gaps := by
  let rate : ℝ := manyServerUniformizationRate
    (trafficIntensity : ℝ) serviceRate servers
  let trajectory : Measure (ℕ → ℕ × Bool) := stationaryTrajMeasure
    (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
    (manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers)
  let gaps : Measure (ℕ → ℝ) :=
    PoissonProcess.exponentialInterarrivalMeasure rate
  let source : Measure ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := trajectory.prod gaps
  let correction : ((ℕ → ℕ × Bool) × (ℕ → ℝ)) → ℝ :=
    manyServerMarkedCanonicalCenteredUnrealizedPotentialServiceCorrection servers time
  let compensator : ((ℕ → ℕ × Bool) × (ℕ → ℝ)) → ℝ :=
    manyServerMarkedCanonicalUnrealizedPotentialServiceCompensator servers time
  let idle : ℕ → (ℕ → ℕ × Bool) → ℝ := fun index path =>
    if (path index).2 then 0 else
      1 - (manyServerBusyFraction servers (path index).1 : ℝ)
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  have hrate : 0 < rate := by
    exact manyServerUniformizationRate_pos trafficIntensity serviceRate servers hservers hserviceRate
  letI : IsProbabilityMeasure gaps :=
    PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure source := by
    dsimp [source]
    infer_instance
  letI : IsFiniteMeasure source := by infer_instance
  have hcorrection_meas : Measurable correction := by
    exact measurable_manyServerMarkedCanonicalCenteredUnrealizedPotentialServiceCorrection
      servers time
  have hcompensator_meas : Measurable compensator := by
    exact measurable_manyServerMarkedCanonicalUnrealizedPotentialServiceCompensator
      servers time
  have hpoly : ∀ count : ℕ, (count : ℝ) ^ 2 ≤ (4 : ℝ) ^ count := by
    intro count
    have hcount : (count : ℝ) ≤ (2 : ℝ) ^ count := by
      exact_mod_cast Nat.le_of_lt (Nat.lt_two_pow_self (n := count))
    calc
      (count : ℝ) ^ 2 ≤ ((2 : ℝ) ^ count) ^ 2 :=
        (sq_le_sq₀ (by positivity) (by positivity)).mpr hcount
      _ = (4 : ℝ) ^ count := by
        rw [pow_two, show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]
  have hpow : Integrable (fun gap : ℕ → ℝ =>
      (4 : ℝ) ^ PoissonProcess.canonicalRenewalCount time gap) gaps := by
    exact PoissonProcess.integrable_pow_canonicalRenewalCount hrate htime 4
  have hpow_source : Integrable (fun value : (ℕ → ℕ × Bool) × (ℕ → ℝ) =>
      (4 : ℝ) ^ PoissonProcess.canonicalRenewalCount time value.2) source := by
    have hpreserve : MeasurePreserving Prod.snd (trajectory.prod gaps) gaps :=
      measurePreserving_snd
    simpa [source, Function.comp_def] using
      (hpreserve.integrable_comp hpow.aestronglyMeasurable).mpr hpow
  have hcorrection_sq_int : Integrable (fun value => correction value ^ 2) source := by
    apply hpow_source.mono' (hcorrection_meas.aestronglyMeasurable.pow 2)
    filter_upwards [] with value
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hsum :=
      abs_manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum_le
        servers hservers (PoissonProcess.canonicalRenewalCount time value.2) value.1
    have hsq : correction value ^ 2 ≤
        (PoissonProcess.canonicalRenewalCount time value.2 : ℝ) ^ 2 := by
      apply (sq_le_sq).mpr
      have hcount_nonneg :
          0 ≤ (PoissonProcess.canonicalRenewalCount time value.2 : ℝ) := by positivity
      simpa [abs_of_nonneg hcount_nonneg, correction,
        manyServerMarkedCanonicalCenteredUnrealizedPotentialServiceCorrection] using hsum
    exact hsq.trans (hpoly (PoissonProcess.canonicalRenewalCount time value.2))
  have hcount : Integrable (fun value : (ℕ → ℕ × Bool) × (ℕ → ℝ) =>
      (PoissonProcess.canonicalRenewalCount time value.2 : ℝ)) source := by
    have hcount_gaps := PoissonProcess.integrable_canonicalRenewalCount hrate htime
    have hpreserve : MeasurePreserving Prod.snd (trajectory.prod gaps) gaps :=
      measurePreserving_snd
    simpa [source, Function.comp_def] using
      (hpreserve.integrable_comp hcount_gaps.aestronglyMeasurable).mpr hcount_gaps
  have hcompensator_int : Integrable compensator source := by
    apply hcount.mono' hcompensator_meas.aestronglyMeasurable
    filter_upwards [] with value
    rcases manyServerMarkedCanonicalUnrealizedPotentialServiceCompensator_nonneg_le_clock
      servers hservers time value with ⟨hnonneg, hle⟩
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    exact hle
  have hidle_int : ∀ index, Integrable (idle index) trajectory := by
    intro index
    have hmeas : Measurable (idle index) := by
      dsimp [idle]
      exact (measurable_of_countable (fun current : ℕ × Bool =>
        if current.2 then 0 else
          1 - (manyServerBusyFraction servers current.1 : ℝ))).comp
        (measurable_pi_apply index)
    apply Integrable.of_bound hmeas.aestronglyMeasurable 1
    filter_upwards [] with path
    dsimp [idle]
    cases hmark : (path index).2 with
    | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        have hbusy_nonneg :
            0 ≤ (manyServerBusyFraction servers (path index).1 : ℝ) := by positivity
        have hbusy_le :
            (manyServerBusyFraction servers (path index).1 : ℝ) ≤ 1 := by
          exact_mod_cast
            manyServerBusyFraction_le_one servers (path index).1 hservers
        rw [abs_of_nonneg (by linarith)]
        linarith
    | true => simp
  have hinner_correction_int : Integrable (fun gap : ℕ → ℝ =>
      ∫ path, correction (path, gap) ^ 2 ∂trajectory) gaps := by
    have hfactor := (MeasureTheory.integrable_prod_iff
      hcorrection_sq_int.swap.aestronglyMeasurable).mp hcorrection_sq_int.swap
    convert hfactor.2 using 1
    ext gap
    congr 1
    funext path
    simp only [Function.comp_apply, Prod.swap_prod_mk]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hinner_compensator_int : Integrable (fun gap : ℕ → ℝ =>
      ∫ path, compensator (path, gap) ∂trajectory) gaps := by
    have hfactor := (MeasureTheory.integrable_prod_iff
      hcompensator_int.swap.aestronglyMeasurable).mp hcompensator_int.swap
    convert hfactor.2 using 1
    ext gap
    congr 1
    funext path
    have hnonneg := (manyServerMarkedCanonicalUnrealizedPotentialServiceCompensator_nonneg_le_clock
      servers hservers time (path, gap)).1
    change compensator (path, gap) = |compensator (path, gap)|
    rw [abs_of_nonneg (by simpa [compensator] using hnonneg)]
  have hinner_le : ∀ gap : ℕ → ℝ,
      (∫ path, correction (path, gap) ^ 2 ∂trajectory) ≤
        ∫ path, compensator (path, gap) ∂trajectory := by
    intro gap
    let count : ℕ := PoissonProcess.canonicalRenewalCount time gap
    have hcomp_integral :
        (∫ path, compensator (path, gap) ∂trajectory) =
          ∑ index ∈ Finset.range count, ∫ path, idle index path ∂trajectory := by
      change (∫ path, (∑ index ∈ Finset.range count, idle index path) ∂trajectory) = _
      rw [integral_finset_sum]
      intro index _
      exact hidle_int index
    calc
      (∫ path, correction (path, gap) ^ 2 ∂trajectory) ≤
          ∑ index ∈ Finset.range count, ∫ path, idle index path ∂trajectory := by
            simpa [count, correction, idle, trajectory] using
              manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum_secondMoment_le_sum_expectedIdleFraction_from_initial
                initial trafficIntensity servers hservers
                (PoissonProcess.canonicalRenewalCount time gap)
      _ = ∫ path, compensator (path, gap) ∂trajectory := hcomp_integral.symm
  change (∫ value, correction value ^ 2 ∂source) ≤
    ∫ value, compensator value ∂source
  calc
    (∫ value, correction value ^ 2 ∂source) =
        ∫ gap, ∫ path, correction (path, gap) ^ 2 ∂trajectory ∂gaps := by
          exact MeasureTheory.integral_prod_symm _ hcorrection_sq_int
    _ ≤ ∫ gap, ∫ path, compensator (path, gap) ∂trajectory ∂gaps := by
      apply integral_mono_ae hinner_correction_int hinner_compensator_int
      exact Filter.Eventually.of_forall hinner_le
    _ = ∫ value, compensator value ∂source := by
      exact (MeasureTheory.integral_prod_symm _ hcompensator_int).symm

/-- The continuous-time centered correction inherits the embedded martingale's
second-moment bound through the independent canonical Poisson clock. -/
theorem manyServerMarkedCanonicalCenteredUnrealizedPotentialServiceCorrection_secondMoment_le
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers : ℕ) (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    (time : ℝ) (htime : 0 ≤ time) :
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    let trajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    let gaps := PoissonProcess.exponentialInterarrivalMeasure rate
    (∫ value,
      (manyServerMarkedCanonicalCenteredUnrealizedPotentialServiceCorrection
        servers time value) ^ 2 ∂trajectory.prod gaps) ≤ rate * time := by
  let rate : ℝ := manyServerUniformizationRate
    (trafficIntensity : ℝ) serviceRate servers
  let trajectory : Measure (ℕ → ℕ × Bool) := stationaryTrajMeasure
    (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
    (manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers)
  let gaps : Measure (ℕ → ℝ) :=
    PoissonProcess.exponentialInterarrivalMeasure rate
  let source : Measure ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := trajectory.prod gaps
  let correction : ((ℕ → ℕ × Bool) × (ℕ → ℝ)) → ℝ :=
    manyServerMarkedCanonicalCenteredUnrealizedPotentialServiceCorrection servers time
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  have hrate : 0 < rate := by
    exact manyServerUniformizationRate_pos trafficIntensity serviceRate servers hservers hserviceRate
  letI : IsProbabilityMeasure gaps :=
    PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure source := by
    dsimp [source]
    infer_instance
  letI : IsFiniteMeasure source := by infer_instance
  have hcorrection_meas : Measurable correction := by
    exact
      measurable_manyServerMarkedCanonicalCenteredUnrealizedPotentialServiceCorrection
        servers time
  have hpoly : ∀ count : ℕ, (count : ℝ) ^ 2 ≤ (4 : ℝ) ^ count := by
    intro count
    have hcount : (count : ℝ) ≤ (2 : ℝ) ^ count := by
      exact_mod_cast Nat.le_of_lt (Nat.lt_two_pow_self (n := count))
    calc
      (count : ℝ) ^ 2 ≤ ((2 : ℝ) ^ count) ^ 2 :=
        (sq_le_sq₀ (by positivity) (by positivity)).mpr hcount
      _ = (4 : ℝ) ^ count := by
        rw [pow_two, show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]
  have hpow : Integrable (fun gaps : ℕ → ℝ =>
      (4 : ℝ) ^ PoissonProcess.canonicalRenewalCount time gaps) gaps := by
    exact PoissonProcess.integrable_pow_canonicalRenewalCount hrate htime 4
  have hpow_source : Integrable (fun value : (ℕ → ℕ × Bool) × (ℕ → ℝ) =>
      (4 : ℝ) ^ PoissonProcess.canonicalRenewalCount time value.2) source := by
    have hpreserve : MeasurePreserving Prod.snd (trajectory.prod gaps) gaps :=
      measurePreserving_snd
    simpa [source, Function.comp_def] using
      (hpreserve.integrable_comp hpow.aestronglyMeasurable).mpr hpow
  have hcorrection_sq_int : Integrable (fun value => correction value ^ 2) source := by
    apply hpow_source.mono' (hcorrection_meas.aestronglyMeasurable.pow 2)
    filter_upwards [] with value
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hsum :=
      abs_manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum_le
        servers hservers (PoissonProcess.canonicalRenewalCount time value.2) value.1
    have hsq : correction value ^ 2 ≤
        (PoissonProcess.canonicalRenewalCount time value.2 : ℝ) ^ 2 := by
      apply (sq_le_sq).mpr
      have hcount_nonneg :
          0 ≤ (PoissonProcess.canonicalRenewalCount time value.2 : ℝ) := by positivity
      simpa [abs_of_nonneg hcount_nonneg, correction,
        manyServerMarkedCanonicalCenteredUnrealizedPotentialServiceCorrection] using hsum
    exact hsq.trans (hpoly (PoissonProcess.canonicalRenewalCount time value.2))
  have hinner_integrable : Integrable (fun gap : ℕ → ℝ =>
      ∫ path, correction (path, gap) ^ 2 ∂trajectory) gaps := by
    have hfactor := (MeasureTheory.integrable_prod_iff
      hcorrection_sq_int.swap.aestronglyMeasurable).mp hcorrection_sq_int.swap
    convert hfactor.2 using 1
    ext gap
    congr 1
    funext path
    simp only [Function.comp_apply, Prod.swap_prod_mk]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  change (∫ value, correction value ^ 2 ∂source) ≤ rate * time
  calc
    (∫ value, correction value ^ 2 ∂source) =
        ∫ gap, ∫ path, correction (path, gap) ^ 2 ∂trajectory ∂gaps := by
          exact MeasureTheory.integral_prod_symm _ hcorrection_sq_int
    _ ≤ ∫ gap, (PoissonProcess.canonicalRenewalCount time gap : ℝ) ∂gaps := by
      apply integral_mono_ae hinner_integrable
        (PoissonProcess.integrable_canonicalRenewalCount hrate htime)
      filter_upwards [] with gap
      simpa [correction,
        manyServerMarkedCanonicalCenteredUnrealizedPotentialServiceCorrection,
        trajectory, gaps, rate] using
        manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum_secondMoment_le_from_initial
          initial trafficIntensity servers hservers
          (PoissonProcess.canonicalRenewalCount time gap)
    _ = rate * time := by
      exact PoissonProcess.integral_canonicalRenewalCount hrate htime

/-- On the actual canonical marked path, the literal unrealized potential
service count is the finite prefix sum of the corresponding embedded
increments. -/
theorem ae_manyServerMarkedCanonicalUnrealizedPotentialServiceCount_eq_prefix_from_initial
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers : ℕ) (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    (time : ℝ) :
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    ∀ᵐ value ∂((stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)).prod
      (PoissonProcess.exponentialInterarrivalMeasure rate)),
      manyServerMarkedCanonicalUnrealizedPotentialServiceCount time value =
        manyServerMarkedStateUnrealizedPotentialServicePrefix value.1
          (PoissonProcess.canonicalRenewalCount time value.2) := by
  dsimp only
  let rate : ℝ := manyServerUniformizationRate
    (trafficIntensity : ℝ) serviceRate servers
  let trajectory : Measure (ℕ → ℕ × Bool) := stationaryTrajMeasure
    (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
    (manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers)
  let gaps : Measure (ℕ → ℝ) :=
    PoissonProcess.exponentialInterarrivalMeasure rate
  let source : Measure ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := trajectory.prod gaps
  have hrate : 0 < rate := by
    exact manyServerUniformizationRate_pos trafficIntensity serviceRate servers hservers hserviceRate
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsProbabilityMeasure gaps :=
    PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  change ∀ᵐ value ∂source,
    manyServerMarkedCanonicalUnrealizedPotentialServiceCount time value =
      manyServerMarkedStateUnrealizedPotentialServicePrefix value.1
        (PoissonProcess.canonicalRenewalCount time value.2)
  have hsteps : ∀ᵐ value ∂source,
      ∀ index : ℕ,
        ManyServerMarkedStateStepAllowed (value.1 index) (value.1 (index + 1)) := by
    refine ae_of_ae_map (μ := source) (f := Prod.fst)
      (p := fun path : ℕ → ℕ × Bool =>
        ∀ index : ℕ,
          ManyServerMarkedStateStepAllowed (path index) (path (index + 1)))
      measurable_fst.aemeasurable ?_
    rw [show Measure.map Prod.fst source = trajectory by
      dsimp [source]
      rw [Measure.map_fst_prod, measure_univ, one_smul]]
    exact ae_all_manyServerMarkedStateTrajectory_stepAllowed_from_initial
      initial trafficIntensity servers hservers
  filter_upwards [hsteps] with value hvalue
  let steps := PoissonProcess.canonicalRenewalCount time value.2
  have hunrealized :=
    manyServerMarkedStateUnrealizedPotentialServicePrefix_eq_potentialServicePrefix_sub_departurePrefix
      value.1 hvalue steps
  have hpotential := manyServerMarkedStatePotentialServicePrefix_eq_discardedInMarks
    value.1 steps
  rw [hpotential] at hunrealized
  simpa [steps, manyServerMarkedCanonicalUnrealizedPotentialServiceCount,
    manyServerMarkedCanonicalPotentialServiceCount,
    manyServerMarkedCanonicalDepartureCount,
    manyServerMarkedCanonicalHorizonSample,
    FiniteHorizonMarkedPoisson.discarded, Function.comp_def] using hunrealized.symm

/-- The literal canonical unrealized-potential-service count is its predictable
compensator plus the centered correction, outside a single null event. -/
theorem ae_manyServerMarkedCanonicalUnrealizedPotentialServiceCount_sub_compensator_eq_centeredCorrection_from_initial
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers : ℕ) (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    (time : ℝ) :
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    ∀ᵐ value ∂((stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)).prod
      (PoissonProcess.exponentialInterarrivalMeasure rate)),
      (manyServerMarkedCanonicalUnrealizedPotentialServiceCount time value : ℝ) -
          manyServerMarkedCanonicalUnrealizedPotentialServiceCompensator
            servers time value =
        manyServerMarkedCanonicalCenteredUnrealizedPotentialServiceCorrection
          servers time value := by
  have hraw := ae_manyServerMarkedCanonicalUnrealizedPotentialServiceCount_eq_prefix_from_initial
    initial trafficIntensity serviceRate servers hservers hserviceRate time
  filter_upwards [hraw] with value hvalue
  rw [hvalue]
  exact
    (manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum_eq_unrealizedPotentialServicePrefix_sub_compensator
      servers value.1 (PoissonProcess.canonicalRenewalCount time value.2)).symm

/-- The literal unrealized-potential-service count has the same predictable
compensator-plus-centered-correction decomposition simultaneously at every
real time on one common full-measure trajectory event.  This is the pathwise
form needed when a finite-horizon correction estimate is used in a functional
diffusion argument. -/
theorem ae_forall_manyServerMarkedCanonicalUnrealizedPotentialServiceCount_sub_compensator_eq_centeredCorrection_from_initial
    (initial : PMF ℕ) (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers : ℕ) (hservers : 0 < servers) (hserviceRate : 0 < serviceRate) :
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    ∀ᵐ value ∂((stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)).prod
      (PoissonProcess.exponentialInterarrivalMeasure rate)),
      ∀ time : ℝ,
        (manyServerMarkedCanonicalUnrealizedPotentialServiceCount time value : ℝ) -
            manyServerMarkedCanonicalUnrealizedPotentialServiceCompensator
              servers time value =
          manyServerMarkedCanonicalCenteredUnrealizedPotentialServiceCorrection
            servers time value := by
  dsimp only
  let rate : ℝ := manyServerUniformizationRate
    (trafficIntensity : ℝ) serviceRate servers
  let trajectory : Measure (ℕ → ℕ × Bool) := stationaryTrajMeasure
    (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
    (manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers)
  let gaps : Measure (ℕ → ℝ) :=
    PoissonProcess.exponentialInterarrivalMeasure rate
  let source : Measure ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := trajectory.prod gaps
  have hrate : 0 < rate := by
    exact manyServerUniformizationRate_pos trafficIntensity serviceRate
      servers hservers hserviceRate
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsProbabilityMeasure gaps :=
    PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  change ∀ᵐ value ∂source, ∀ time : ℝ,
    (manyServerMarkedCanonicalUnrealizedPotentialServiceCount time value : ℝ) -
        manyServerMarkedCanonicalUnrealizedPotentialServiceCompensator
          servers time value =
      manyServerMarkedCanonicalCenteredUnrealizedPotentialServiceCorrection
        servers time value
  have hsteps : ∀ᵐ value ∂source,
      ∀ index : ℕ,
        ManyServerMarkedStateStepAllowed (value.1 index) (value.1 (index + 1)) := by
    refine ae_of_ae_map (μ := source) (f := Prod.fst)
      (p := fun path : ℕ → ℕ × Bool =>
        ∀ index : ℕ,
          ManyServerMarkedStateStepAllowed (path index) (path (index + 1)))
      measurable_fst.aemeasurable ?_
    rw [show Measure.map Prod.fst source = trajectory by
      dsimp [source]
      rw [Measure.map_fst_prod, measure_univ, one_smul]]
    exact ae_all_manyServerMarkedStateTrajectory_stepAllowed_from_initial
      initial trafficIntensity servers hservers
  filter_upwards [hsteps] with value hvalue
  intro time
  let steps := PoissonProcess.canonicalRenewalCount time value.2
  have hunrealized :=
    manyServerMarkedStateUnrealizedPotentialServicePrefix_eq_potentialServicePrefix_sub_departurePrefix
      value.1 hvalue steps
  have hpotential := manyServerMarkedStatePotentialServicePrefix_eq_discardedInMarks
    value.1 steps
  rw [hpotential] at hunrealized
  have hprefix :
      manyServerMarkedCanonicalUnrealizedPotentialServiceCount time value =
        manyServerMarkedStateUnrealizedPotentialServicePrefix value.1 steps := by
    simpa [steps, manyServerMarkedCanonicalUnrealizedPotentialServiceCount,
      manyServerMarkedCanonicalPotentialServiceCount,
      manyServerMarkedCanonicalDepartureCount,
      manyServerMarkedCanonicalHorizonSample,
      FiniteHorizonMarkedPoisson.discarded, Function.comp_def] using hunrealized.symm
  rw [hprefix]
  exact
    (manyServerMarkedStateCenteredUnrealizedPotentialServicePartialSum_eq_unrealizedPotentialServicePrefix_sub_compensator
      servers value.1 steps).symm

/-- The queue-length coordinate of the actual marked embedded path at a
canonical clock horizon. -/
def manyServerMarkedCanonicalQueueLength (time : ℝ) :
    ((ℕ → ℕ × Bool) × (ℕ → ℝ)) → ℕ :=
  fun value => (value.1 (PoissonProcess.canonicalRenewalCount time value.2)).1

/-- The physical-time queue length obtained from the marked canonical event
trajectory. -/
noncomputable def manyServerMarkedCanonicalQueueLengthOnReal
    (value : (ℕ → ℕ × Bool) × (ℕ → ℝ)) : ℝ → ℕ :=
  fun time => manyServerMarkedCanonicalQueueLength time value

/-- The instantaneous idle fraction of the physical-time marked queue.  This
depends only on the queue coordinate, not on the mark selected for the next
potential event. -/
noncomputable def manyServerMarkedCanonicalIdleFractionOnReal
    (servers : ℕ) (value : (ℕ → ℕ × Bool) × (ℕ → ℝ)) : ℝ → ℝ :=
  fun time => 1 - (manyServerBusyFraction servers
    (manyServerMarkedCanonicalQueueLength time value) : ℝ)

/-- The marked physical-time idle fraction is jointly Borel measurable in
the full canonical input and physical time. -/
theorem measurable_manyServerMarkedCanonicalIdleFractionOnReal_joint
    (servers : ℕ) :
    Measurable (fun point : ((ℕ → ℕ × Bool) × (ℕ → ℝ)) × ℝ =>
      manyServerMarkedCanonicalIdleFractionOnReal servers point.1 point.2) := by
  let stateAt : (ℕ → ℕ × Bool) × ℕ → ℕ × Bool := fun value =>
    value.1 value.2
  have hstateAt : Measurable stateAt := by
    apply measurable_from_prod_countable_left
    intro index
    exact measurable_pi_apply index
  let clockAt : ((ℕ → ℕ × Bool) × (ℕ → ℝ)) × ℝ → ℕ := fun point =>
    PoissonProcess.canonicalRenewalCount point.2 point.1.2
  have hclockAt : Measurable clockAt := by
    exact PoissonProcess.measurable_canonicalRenewalCount_joint.comp
      (measurable_snd.prodMk (measurable_snd.comp measurable_fst))
  let currentState : ((ℕ → ℕ × Bool) × (ℕ → ℝ)) × ℝ → ℕ × Bool := fun point =>
    stateAt (point.1.1, clockAt point)
  have hcurrentState : Measurable currentState := by
    exact hstateAt.comp ((measurable_fst.comp measurable_fst).prodMk hclockAt)
  exact (measurable_of_countable fun state : ℕ × Bool =>
    1 - (manyServerBusyFraction servers state.1 : ℝ)).comp hcurrentState

/-- The physical-time occupation of the idle fraction over the interval from
zero to `time`.  Multiplying this quantity by the total potential-service rate
gives the state-dependent unused-service compensator of an M/M/s queue; the
comparison with the embedded-event reward is a separate stochastic estimate. -/
noncomputable def manyServerMarkedCanonicalIdleFractionOccupation
    (servers : ℕ) (time : ℝ) (value : (ℕ → ℕ × Bool) × (ℕ → ℝ)) : ℝ :=
  ∫ u in (0 : ℝ)..time,
    manyServerMarkedCanonicalIdleFractionOnReal servers value u

/-- At each fixed physical time, the marked idle-fraction occupation is
Borel measurable in the canonical input. -/
theorem measurable_manyServerMarkedCanonicalIdleFractionOccupation
    (servers : ℕ) (time : ℝ) :
    Measurable (manyServerMarkedCanonicalIdleFractionOccupation servers time) := by
  let idle : ((ℕ → ℕ × Bool) × (ℕ → ℝ)) → ℝ → ℝ := fun value u =>
    manyServerMarkedCanonicalIdleFractionOnReal servers value u
  have hidle : StronglyMeasurable (Function.uncurry idle) := by
    exact (measurable_manyServerMarkedCanonicalIdleFractionOnReal_joint servers).stronglyMeasurable
  have hforward : StronglyMeasurable (fun value =>
      ∫ u, idle value u ∂(MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) time))) :=
    hidle.integral_prod_right
  have hreverse : StronglyMeasurable (fun value =>
      ∫ u, idle value u ∂(MeasureTheory.volume.restrict (Set.Ioc time (0 : ℝ)))) :=
    hidle.integral_prod_right
  simpa [manyServerMarkedCanonicalIdleFractionOccupation, idle,
    intervalIntegral] using (hforward.sub hreverse).measurable

/-- The physical occupation of the idle fraction is continuous whenever the
underlying renewal clock is monotone and nonexplosive. -/
theorem continuous_manyServerMarkedCanonicalIdleFractionOccupation_of_clock
    (servers : ℕ) (value : (ℕ → ℕ × Bool) × (ℕ → ℝ))
    (hdiverges : Filter.Tendsto
      (fun index : ℕ => PoissonProcess.arrivalTime index value.2)
      Filter.atTop Filter.atTop)
    (hmono : Monotone
      (fun index : ℕ => PoissonProcess.arrivalTime index value.2)) :
    Continuous (fun time : ℝ =>
      manyServerMarkedCanonicalIdleFractionOccupation servers time value) := by
  simpa [manyServerMarkedCanonicalIdleFractionOccupation,
    manyServerMarkedCanonicalIdleFractionOnReal,
    manyServerMarkedCanonicalQueueLength] using
    (PoissonProcess.continuous_intervalIntegral_canonicalRenewalCount_value
      (fun index : ℕ => 1 -
        (manyServerBusyFraction servers (value.1 index).1 : ℝ))
      value.2 hdiverges hmono)

/-- The instantaneous physical idle fraction lies between zero and one. -/
theorem manyServerMarkedCanonicalIdleFractionOnReal_nonneg_le_one
    (servers : ℕ) (hservers : 0 < servers)
    (value : (ℕ → ℕ × Bool) × (ℕ → ℝ)) (time : ℝ) :
    0 ≤ manyServerMarkedCanonicalIdleFractionOnReal servers value time ∧
      manyServerMarkedCanonicalIdleFractionOnReal servers value time ≤ 1 := by
  unfold manyServerMarkedCanonicalIdleFractionOnReal
  have hbusy_nonneg : 0 ≤
      (manyServerBusyFraction servers
        (manyServerMarkedCanonicalQueueLength time value) : ℝ) := by
    positivity
  have hbusy_le :
      (manyServerBusyFraction servers
        (manyServerMarkedCanonicalQueueLength time value) : ℝ) ≤ 1 := by
    exact_mod_cast manyServerBusyFraction_le_one servers
      (manyServerMarkedCanonicalQueueLength time value) hservers
  constructor <;> linarith

/-- The physical idle-fraction occupation is nonnegative on every
nonnegative time interval. -/
theorem manyServerMarkedCanonicalIdleFractionOccupation_nonneg
    (servers : ℕ) (hservers : 0 < servers) {time : ℝ} (htime : 0 ≤ time)
    (value : (ℕ → ℕ × Bool) × (ℕ → ℝ)) :
    0 ≤ manyServerMarkedCanonicalIdleFractionOccupation servers time value := by
  unfold manyServerMarkedCanonicalIdleFractionOccupation
  apply intervalIntegral.integral_nonneg htime
  intro u _
  exact (manyServerMarkedCanonicalIdleFractionOnReal_nonneg_le_one
    servers hservers value u).1

/-- On a nonnegative interval, idle-fraction occupation is at most elapsed
physical time. -/
theorem manyServerMarkedCanonicalIdleFractionOccupation_le_time
    (servers : ℕ) (hservers : 0 < servers) {time : ℝ} (htime : 0 ≤ time)
    (value : (ℕ → ℕ × Bool) × (ℕ → ℝ)) :
    manyServerMarkedCanonicalIdleFractionOccupation servers time value ≤ time := by
  have hnonneg := manyServerMarkedCanonicalIdleFractionOccupation_nonneg
    servers hservers htime value
  have hnorm :
      ‖manyServerMarkedCanonicalIdleFractionOccupation servers time value‖ ≤
        (1 : ℝ) * |time - 0| := by
    unfold manyServerMarkedCanonicalIdleFractionOccupation
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro u _
    have hbound := manyServerMarkedCanonicalIdleFractionOnReal_nonneg_le_one
      servers hservers value u
    rw [Real.norm_eq_abs, abs_of_nonneg hbound.1]
    exact hbound.2
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg] at hnorm
  simpa [abs_of_nonneg htime] using hnorm

/-- Under a nonexplosive monotone renewal clock, idle-fraction occupation is
one-Lipschitz in physical time.  The bound is the deterministic consequence
of the instantaneous idle fraction lying in `[0, 1]`. -/
theorem abs_sub_manyServerMarkedCanonicalIdleFractionOccupation_le_abs_sub_of_clock
    (servers : ℕ) (hservers : 0 < servers)
    (value : (ℕ → ℕ × Bool) × (ℕ → ℝ))
    (hdiverges : Filter.Tendsto
      (fun index : ℕ => PoissonProcess.arrivalTime index value.2) Filter.atTop Filter.atTop)
    (hmono : Monotone
      (fun index : ℕ => PoissonProcess.arrivalTime index value.2))
    (first second : ℝ) :
    |manyServerMarkedCanonicalIdleFractionOccupation servers second value -
        manyServerMarkedCanonicalIdleFractionOccupation servers first value| ≤
      |second - first| := by
  let values : ℕ → ℝ := fun index =>
    1 - (manyServerBusyFraction servers (value.1 index).1 : ℝ)
  have hintegrable : ∀ lower upper : ℝ,
      IntervalIntegrable (fun time : ℝ => values
        (PoissonProcess.canonicalRenewalCount time value.2)) volume lower upper := by
    intro lower upper
    exact PoissonProcess.intervalIntegrable_canonicalRenewalCount_value
      values value.2 hdiverges hmono lower upper
  have hdifference :
      manyServerMarkedCanonicalIdleFractionOccupation servers second value -
          manyServerMarkedCanonicalIdleFractionOccupation servers first value =
        ∫ time in first..second, values
          (PoissonProcess.canonicalRenewalCount time value.2) := by
    simpa [manyServerMarkedCanonicalIdleFractionOccupation,
      manyServerMarkedCanonicalIdleFractionOnReal,
      manyServerMarkedCanonicalQueueLength, values] using
      (intervalIntegral.integral_interval_sub_left
        (hintegrable 0 second) (hintegrable 0 first))
  rw [hdifference, ← Real.norm_eq_abs]
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := first) (b := second) (C := (1 : ℝ))
    (f := fun time : ℝ => values (PoissonProcess.canonicalRenewalCount time value.2))
    (fun time _ => by
      change |1 - (manyServerBusyFraction servers
        (value.1 (PoissonProcess.canonicalRenewalCount time value.2)).1 : ℝ)| ≤ 1
      rw [abs_of_nonneg]
      · exact (manyServerMarkedCanonicalIdleFractionOnReal_nonneg_le_one
          servers hservers value time).2
      · exact (manyServerMarkedCanonicalIdleFractionOnReal_nonneg_le_one
          servers hservers value time).1)
  simpa using hnorm

/-- Project a marked embedded trajectory to its queue-state path while
retaining the independent canonical clock. -/
def manyServerMarkedCanonicalQueueProjection :
    ((ℕ → ℕ × Bool) × (ℕ → ℝ)) → (ℕ → ℕ) × (ℕ → ℝ) :=
  Prod.map (fun path index => (path index).1) id

theorem measurable_manyServerMarkedCanonicalQueueProjection :
    Measurable manyServerMarkedCanonicalQueueProjection := by
  exact (measurable_pi_lambda _ fun index =>
    measurable_fst.comp (measurable_pi_apply index)).prodMap measurable_id

/-- The centered square-root marked queue path, before selecting its bundled
local-Skorokhod version. -/
noncomputable def manyServerMarkedCenteredSqrtCanonicalTrajectoryOnReal
    (servers : ℕ) (value : (ℕ → ℕ × Bool) × (ℕ → ℝ)) : ℝ → ℝ :=
  manyServerCenteredSqrtPath servers
    (manyServerMarkedCanonicalQueueLengthOnReal value)

/-- A total local-`J₁` version of the marked canonical queue path.  It is
defined by the measurable mark-forgetting projection, so its law can be
identified exactly with the unmarked canonical path law. -/
noncomputable def manyServerMarkedCenteredSqrtCanonicalSkorokhodPath
    (servers : ℕ) (value : (ℕ → ℕ × Bool) × (ℕ → ℝ)) :
    SkorokhodJ1LocalPath ℝ :=
  manyServerCenteredSqrtCanonicalSkorokhodPath servers
    (manyServerMarkedCanonicalQueueProjection value)

/-- The marked canonical queue length has almost surely càdlàg physical-time
paths. -/
theorem ae_isCadlagPath_manyServerMarkedCanonicalQueueLengthOnReal
    {initial : PMF ℕ} (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers : ℕ) (hservers : 0 < servers) (hserviceRate : 0 < serviceRate) :
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    let trajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    let gaps := PoissonProcess.exponentialInterarrivalMeasure rate
    ∀ᵐ value ∂trajectory.prod gaps,
      IsCadlagPath (manyServerMarkedCanonicalQueueLengthOnReal value) := by
  simpa [manyServerMarkedCanonicalQueueLengthOnReal,
    manyServerMarkedCanonicalQueueLength] using
    (ae_isCadlagPath_manyServerMarkedCanonical_clock_comp
      (initial := initial) trafficIntensity serviceRate servers hservers hserviceRate
      (fun path index => (path index).1))

/-- Projecting the complete marked trajectory while retaining the independent
canonical clock gives exactly the unmarked canonical input law. -/
theorem map_manyServerMarkedCanonicalQueueProjection_eq_unmarked
    {initial : PMF ℕ} (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers : ℕ) (hservers : 0 < servers) (hserviceRate : 0 < serviceRate) :
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    let markedTrajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    let unmarkedTrajectory := manyServerUniformizedEmbeddedTrajectoryMeasure
      initial.toMeasure trafficIntensity servers hservers
    let gaps := PoissonProcess.exponentialInterarrivalMeasure rate
    Measure.map manyServerMarkedCanonicalQueueProjection
      (markedTrajectory.prod gaps) = unmarkedTrajectory.prod gaps := by
  dsimp only
  let rate : ℝ := manyServerUniformizationRate
    (trafficIntensity : ℝ) serviceRate servers
  let markedTrajectory : Measure (ℕ → ℕ × Bool) := stationaryTrajMeasure
    (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
    (manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers)
  let unmarkedTrajectory : Measure (ℕ → ℕ) :=
    manyServerUniformizedEmbeddedTrajectoryMeasure
      initial.toMeasure trafficIntensity servers hservers
  let gaps : Measure (ℕ → ℝ) :=
    PoissonProcess.exponentialInterarrivalMeasure rate
  let forgetMark : (ℕ → ℕ × Bool) → ℕ → ℕ :=
    fun path index => (path index).1
  have hrate : 0 < rate := by
    exact manyServerUniformizationRate_pos trafficIntensity serviceRate
      servers hservers hserviceRate
  letI : IsProbabilityMeasure markedTrajectory := by
    dsimp [markedTrajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsProbabilityMeasure gaps :=
    PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  have hforgetMark : Measurable forgetMark := by
    apply measurable_pi_lambda
    intro index
    exact measurable_fst.comp (measurable_pi_apply index)
  calc
    Measure.map manyServerMarkedCanonicalQueueProjection
        (markedTrajectory.prod gaps) =
        (Measure.map forgetMark markedTrajectory).prod (Measure.map id gaps) := by
          simpa [manyServerMarkedCanonicalQueueProjection, forgetMark] using
            (Measure.map_prod_map markedTrajectory gaps hforgetMark measurable_id).symm
    _ = unmarkedTrajectory.prod gaps := by
          rw [manyServerMarkedStateTrajectory_queuePath_map_eq_unmarked
            initial trafficIntensity servers hservers, Measure.map_id]

/-- Forgetting the retained Boolean marks commutes with the independent
canonical clock.  Hence the full marked physical-time queue-length path has
exactly the same raw path law as the unmarked canonical construction.  This
is a law identity on real-indexed paths, before imposing any local
Skorokhod-path version. -/
theorem map_manyServerMarkedCanonicalQueueLengthOnReal_eq_unmarked
    {initial : PMF ℕ} (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers : ℕ) (hservers : 0 < servers) (hserviceRate : 0 < serviceRate) :
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    let markedTrajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    let unmarkedTrajectory := manyServerUniformizedEmbeddedTrajectoryMeasure
      initial.toMeasure trafficIntensity servers hservers
    let gaps := PoissonProcess.exponentialInterarrivalMeasure rate
    Measure.map manyServerMarkedCanonicalQueueLengthOnReal
      (markedTrajectory.prod gaps) =
      Measure.map manyServerCanonicalQueueLengthOnReal
        (unmarkedTrajectory.prod gaps) := by
  dsimp only
  let rate : ℝ := manyServerUniformizationRate
    (trafficIntensity : ℝ) serviceRate servers
  let markedTrajectory : Measure (ℕ → ℕ × Bool) := stationaryTrajMeasure
    (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
    (manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers)
  let unmarkedTrajectory : Measure (ℕ → ℕ) :=
    manyServerUniformizedEmbeddedTrajectoryMeasure
      initial.toMeasure trafficIntensity servers hservers
  let gaps : Measure (ℕ → ℝ) :=
    PoissonProcess.exponentialInterarrivalMeasure rate
  let forgetMark : (ℕ → ℕ × Bool) → ℕ → ℕ :=
    fun path index => (path index).1
  let clockProjection : ((ℕ → ℕ × Bool) × (ℕ → ℝ)) →
      (ℕ → ℕ) × (ℕ → ℝ) := Prod.map forgetMark id
  have hrate : 0 < rate := by
    exact manyServerUniformizationRate_pos trafficIntensity serviceRate
      servers hservers hserviceRate
  letI : IsProbabilityMeasure markedTrajectory := by
    dsimp [markedTrajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsProbabilityMeasure gaps :=
    PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  have hforgetMark : Measurable forgetMark := by
    apply measurable_pi_lambda
    intro index
    exact measurable_fst.comp (measurable_pi_apply index)
  have hclockProjection : Measurable clockProjection := by
    exact hforgetMark.prodMap measurable_id
  have hprojectedLaw :
      Measure.map clockProjection (markedTrajectory.prod gaps) =
        unmarkedTrajectory.prod gaps := by
    calc
      Measure.map clockProjection (markedTrajectory.prod gaps) =
          (Measure.map forgetMark markedTrajectory).prod (Measure.map id gaps) := by
            simpa [clockProjection] using
              (Measure.map_prod_map markedTrajectory gaps hforgetMark measurable_id).symm
      _ = unmarkedTrajectory.prod gaps := by
            rw [manyServerMarkedStateTrajectory_queuePath_map_eq_unmarked
              initial trafficIntensity servers hservers, Measure.map_id]
  have hraw : manyServerMarkedCanonicalQueueLengthOnReal =
      manyServerCanonicalQueueLengthOnReal ∘ clockProjection := by
    funext value time
    simp [manyServerMarkedCanonicalQueueLengthOnReal,
      manyServerMarkedCanonicalQueueLength,
      manyServerCanonicalQueueLengthOnReal, clockProjection, forgetMark]
  calc
    Measure.map manyServerMarkedCanonicalQueueLengthOnReal
        (markedTrajectory.prod gaps) =
        Measure.map (manyServerCanonicalQueueLengthOnReal ∘ clockProjection)
          (markedTrajectory.prod gaps) := by rw [hraw]
    _ = Measure.map manyServerCanonicalQueueLengthOnReal
          (Measure.map clockProjection (markedTrajectory.prod gaps)) := by
            exact (Measure.map_map measurable_manyServerCanonicalQueueLengthOnReal
              hclockProjection).symm
    _ = Measure.map manyServerCanonicalQueueLengthOnReal
          (unmarkedTrajectory.prod gaps) := by rw [hprojectedLaw]

/-- The projected marked local-`J₁` path is almost-everywhere measurable for
the same Borel structure as the unmarked canonical path. -/
theorem aemeasurable_manyServerMarkedCenteredSqrtCanonicalSkorokhodPath
    {initial : PMF ℕ} (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers : ℕ) (hservers : 0 < servers) (hserviceRate : 0 < serviceRate) :
    letI : UniformSpace (SkorokhodJ1LocalPath ℝ) :=
      SkorokhodJ1LocalEntourage.uniformSpace (State := ℝ)
    letI : MeasurableSpace (SkorokhodJ1LocalPath ℝ) :=
      SkorokhodJ1LocalEntourage.borelMeasurableSpace (State := ℝ)
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    let markedTrajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    let gaps := PoissonProcess.exponentialInterarrivalMeasure rate
    AEMeasurable
      (manyServerMarkedCenteredSqrtCanonicalSkorokhodPath servers)
      (markedTrajectory.prod gaps) := by
  letI : UniformSpace (SkorokhodJ1LocalPath ℝ) :=
    SkorokhodJ1LocalEntourage.uniformSpace (State := ℝ)
  letI : MeasurableSpace (SkorokhodJ1LocalPath ℝ) :=
    SkorokhodJ1LocalEntourage.borelMeasurableSpace (State := ℝ)
  let rate : ℝ := manyServerUniformizationRate
    (trafficIntensity : ℝ) serviceRate servers
  let markedTrajectory : Measure (ℕ → ℕ × Bool) := stationaryTrajMeasure
    (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
    (manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers)
  let unmarkedTrajectory : Measure (ℕ → ℕ) :=
    manyServerUniformizedEmbeddedTrajectoryMeasure
      initial.toMeasure trafficIntensity servers hservers
  let gaps : Measure (ℕ → ℝ) :=
    PoissonProcess.exponentialInterarrivalMeasure rate
  let source := markedTrajectory.prod gaps
  let target := unmarkedTrajectory.prod gaps
  have hprojection :
      Measure.map manyServerMarkedCanonicalQueueProjection source = target := by
    simpa [source, target, markedTrajectory, unmarkedTrajectory, gaps, rate] using
      (map_manyServerMarkedCanonicalQueueProjection_eq_unmarked
        (initial := initial) trafficIntensity serviceRate servers hservers hserviceRate)
  have htarget : AEMeasurable
      (manyServerCenteredSqrtCanonicalSkorokhodPath servers) target := by
    simpa [target, unmarkedTrajectory, gaps, rate] using
      (aemeasurable_manyServerCenteredSqrtCanonicalSkorokhodPath
        (initial := initial.toMeasure) trafficIntensity serviceRate servers
        hservers hserviceRate)
  have htargetOnMap : AEMeasurable
      (manyServerCenteredSqrtCanonicalSkorokhodPath servers)
      (Measure.map manyServerMarkedCanonicalQueueProjection source) := by
    rw [hprojection]
    exact htarget
  simpa [manyServerMarkedCenteredSqrtCanonicalSkorokhodPath,
    Function.comp_def] using
    htargetOnMap.comp_aemeasurable
      measurable_manyServerMarkedCanonicalQueueProjection.aemeasurable

/-- The marked local-`J₁` version has exactly the unmarked canonical path law.
This transports marked primitive-count arguments to the path-space law used
by the M/M/n diffusion statement. -/
theorem map_manyServerMarkedCenteredSqrtCanonicalSkorokhodPath_eq_unmarked
    {initial : PMF ℕ} (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers : ℕ) (hservers : 0 < servers) (hserviceRate : 0 < serviceRate) :
    letI : UniformSpace (SkorokhodJ1LocalPath ℝ) :=
      SkorokhodJ1LocalEntourage.uniformSpace (State := ℝ)
    letI : MeasurableSpace (SkorokhodJ1LocalPath ℝ) :=
      SkorokhodJ1LocalEntourage.borelMeasurableSpace (State := ℝ)
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    let markedTrajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    let unmarkedTrajectory := manyServerUniformizedEmbeddedTrajectoryMeasure
      initial.toMeasure trafficIntensity servers hservers
    let gaps := PoissonProcess.exponentialInterarrivalMeasure rate
    Measure.map (manyServerMarkedCenteredSqrtCanonicalSkorokhodPath servers)
      (markedTrajectory.prod gaps) =
      Measure.map (manyServerCenteredSqrtCanonicalSkorokhodPath servers)
        (unmarkedTrajectory.prod gaps) := by
  letI : UniformSpace (SkorokhodJ1LocalPath ℝ) :=
    SkorokhodJ1LocalEntourage.uniformSpace (State := ℝ)
  letI : MeasurableSpace (SkorokhodJ1LocalPath ℝ) :=
    SkorokhodJ1LocalEntourage.borelMeasurableSpace (State := ℝ)
  let rate : ℝ := manyServerUniformizationRate
    (trafficIntensity : ℝ) serviceRate servers
  let markedTrajectory : Measure (ℕ → ℕ × Bool) := stationaryTrajMeasure
    (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
    (manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers)
  let unmarkedTrajectory : Measure (ℕ → ℕ) :=
    manyServerUniformizedEmbeddedTrajectoryMeasure
      initial.toMeasure trafficIntensity servers hservers
  let gaps : Measure (ℕ → ℝ) :=
    PoissonProcess.exponentialInterarrivalMeasure rate
  let source := markedTrajectory.prod gaps
  let target := unmarkedTrajectory.prod gaps
  have hprojection :
      Measure.map manyServerMarkedCanonicalQueueProjection source = target := by
    simpa [source, target, markedTrajectory, unmarkedTrajectory, gaps, rate] using
      (map_manyServerMarkedCanonicalQueueProjection_eq_unmarked
        (initial := initial) trafficIntensity serviceRate servers hservers hserviceRate)
  have htarget : AEMeasurable
      (manyServerCenteredSqrtCanonicalSkorokhodPath servers) target := by
    simpa [target, unmarkedTrajectory, gaps, rate] using
      (aemeasurable_manyServerCenteredSqrtCanonicalSkorokhodPath
        (initial := initial.toMeasure) trafficIntensity serviceRate servers
        hservers hserviceRate)
  have htargetOnMap : AEMeasurable
      (manyServerCenteredSqrtCanonicalSkorokhodPath servers)
      (Measure.map manyServerMarkedCanonicalQueueProjection source) := by
    rw [hprojection]
    exact htarget
  calc
    Measure.map (manyServerMarkedCenteredSqrtCanonicalSkorokhodPath servers) source =
        Measure.map
          (manyServerCenteredSqrtCanonicalSkorokhodPath servers)
          (Measure.map manyServerMarkedCanonicalQueueProjection source) := by
            exact (htargetOnMap.map_map_of_aemeasurable
              measurable_manyServerMarkedCanonicalQueueProjection.aemeasurable).symm
    _ = Measure.map (manyServerCenteredSqrtCanonicalSkorokhodPath servers) target := by
          rw [hprojection]

/-- On a common full-measure event, the bundled marked local-`J₁` path agrees
at every time with the literal centered and scaled marked queue trajectory. -/
theorem ae_forall_manyServerMarkedCenteredSqrtCanonicalSkorokhodPath_eq
    {initial : PMF ℕ} (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers : ℕ) (hservers : 0 < servers) (hserviceRate : 0 < serviceRate) :
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    let markedTrajectory := stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)
    let gaps := PoissonProcess.exponentialInterarrivalMeasure rate
    ∀ᵐ value ∂markedTrajectory.prod gaps, ∀ time : ℝ,
      manyServerMarkedCenteredSqrtCanonicalSkorokhodPath servers value time =
        manyServerMarkedCenteredSqrtCanonicalTrajectoryOnReal servers value time := by
  let rate : ℝ := manyServerUniformizationRate
    (trafficIntensity : ℝ) serviceRate servers
  let markedTrajectory : Measure (ℕ → ℕ × Bool) := stationaryTrajMeasure
    (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
    (manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers)
  let unmarkedTrajectory : Measure (ℕ → ℕ) :=
    manyServerUniformizedEmbeddedTrajectoryMeasure
      initial.toMeasure trafficIntensity servers hservers
  let gaps : Measure (ℕ → ℝ) :=
    PoissonProcess.exponentialInterarrivalMeasure rate
  let source := markedTrajectory.prod gaps
  let target := unmarkedTrajectory.prod gaps
  have hprojection :
      Measure.map manyServerMarkedCanonicalQueueProjection source = target := by
    simpa [source, target, markedTrajectory, unmarkedTrajectory, gaps, rate] using
      (map_manyServerMarkedCanonicalQueueProjection_eq_unmarked
        (initial := initial) trafficIntensity serviceRate servers hservers hserviceRate)
  have htarget : ∀ᵐ z ∂target, ∀ time : ℝ,
      manyServerCenteredSqrtCanonicalSkorokhodPath servers z time =
        manyServerCenteredSqrtCanonicalTrajectoryOnReal servers z time := by
    simpa [target, unmarkedTrajectory, gaps, rate] using
      (ae_forall_manyServerCenteredSqrtCanonicalSkorokhodPath_eq
        (initial := initial.toMeasure) trafficIntensity serviceRate servers
        hservers hserviceRate)
  have htargetOnMap : ∀ᵐ z ∂Measure.map manyServerMarkedCanonicalQueueProjection source,
      ∀ time : ℝ,
        manyServerCenteredSqrtCanonicalSkorokhodPath servers z time =
          manyServerCenteredSqrtCanonicalTrajectoryOnReal servers z time := by
    rw [hprojection]
    exact htarget
  have hsource := ae_of_ae_map
    measurable_manyServerMarkedCanonicalQueueProjection.aemeasurable htargetOnMap
  filter_upwards [hsource] with value hvalue
  intro time
  simpa [manyServerMarkedCenteredSqrtCanonicalSkorokhodPath,
    manyServerMarkedCenteredSqrtCanonicalTrajectoryOnReal,
    manyServerCenteredSqrtCanonicalTrajectoryOnReal,
    manyServerCenteredSqrtPath, manyServerCanonicalQueueLengthOnReal,
    manyServerMarkedCanonicalQueueLengthOnReal,
    manyServerMarkedCanonicalQueueLength,
    manyServerMarkedCanonicalQueueProjection] using hvalue time

/-- The arrival and potential-service counts from the canonical marked
uniformization, retained as an ordered pair. -/
def manyServerMarkedCanonicalArrivalPotentialCounts (time : ℝ) :
    ((ℕ → ℕ × Bool) × (ℕ → ℝ)) → ℕ × ℕ :=
  FiniteHorizonMarkedPoisson.splitCounts ∘
    manyServerMarkedCanonicalHorizonSample time

/-- The two mark classes in an actual physical interval are precisely the
increments of the corresponding canonical marked-event counts.  This is a
pathwise finite-block identity: the retained interval marks are the tail of
the original mark vector after the events already present at `start`. -/
theorem ae_manyServerMarkedCanonicalIntervalSample_splitCounts_eq_increments
    {initial : PMF ℕ} (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers : ℕ) (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    {start duration : ℝ} (hduration : 0 ≤ duration) :
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    ∀ᵐ value ∂((stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)).prod
      (PoissonProcess.exponentialInterarrivalMeasure rate)),
      FiniteHorizonMarkedPoisson.splitCounts
        (manyServerMarkedCanonicalIntervalSample start duration value) =
        (manyServerMarkedCanonicalArrivalCount (start + duration) value -
            manyServerMarkedCanonicalArrivalCount start value,
          manyServerMarkedCanonicalPotentialServiceCount (start + duration) value -
            manyServerMarkedCanonicalPotentialServiceCount start value) := by
  dsimp only
  let rate : ℝ := manyServerUniformizationRate
    (trafficIntensity : ℝ) serviceRate servers
  let trajectory : Measure (ℕ → ℕ × Bool) := stationaryTrajMeasure
    (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
    (manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers)
  let gaps : Measure (ℕ → ℝ) :=
    PoissonProcess.exponentialInterarrivalMeasure rate
  let source : Measure ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := trajectory.prod gaps
  have hrate : 0 < rate := by
    exact manyServerUniformizationRate_pos trafficIntensity serviceRate
      servers hservers hserviceRate
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsProbabilityMeasure gaps :=
    PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  change ∀ᵐ value ∂source,
    FiniteHorizonMarkedPoisson.splitCounts
      (manyServerMarkedCanonicalIntervalSample start duration value) =
      (manyServerMarkedCanonicalArrivalCount (start + duration) value -
          manyServerMarkedCanonicalArrivalCount start value,
        manyServerMarkedCanonicalPotentialServiceCount (start + duration) value -
          manyServerMarkedCanonicalPotentialServiceCount start value)
  have hclock : ∀ᵐ value ∂source,
      PoissonProcess.canonicalRenewalCount (start + duration) value.2 =
        PoissonProcess.canonicalRenewalCount start value.2 +
          PoissonProcess.canonicalRenewalCount duration
            (PoissonProcess.residualTail start value.2) := by
    refine ae_of_ae_map (μ := source) (f := Prod.snd)
      (p := fun clock : ℕ → ℝ =>
        PoissonProcess.canonicalRenewalCount (start + duration) clock =
          PoissonProcess.canonicalRenewalCount start clock +
            PoissonProcess.canonicalRenewalCount duration
              (PoissonProcess.residualTail start clock))
      measurable_snd.aemeasurable ?_
    rw [show Measure.map Prod.snd source = gaps by
      dsimp [source]
      rw [Measure.map_snd_prod, measure_univ, one_smul]]
    exact PoissonProcess.ae_canonicalRenewalCount_add_eq_residualTailCount
      hrate start duration hduration
  filter_upwards [hclock] with value hvalue
  let m := PoissonProcess.canonicalRenewalCount start value.2
  let n := PoissonProcess.canonicalRenewalCount duration
    (PoissonProcess.residualTail start value.2)
  have hfinal :
      PoissonProcess.canonicalRenewalCount (start + duration) value.2 = m + n := by
    simpa [m, n] using hvalue
  change FiniteHorizonMarkedPoisson.splitCounts
      (manyServerMarkedCanonicalIntervalSample start duration value) =
      (FiniteHorizonMarkedPoisson.kept
          (manyServerMarkedCanonicalHorizonSample (start + duration) value) -
          FiniteHorizonMarkedPoisson.kept
            (manyServerMarkedCanonicalHorizonSample start value),
        FiniteHorizonMarkedPoisson.discarded
          (manyServerMarkedCanonicalHorizonSample (start + duration) value) -
          FiniteHorizonMarkedPoisson.discarded
            (manyServerMarkedCanonicalHorizonSample start value))
  unfold FiniteHorizonMarkedPoisson.kept FiniteHorizonMarkedPoisson.discarded
    manyServerMarkedCanonicalHorizonSample
  rw [hfinal]
  change
    (FiniteHorizonMarkedPoisson.keptInMarks
        (fun i : Fin n => (value.1 (m + i)).2),
      FiniteHorizonMarkedPoisson.discardedInMarks
        (fun i : Fin n => (value.1 (m + i)).2)) =
      (FiniteHorizonMarkedPoisson.keptInMarks
          (fun i : Fin (m + n) => (value.1 i).2) -
          FiniteHorizonMarkedPoisson.keptInMarks
            (fun i : Fin m => (value.1 i).2),
        FiniteHorizonMarkedPoisson.discardedInMarks
          (fun i : Fin (m + n) => (value.1 i).2) -
          FiniteHorizonMarkedPoisson.discardedInMarks
            (fun i : Fin m => (value.1 i).2))
  apply Prod.ext
  · change FiniteHorizonMarkedPoisson.keptInMarks
        (fun i : Fin n => (value.1 (m + i)).2) =
        FiniteHorizonMarkedPoisson.keptInMarks
          (fun i : Fin (m + n) => (value.1 i).2) -
          FiniteHorizonMarkedPoisson.keptInMarks
            (fun i : Fin m => (value.1 i).2)
    exact FiniteHorizonMarkedPoisson.keptInMarks_tail_eq_sub (m := m) (n := n)
      (fun i : Fin (m + n) => (value.1 i).2)
  · change FiniteHorizonMarkedPoisson.discardedInMarks
        (fun i : Fin n => (value.1 (m + i)).2) =
        FiniteHorizonMarkedPoisson.discardedInMarks
          (fun i : Fin (m + n) => (value.1 i).2) -
          FiniteHorizonMarkedPoisson.discardedInMarks
            (fun i : Fin m => (value.1 i).2)
    exact FiniteHorizonMarkedPoisson.discardedInMarks_tail_eq_sub (m := m) (n := n)
      (fun i : Fin (m + n) => (value.1 i).2)

/-- Over a nonnegative deterministic interval, the marked arrival and
potential-service counts split additively into their value at the interval
start and the literal counts in the intervening marked sample.  This is the
pathwise count identity underlying independent-increment arguments. -/
theorem ae_manyServerMarkedCanonicalArrivalPotentialCount_add_interval
    {initial : PMF ℕ} (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers : ℕ) (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    {start duration : ℝ} (hduration : 0 ≤ duration) :
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    ∀ᵐ value ∂((stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)).prod
      (PoissonProcess.exponentialInterarrivalMeasure rate)),
      (manyServerMarkedCanonicalArrivalCount (start + duration) value,
        manyServerMarkedCanonicalPotentialServiceCount (start + duration) value) =
        (manyServerMarkedCanonicalArrivalCount start value,
          manyServerMarkedCanonicalPotentialServiceCount start value) +
          FiniteHorizonMarkedPoisson.splitCounts
            (manyServerMarkedCanonicalIntervalSample start duration value) := by
  dsimp only
  let rate : ℝ := manyServerUniformizationRate
    (trafficIntensity : ℝ) serviceRate servers
  let trajectory : Measure (ℕ → ℕ × Bool) := stationaryTrajMeasure
    (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
    (manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers)
  let gaps : Measure (ℕ → ℝ) :=
    PoissonProcess.exponentialInterarrivalMeasure rate
  let source : Measure ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := trajectory.prod gaps
  have hrate : 0 < rate := by
    exact manyServerUniformizationRate_pos trafficIntensity serviceRate
      servers hservers hserviceRate
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsProbabilityMeasure gaps :=
    PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  change ∀ᵐ value ∂source,
    (manyServerMarkedCanonicalArrivalCount (start + duration) value,
      manyServerMarkedCanonicalPotentialServiceCount (start + duration) value) =
      (manyServerMarkedCanonicalArrivalCount start value,
        manyServerMarkedCanonicalPotentialServiceCount start value) +
        FiniteHorizonMarkedPoisson.splitCounts
          (manyServerMarkedCanonicalIntervalSample start duration value)
  have hclock : ∀ᵐ value ∂source,
      PoissonProcess.canonicalRenewalCount (start + duration) value.2 =
        PoissonProcess.canonicalRenewalCount start value.2 +
          PoissonProcess.canonicalRenewalCount duration
            (PoissonProcess.residualTail start value.2) := by
    refine ae_of_ae_map (μ := source) (f := Prod.snd)
      (p := fun clock : ℕ → ℝ =>
        PoissonProcess.canonicalRenewalCount (start + duration) clock =
          PoissonProcess.canonicalRenewalCount start clock +
            PoissonProcess.canonicalRenewalCount duration
              (PoissonProcess.residualTail start clock))
      measurable_snd.aemeasurable ?_
    rw [show Measure.map Prod.snd source = gaps by
      dsimp [source]
      rw [Measure.map_snd_prod, measure_univ, one_smul]]
    exact PoissonProcess.ae_canonicalRenewalCount_add_eq_residualTailCount
      hrate start duration hduration
  filter_upwards [hclock] with value hvalue
  let m := PoissonProcess.canonicalRenewalCount start value.2
  let n := PoissonProcess.canonicalRenewalCount duration
    (PoissonProcess.residualTail start value.2)
  have hfinal :
      PoissonProcess.canonicalRenewalCount (start + duration) value.2 = m + n := by
    simpa [m, n] using hvalue
  change
    (FiniteHorizonMarkedPoisson.kept
        (manyServerMarkedCanonicalHorizonSample (start + duration) value),
      FiniteHorizonMarkedPoisson.discarded
        (manyServerMarkedCanonicalHorizonSample (start + duration) value)) =
      (FiniteHorizonMarkedPoisson.kept
        (manyServerMarkedCanonicalHorizonSample start value),
        FiniteHorizonMarkedPoisson.discarded
          (manyServerMarkedCanonicalHorizonSample start value)) +
        FiniteHorizonMarkedPoisson.splitCounts
          (manyServerMarkedCanonicalIntervalSample start duration value)
  unfold FiniteHorizonMarkedPoisson.kept FiniteHorizonMarkedPoisson.discarded
    FiniteHorizonMarkedPoisson.splitCounts manyServerMarkedCanonicalHorizonSample
    manyServerMarkedCanonicalIntervalSample manyServerMarkedFreshHorizonSample
    manyServerMarkedCanonicalFutureDriver
  rw [hfinal]
  change
    (FiniteHorizonMarkedPoisson.keptInMarks
        (fun i : Fin (m + n) => (value.1 i).2),
      FiniteHorizonMarkedPoisson.discardedInMarks
        (fun i : Fin (m + n) => (value.1 i).2)) =
      (FiniteHorizonMarkedPoisson.keptInMarks
        (fun i : Fin m => (value.1 i).2),
        FiniteHorizonMarkedPoisson.discardedInMarks
          (fun i : Fin m => (value.1 i).2)) +
        (FiniteHorizonMarkedPoisson.keptInMarks
          (fun i : Fin n => (value.1 (m + i)).2),
          FiniteHorizonMarkedPoisson.discardedInMarks
            (fun i : Fin n => (value.1 (m + i)).2))
  apply Prod.ext
  · have hsplit := Fin.append_castAdd_natAdd
      (f := fun i : Fin (m + n) => (value.1 i).2)
    rw [← hsplit]
    exact FiniteHorizonMarkedPoisson.keptInMarks_append
      (fun i : Fin m => (value.1 i).2)
      (fun i : Fin n => (value.1 (m + i)).2)
  · have hsplit := Fin.append_castAdd_natAdd
      (f := fun i : Fin (m + n) => (value.1 i).2)
    rw [← hsplit]
    exact FiniteHorizonMarkedPoisson.discardedInMarks_append
      (fun i : Fin m => (value.1 i).2)
      (fun i : Fin n => (value.1 (m + i)).2)

/-- The ordered arrival and potential-service count increments in each
consecutive interval of a finite deterministic partition. -/
noncomputable def manyServerMarkedCanonicalIntervalIncrementList (start : ℝ) :
    List (ℝ≥0) → ((ℕ → ℕ × Bool) × (ℕ → ℝ)) → List (ℕ × ℕ)
  | [], _ => []
  | duration :: durations, value =>
      (manyServerMarkedCanonicalArrivalCount (start + (duration : ℝ)) value -
          manyServerMarkedCanonicalArrivalCount start value,
        manyServerMarkedCanonicalPotentialServiceCount (start + (duration : ℝ)) value -
          manyServerMarkedCanonicalPotentialServiceCount start value) ::
        manyServerMarkedCanonicalIntervalIncrementList
          (start + (duration : ℝ)) durations value

/-- Splitting every literal marked sample in a finite deterministic partition
returns the actual arrival and potential-service count increments. -/
theorem ae_list_map_markedSplitCounts_intervalSampleList_eq_incrementList
    {initial : PMF ℕ} (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers : ℕ) (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    (start : ℝ) (durations : List (ℝ≥0)) :
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    let source :=
      (stationaryTrajMeasure
        (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
        (manyServerMarkedStateUniformizationMeasureKernel
          trafficIntensity servers hservers)).prod
        (PoissonProcess.exponentialInterarrivalMeasure rate)
    ∀ᵐ value ∂source,
      List.map (FiniteHorizonMarkedPoisson.splitCounts :
        FiniteHorizonMarkedPoisson.Sample → ℕ × ℕ)
        (manyServerMarkedCanonicalIntervalSampleList start durations value) =
        manyServerMarkedCanonicalIntervalIncrementList start durations value := by
  dsimp only
  let rate := manyServerUniformizationRate
    (trafficIntensity : ℝ) serviceRate servers
  let trajectory := stationaryTrajMeasure
    (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
    (manyServerMarkedStateUniformizationMeasureKernel trafficIntensity servers hservers)
  let gaps := PoissonProcess.exponentialInterarrivalMeasure rate
  let source := trajectory.prod gaps
  induction durations generalizing start with
  | nil =>
      filter_upwards [] with value
      rfl
  | cons duration durations ih =>
      have hhead : ∀ᵐ value ∂source,
          FiniteHorizonMarkedPoisson.splitCounts
            (manyServerMarkedCanonicalIntervalSample start (duration : ℝ) value) =
            (manyServerMarkedCanonicalArrivalCount (start + (duration : ℝ)) value -
              manyServerMarkedCanonicalArrivalCount start value,
            manyServerMarkedCanonicalPotentialServiceCount (start + (duration : ℝ)) value -
              manyServerMarkedCanonicalPotentialServiceCount start value) := by
        simpa [source, trajectory, gaps, rate] using
          (ae_manyServerMarkedCanonicalIntervalSample_splitCounts_eq_increments
            (initial := initial) trafficIntensity serviceRate servers hservers hserviceRate
            (start := start) (duration := (duration : ℝ)) duration.2)
      have htail : ∀ᵐ value ∂source,
          List.map (FiniteHorizonMarkedPoisson.splitCounts :
            FiniteHorizonMarkedPoisson.Sample → ℕ × ℕ)
            (manyServerMarkedCanonicalIntervalSampleList
              (start + (duration : ℝ)) durations value) =
            manyServerMarkedCanonicalIntervalIncrementList
              (start + (duration : ℝ)) durations value := by
        exact ih (start := start + (duration : ℝ))
      filter_upwards [hhead, htail] with value hheadValue htailValue
      change FiniteHorizonMarkedPoisson.splitCounts
          (manyServerMarkedCanonicalIntervalSample start (duration : ℝ) value) ::
          List.map (FiniteHorizonMarkedPoisson.splitCounts :
            FiniteHorizonMarkedPoisson.Sample → ℕ × ℕ)
            (manyServerMarkedCanonicalIntervalSampleList
              (start + (duration : ℝ)) durations value) =
        (manyServerMarkedCanonicalArrivalCount (start + (duration : ℝ)) value -
            manyServerMarkedCanonicalArrivalCount start value,
          manyServerMarkedCanonicalPotentialServiceCount (start + (duration : ℝ)) value -
            manyServerMarkedCanonicalPotentialServiceCount start value) ::
          manyServerMarkedCanonicalIntervalIncrementList
            (start + (duration : ℝ)) durations value
      rw [hheadValue, htailValue]

/-- The count pair at a deterministic horizon together with the actual
arrival and potential-service count increments in every later block of a
finite deterministic partition. -/
noncomputable def manyServerMarkedCanonicalHorizon_intervalIncrementList
    (start : ℝ) (durations : List (ℝ≥0)) :
    ((ℕ → ℕ × Bool) × (ℕ → ℝ)) → (ℕ × ℕ) × List (ℕ × ℕ) :=
  fun value =>
    (manyServerMarkedCanonicalArrivalPotentialCounts start value,
      manyServerMarkedCanonicalIntervalIncrementList start durations value)

/-- The actual count pair at a deterministic horizon and every subsequent
interval increment have the iterated product of the corresponding thinned
Poisson laws. -/
theorem manyServerMarkedCanonicalHorizon_intervalIncrementList_hasLaw
    {initial : PMF ℕ} (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers : ℕ) (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    {start : ℝ} (hstart : 0 ≤ start) (durations : List (ℝ≥0)) :
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    let firstMean : ℝ≥0 := ⟨rate * start, mul_nonneg
      (le_of_lt (manyServerUniformizationRate_pos trafficIntensity serviceRate
        servers hservers hserviceRate)) hstart⟩
    let arrivalProbability := uniformizedBirthProbability trafficIntensity
    let tailMeans : List (ℝ≥0) :=
      durations.map fun (duration : ℝ≥0) =>
        ⟨rate * (duration : ℝ), mul_nonneg
          (le_of_lt (manyServerUniformizationRate_pos trafficIntensity serviceRate
            servers hservers hserviceRate)) duration.2⟩
    HasLaw (manyServerMarkedCanonicalHorizon_intervalIncrementList start durations)
      ((((ProbabilityTheory.poissonMeasure (firstMean * arrivalProbability)).prod
        (ProbabilityTheory.poissonMeasure
          (firstMean * (1 - arrivalProbability)))).prod
        (poissonCountPairListMeasure
          (tailMeans.map fun mean =>
            (ProbabilityTheory.poissonMeasure (mean * arrivalProbability)).prod
              (ProbabilityTheory.poissonMeasure
                (mean * (1 - arrivalProbability)))))))
      ((stationaryTrajMeasure
        (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
        (manyServerMarkedStateUniformizationMeasureKernel
          trafficIntensity servers hservers)).prod
        (PoissonProcess.exponentialInterarrivalMeasure rate)) := by
  dsimp only
  let rate : ℝ := manyServerUniformizationRate
    (trafficIntensity : ℝ) serviceRate servers
  let source : Measure ((ℕ → ℕ × Bool) × (ℕ → ℝ)) :=
    (stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)).prod
      (PoissonProcess.exponentialInterarrivalMeasure rate)
  have hraw := manyServerMarkedCanonicalHorizon_splitCountList_hasLaw
    (initial := initial) trafficIntensity serviceRate servers hservers hserviceRate hstart durations
  dsimp only at hraw
  have hsample : ∀ᵐ value ∂source,
      manyServerMarkedFreshSampleList durations
        (manyServerMarkedCanonicalFutureDriver start value) =
        manyServerMarkedCanonicalIntervalSampleList start durations value := by
    simpa [source, rate] using
      (ae_manyServerMarkedFreshSampleList_canonicalFutureDriver_eq_intervalSampleList
        (initial := initial) trafficIntensity serviceRate servers hservers hserviceRate start durations)
  have hincrement : ∀ᵐ value ∂source,
      List.map (FiniteHorizonMarkedPoisson.splitCounts :
        FiniteHorizonMarkedPoisson.Sample → ℕ × ℕ)
        (manyServerMarkedCanonicalIntervalSampleList start durations value) =
        manyServerMarkedCanonicalIntervalIncrementList start durations value := by
    simpa [source, rate] using
      (ae_list_map_markedSplitCounts_intervalSampleList_eq_incrementList
        (initial := initial) trafficIntensity serviceRate servers hservers hserviceRate start durations)
  have hactual :
      manyServerMarkedCanonicalHorizon_intervalIncrementList start durations =ᵐ[source]
        manyServerMarkedCanonicalHorizon_splitCountList start durations := by
    filter_upwards [hsample, hincrement] with value hsampleValue hincrementValue
    change
      (FiniteHorizonMarkedPoisson.splitCounts
        (manyServerMarkedCanonicalHorizonSample start value),
        manyServerMarkedCanonicalIntervalIncrementList start durations value) =
      (FiniteHorizonMarkedPoisson.splitCounts
        (manyServerMarkedCanonicalHorizonSample start value),
        List.map (FiniteHorizonMarkedPoisson.splitCounts :
          FiniteHorizonMarkedPoisson.Sample → ℕ × ℕ)
          (manyServerMarkedFreshSampleList durations
            (manyServerMarkedCanonicalFutureDriver start value)))
    rw [hsampleValue, hincrementValue]
  exact hraw.congr hactual

/-- The actual arrival and potential-service count increments in a finite
deterministic partition, represented as a finite vector. -/
noncomputable def manyServerMarkedCanonicalIntervalIncrementVector
    (start : ℝ) (durations : List (ℝ≥0)) :
    ((ℕ → ℕ × Bool) × (ℕ → ℝ)) → Fin durations.length → ℕ × ℕ :=
  fun value => countPairListToFinFunction durations.length
    (manyServerMarkedCanonicalIntervalIncrementList start durations value)

/-- The finite vector of actual partition increments has the corresponding
product law of thinned Poisson count pairs. -/
theorem manyServerMarkedCanonicalIntervalIncrementVector_hasLaw
    {initial : PMF ℕ} (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers : ℕ) (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    {start : ℝ} (hstart : 0 ≤ start) (durations : List (ℝ≥0)) :
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    let tailMeans : List (ℝ≥0) :=
      durations.map fun (duration : ℝ≥0) =>
        ⟨rate * (duration : ℝ), mul_nonneg
          (le_of_lt (manyServerUniformizationRate_pos trafficIntensity serviceRate
            servers hservers hserviceRate)) duration.2⟩
    let tailLaws := tailMeans.map fun mean =>
      (ProbabilityTheory.poissonMeasure
        (mean * uniformizedBirthProbability trafficIntensity)).prod
      (ProbabilityTheory.poissonMeasure
        (mean * (1 - uniformizedBirthProbability trafficIntensity)))
    HasLaw (manyServerMarkedCanonicalIntervalIncrementVector start durations)
      (Measure.map
        (finFunctionReindex (α := ℕ × ℕ)
          (by simp only [tailMeans, tailLaws, List.length_map]))
        (poissonCountPairFiniteProductMeasure tailLaws))
      ((stationaryTrajMeasure
        (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
        (manyServerMarkedStateUniformizationMeasureKernel
          trafficIntensity servers hservers)).prod
        (PoissonProcess.exponentialInterarrivalMeasure rate)) := by
  dsimp only
  have hwhole := manyServerMarkedCanonicalHorizon_intervalIncrementList_hasLaw
    (initial := initial) trafficIntensity serviceRate servers hservers hserviceRate
    hstart durations
  dsimp only at hwhole
  let tailMeans : List (ℝ≥0) := durations.map fun (duration : ℝ≥0) =>
    ⟨manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers *
        (duration : ℝ),
      mul_nonneg
        (le_of_lt (manyServerUniformizationRate_pos trafficIntensity serviceRate
          servers hservers hserviceRate)) duration.2⟩
  let tailLaws : List (Measure (ℕ × ℕ)) := tailMeans.map fun mean =>
    (ProbabilityTheory.poissonMeasure
      (mean * uniformizedBirthProbability trafficIntensity)).prod
    (ProbabilityTheory.poissonMeasure
      (mean * (1 - uniformizedBirthProbability trafficIntensity)))
  let tailLaw := poissonCountPairFiniteProductMeasure tailLaws
  have hvector : HasLaw
      (fun omega => countPairListToFinFunction tailLaws.length
        (manyServerMarkedCanonicalHorizon_intervalIncrementList start durations omega).2)
      tailLaw
      ((stationaryTrajMeasure
        (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
        (manyServerMarkedStateUniformizationMeasureKernel
          trafficIntensity servers hservers)).prod
        (PoissonProcess.exponentialInterarrivalMeasure
          (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers))) := by
    simpa only [tailMeans, tailLaws, tailLaw] using
      ProbabilityTheory.HasLaw.snd_countPairListToFinFunction hwhole
  let reindex : (Fin tailLaws.length → ℕ × ℕ) → Fin durations.length → ℕ × ℕ :=
    finFunctionReindex (by simp only [tailMeans, tailLaws, List.length_map])
  have hreindex : HasLaw reindex (Measure.map reindex tailLaw) tailLaw := by
    exact ⟨Measurable.of_discrete.aemeasurable, rfl⟩
  simpa only [tailMeans, tailLaws, tailLaw,
    manyServerMarkedCanonicalIntervalIncrementVector, reindex,
    finFunctionReindex, Function.comp_apply] using hreindex.comp hvector

/-- The finite list of uniformization-based interval count laws agrees with
the list whose two coordinates use their physical arrival and potential-
service rates. -/
theorem manyServerMarkedCanonical_intervalTailLaws_eq_physical
    (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers : ℕ) (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    (durations : List (ℝ≥0)) :
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    let tailMeans : List (ℝ≥0) :=
      durations.map fun (duration : ℝ≥0) =>
        ⟨rate * (duration : ℝ), mul_nonneg
          (le_of_lt (manyServerUniformizationRate_pos trafficIntensity serviceRate
            servers hservers hserviceRate)) duration.2⟩
    let tailLaws := tailMeans.map fun mean =>
      (ProbabilityTheory.poissonMeasure
        (mean * uniformizedBirthProbability trafficIntensity)).prod
      (ProbabilityTheory.poissonMeasure
        (mean * (1 - uniformizedBirthProbability trafficIntensity)))
    let physicalTailLaws := durations.map fun (duration : ℝ≥0) =>
      (ProbabilityTheory.poissonMeasure
        (PoissonProcess.rateExposureParam
          ((servers : ℝ) * (trafficIntensity : ℝ) * serviceRate) (duration : ℝ)
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg (by positivity) (by positivity))
              (le_of_lt hserviceRate)) duration.2))).prod
      (ProbabilityTheory.poissonMeasure
        (PoissonProcess.rateExposureParam ((servers : ℝ) * serviceRate) (duration : ℝ)
          (mul_nonneg (mul_nonneg (by positivity) (le_of_lt hserviceRate)) duration.2)))
    tailLaws = physicalTailLaws := by
  dsimp only
  rw [List.map_map]
  apply List.map_congr_left
  intro duration _
  change
    (ProbabilityTheory.poissonMeasure
      (PoissonProcess.rateExposureParam
        (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers)
        (duration : ℝ)
        (mul_nonneg
          (le_of_lt (manyServerUniformizationRate_pos trafficIntensity serviceRate
            servers hservers hserviceRate)) duration.2) *
        uniformizedBirthProbability trafficIntensity)).prod
    (ProbabilityTheory.poissonMeasure
      (PoissonProcess.rateExposureParam
        (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers)
        (duration : ℝ)
        (mul_nonneg
          (le_of_lt (manyServerUniformizationRate_pos trafficIntensity serviceRate
            servers hservers hserviceRate)) duration.2) *
        (1 - uniformizedBirthProbability trafficIntensity))) = _
  congr 1
  · apply congrArg ProbabilityTheory.poissonMeasure
    apply NNReal.eq
    change
      (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers *
          (duration : ℝ)) * (uniformizedBirthProbability trafficIntensity : ℝ) =
        ((servers : ℝ) * (trafficIntensity : ℝ) * serviceRate) * (duration : ℝ)
    calc
      (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers *
          (duration : ℝ)) * (uniformizedBirthProbability trafficIntensity : ℝ) =
          (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers *
            (uniformizedBirthProbability trafficIntensity : ℝ)) * (duration : ℝ) := by
              ring
      _ = ((servers : ℝ) * (trafficIntensity : ℝ) * serviceRate) * (duration : ℝ) := by
        rw [show (uniformizedBirthProbability trafficIntensity : ℝ) =
          (trafficIntensity : ℝ) / (1 + (trafficIntensity : ℝ)) by
            simp [uniformizedBirthProbability],
          manyServerUniformizationRate_birth (trafficIntensity : ℝ) serviceRate servers
            (by positivity)]
  · apply congrArg ProbabilityTheory.poissonMeasure
    apply NNReal.eq
    change
      (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers *
          (duration : ℝ)) * ((1 - uniformizedBirthProbability trafficIntensity : ℝ≥0) : ℝ) =
        ((servers : ℝ) * serviceRate) * (duration : ℝ)
    calc
      (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers *
          (duration : ℝ)) * ((1 - uniformizedBirthProbability trafficIntensity : ℝ≥0) : ℝ) =
          (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers *
            ((1 - uniformizedBirthProbability trafficIntensity : ℝ≥0) : ℝ)) *
              (duration : ℝ) := by ring
      _ = ((servers : ℝ) * serviceRate) * (duration : ℝ) := by
        rw [manyServerUniformizationRate_potentialService]

/-- The finite vector of actual partition increments has the product law of
Poisson counts at the physical arrival and potential-service rates. -/
theorem manyServerMarkedCanonicalIntervalIncrementVector_physical_hasLaw
    {initial : PMF ℕ} (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers : ℕ) (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    {start : ℝ} (hstart : 0 ≤ start) (durations : List (ℝ≥0)) :
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    let physicalTailLaws := durations.map fun (duration : ℝ≥0) =>
      (ProbabilityTheory.poissonMeasure
        (PoissonProcess.rateExposureParam
          ((servers : ℝ) * (trafficIntensity : ℝ) * serviceRate) (duration : ℝ)
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg (by positivity) (by positivity))
              (le_of_lt hserviceRate)) duration.2))).prod
      (ProbabilityTheory.poissonMeasure
        (PoissonProcess.rateExposureParam ((servers : ℝ) * serviceRate) (duration : ℝ)
          (mul_nonneg (mul_nonneg (by positivity) (le_of_lt hserviceRate)) duration.2)))
    HasLaw (manyServerMarkedCanonicalIntervalIncrementVector start durations)
      (Measure.map
        (finFunctionReindex (α := ℕ × ℕ)
          (by simp only [physicalTailLaws, List.length_map]))
        (poissonCountPairFiniteProductMeasure physicalTailLaws))
      ((stationaryTrajMeasure
        (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
        (manyServerMarkedStateUniformizationMeasureKernel
          trafficIntensity servers hservers)).prod
        (PoissonProcess.exponentialInterarrivalMeasure rate)) := by
  dsimp only
  let tailMeans : List (ℝ≥0) := durations.map fun (duration : ℝ≥0) =>
    ⟨manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers *
        (duration : ℝ),
      mul_nonneg
        (le_of_lt (manyServerUniformizationRate_pos trafficIntensity serviceRate
          servers hservers hserviceRate)) duration.2⟩
  let tailLaws : List (Measure (ℕ × ℕ)) := tailMeans.map fun mean =>
    (ProbabilityTheory.poissonMeasure
      (mean * uniformizedBirthProbability trafficIntensity)).prod
    (ProbabilityTheory.poissonMeasure
      (mean * (1 - uniformizedBirthProbability trafficIntensity)))
  let physicalTailLaws : List (Measure (ℕ × ℕ)) := durations.map fun (duration : ℝ≥0) =>
    (ProbabilityTheory.poissonMeasure
      (PoissonProcess.rateExposureParam
        ((servers : ℝ) * (trafficIntensity : ℝ) * serviceRate) (duration : ℝ)
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg (by positivity) (by positivity))
            (le_of_lt hserviceRate)) duration.2))).prod
    (ProbabilityTheory.poissonMeasure
      (PoissonProcess.rateExposureParam ((servers : ℝ) * serviceRate) (duration : ℝ)
        (mul_nonneg (mul_nonneg (by positivity) (le_of_lt hserviceRate)) duration.2)))
  have htailLaws : tailLaws = physicalTailLaws := by
    simpa only [tailMeans, tailLaws, physicalTailLaws] using
      manyServerMarkedCanonical_intervalTailLaws_eq_physical
        trafficIntensity serviceRate servers hservers hserviceRate durations
  have hraw := manyServerMarkedCanonicalIntervalIncrementVector_hasLaw
    (initial := initial) trafficIntensity serviceRate servers hservers hserviceRate hstart durations
  dsimp only at hraw
  change HasLaw (manyServerMarkedCanonicalIntervalIncrementVector start durations)
    (Measure.map
      (finFunctionReindex (α := ℕ × ℕ)
        (by simp only [tailMeans, tailLaws, List.length_map]))
      (poissonCountPairFiniteProductMeasure tailLaws))
    ((stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)).prod
      (PoissonProcess.exponentialInterarrivalMeasure
        (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers))) at hraw
  have hmeasure :=
    map_finFunctionReindex_poissonCountPairFiniteProductMeasure_eq_of_eq
      (length := durations.length)
      (by simp only [tailMeans, tailLaws, List.length_map])
      (by simp only [physicalTailLaws, List.length_map]) htailLaws
  rw [hmeasure] at hraw
  exact hraw

/-- The actual marked canonical queue satisfies the finite conservation law at
every deterministic clock horizon: completed services plus current queue
length equal initial queue length plus marked arrivals. -/
theorem ae_manyServerMarkedCanonical_queue_balance
    {initial : PMF ℕ} (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers : ℕ) (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    (hstationary : PMFStationary
      (manyServerUniformizedKernel trafficIntensity servers hservers) initial)
    (time : ℝ) :
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    ∀ᵐ value ∂((stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)).prod
      (PoissonProcess.exponentialInterarrivalMeasure rate)),
      manyServerMarkedCanonicalQueueLength time value +
          manyServerMarkedCanonicalDepartureCount time value =
        (value.1 0).1 + manyServerMarkedCanonicalArrivalCount time value := by
  dsimp only
  let rate : ℝ := manyServerUniformizationRate
    (trafficIntensity : ℝ) serviceRate servers
  let trajectory : Measure (ℕ → ℕ × Bool) := stationaryTrajMeasure
    (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
    (manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers)
  let gaps : Measure (ℕ → ℝ) :=
    PoissonProcess.exponentialInterarrivalMeasure rate
  let source : Measure ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := trajectory.prod gaps
  have hrate : 0 < rate := by
    exact manyServerUniformizationRate_pos trafficIntensity serviceRate
      servers hservers hserviceRate
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsProbabilityMeasure gaps :=
    PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  change ∀ᵐ value ∂source,
    manyServerMarkedCanonicalQueueLength time value +
        manyServerMarkedCanonicalDepartureCount time value =
      (value.1 0).1 + manyServerMarkedCanonicalArrivalCount time value
  have hsteps : ∀ᵐ value ∂source,
      ∀ index : ℕ,
        ManyServerMarkedStateStepAllowed (value.1 index) (value.1 (index + 1)) := by
    refine ae_of_ae_map (μ := source) (f := Prod.fst)
      (p := fun path : ℕ → ℕ × Bool =>
        ∀ index : ℕ,
          ManyServerMarkedStateStepAllowed (path index) (path (index + 1)))
      measurable_fst.aemeasurable ?_
    rw [show Measure.map Prod.fst source = trajectory by
      dsimp [source]
      rw [Measure.map_fst_prod, measure_univ, one_smul]]
    exact ae_all_stationaryManyServerMarkedStateTrajectory_stepAllowed
      trafficIntensity servers hservers hstationary
  filter_upwards [hsteps] with value hvalue
  have hbalance := manyServerMarkedState_queue_balance_prefix value.1 hvalue
    (PoissonProcess.canonicalRenewalCount time value.2)
  rw [manyServerMarkedStateArrivalPrefix_eq_keptInMarks] at hbalance
  simpa [manyServerMarkedCanonicalQueueLength,
    manyServerMarkedCanonicalDepartureCount,
    manyServerMarkedCanonicalArrivalCount, manyServerMarkedCanonicalHorizonSample,
    FiniteHorizonMarkedPoisson.kept, Function.comp_def] using hbalance

/-- The actual marked canonical queue satisfies the same conservation law from
an arbitrary initial countable PMF.  The proof uses only the Markov trajectory
recurrence and the independent clock, not invariance of the initial law. -/
theorem ae_manyServerMarkedCanonical_queue_balance_from_initial
    {initial : PMF ℕ} (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers : ℕ) (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    (time : ℝ) :
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    ∀ᵐ value ∂((stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)).prod
      (PoissonProcess.exponentialInterarrivalMeasure rate)),
      manyServerMarkedCanonicalQueueLength time value +
          manyServerMarkedCanonicalDepartureCount time value =
        (value.1 0).1 + manyServerMarkedCanonicalArrivalCount time value := by
  dsimp only
  let rate : ℝ := manyServerUniformizationRate
    (trafficIntensity : ℝ) serviceRate servers
  let trajectory : Measure (ℕ → ℕ × Bool) := stationaryTrajMeasure
    (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
    (manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers)
  let gaps : Measure (ℕ → ℝ) :=
    PoissonProcess.exponentialInterarrivalMeasure rate
  let source : Measure ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := trajectory.prod gaps
  have hrate : 0 < rate := by
    exact manyServerUniformizationRate_pos trafficIntensity serviceRate
      servers hservers hserviceRate
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsProbabilityMeasure gaps :=
    PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  change ∀ᵐ value ∂source,
    manyServerMarkedCanonicalQueueLength time value +
        manyServerMarkedCanonicalDepartureCount time value =
      (value.1 0).1 + manyServerMarkedCanonicalArrivalCount time value
  have hsteps : ∀ᵐ value ∂source,
      ∀ index : ℕ,
        ManyServerMarkedStateStepAllowed (value.1 index) (value.1 (index + 1)) := by
    refine ae_of_ae_map (μ := source) (f := Prod.fst)
      (p := fun path : ℕ → ℕ × Bool =>
        ∀ index : ℕ,
          ManyServerMarkedStateStepAllowed (path index) (path (index + 1)))
      measurable_fst.aemeasurable ?_
    rw [show Measure.map Prod.fst source = trajectory by
      dsimp [source]
      rw [Measure.map_fst_prod, measure_univ, one_smul]]
    exact ae_all_manyServerMarkedStateTrajectory_stepAllowed_from_initial
      initial trafficIntensity servers hservers
  filter_upwards [hsteps] with value hvalue
  have hbalance := manyServerMarkedState_queue_balance_prefix value.1 hvalue
    (PoissonProcess.canonicalRenewalCount time value.2)
  rw [manyServerMarkedStateArrivalPrefix_eq_keptInMarks] at hbalance
  simpa [manyServerMarkedCanonicalQueueLength,
    manyServerMarkedCanonicalDepartureCount,
    manyServerMarkedCanonicalArrivalCount, manyServerMarkedCanonicalHorizonSample,
    FiniteHorizonMarkedPoisson.kept, Function.comp_def] using hbalance

/-- The canonical marked queue-conservation identity holds simultaneously at
every real time on one common full-measure event.  This strengthens the
fixed-time version into the pathwise form needed by functional arguments. -/
theorem ae_forall_manyServerMarkedCanonical_queue_balance_from_initial
    {initial : PMF ℕ} (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers : ℕ) (hservers : 0 < servers) (hserviceRate : 0 < serviceRate) :
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    ∀ᵐ value ∂((stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)).prod
      (PoissonProcess.exponentialInterarrivalMeasure rate)),
      ∀ time : ℝ,
        manyServerMarkedCanonicalQueueLength time value +
            manyServerMarkedCanonicalDepartureCount time value =
          (value.1 0).1 + manyServerMarkedCanonicalArrivalCount time value := by
  dsimp only
  let rate : ℝ := manyServerUniformizationRate
    (trafficIntensity : ℝ) serviceRate servers
  let trajectory : Measure (ℕ → ℕ × Bool) := stationaryTrajMeasure
    (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
    (manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers)
  let gaps : Measure (ℕ → ℝ) :=
    PoissonProcess.exponentialInterarrivalMeasure rate
  let source : Measure ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := trajectory.prod gaps
  have hrate : 0 < rate := by
    exact manyServerUniformizationRate_pos trafficIntensity serviceRate
      servers hservers hserviceRate
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsProbabilityMeasure gaps :=
    PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  change ∀ᵐ value ∂source, ∀ time : ℝ,
    manyServerMarkedCanonicalQueueLength time value +
        manyServerMarkedCanonicalDepartureCount time value =
      (value.1 0).1 + manyServerMarkedCanonicalArrivalCount time value
  have hsteps : ∀ᵐ value ∂source,
      ∀ index : ℕ,
        ManyServerMarkedStateStepAllowed (value.1 index) (value.1 (index + 1)) := by
    refine ae_of_ae_map (μ := source) (f := Prod.fst)
      (p := fun path : ℕ → ℕ × Bool =>
        ∀ index : ℕ,
          ManyServerMarkedStateStepAllowed (path index) (path (index + 1)))
      measurable_fst.aemeasurable ?_
    rw [show Measure.map Prod.fst source = trajectory by
      dsimp [source]
      rw [Measure.map_fst_prod, measure_univ, one_smul]]
    exact ae_all_manyServerMarkedStateTrajectory_stepAllowed_from_initial
      initial trafficIntensity servers hservers
  filter_upwards [hsteps] with value hvalue
  intro time
  have hbalance := manyServerMarkedState_queue_balance_prefix value.1 hvalue
    (PoissonProcess.canonicalRenewalCount time value.2)
  rw [manyServerMarkedStateArrivalPrefix_eq_keptInMarks] at hbalance
  simpa [manyServerMarkedCanonicalQueueLength,
    manyServerMarkedCanonicalDepartureCount,
    manyServerMarkedCanonicalArrivalCount, manyServerMarkedCanonicalHorizonSample,
    FiniteHorizonMarkedPoisson.kept, Function.comp_def] using hbalance

/-- On the actual canonical marked path, completed services are at most the
number of potential-service events, for every deterministic time and every
initial countable PMF. -/
theorem ae_manyServerMarkedCanonical_departureCount_le_potentialServiceCount_from_initial
    {initial : PMF ℕ} (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers : ℕ) (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    (time : ℝ) :
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    ∀ᵐ value ∂((stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)).prod
      (PoissonProcess.exponentialInterarrivalMeasure rate)),
      manyServerMarkedCanonicalDepartureCount time value ≤
        manyServerMarkedCanonicalPotentialServiceCount time value := by
  dsimp only
  let rate : ℝ := manyServerUniformizationRate
    (trafficIntensity : ℝ) serviceRate servers
  let trajectory : Measure (ℕ → ℕ × Bool) := stationaryTrajMeasure
    (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
    (manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers)
  let gaps : Measure (ℕ → ℝ) :=
    PoissonProcess.exponentialInterarrivalMeasure rate
  let source : Measure ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := trajectory.prod gaps
  have hrate : 0 < rate := by
    exact manyServerUniformizationRate_pos trafficIntensity serviceRate
      servers hservers hserviceRate
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsProbabilityMeasure gaps :=
    PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  change ∀ᵐ value ∂source,
    manyServerMarkedCanonicalDepartureCount time value ≤
      manyServerMarkedCanonicalPotentialServiceCount time value
  have hsteps : ∀ᵐ value ∂source,
      ∀ index : ℕ,
        ManyServerMarkedStateStepAllowed (value.1 index) (value.1 (index + 1)) := by
    refine ae_of_ae_map (μ := source) (f := Prod.fst)
      (p := fun path : ℕ → ℕ × Bool =>
        ∀ index : ℕ,
          ManyServerMarkedStateStepAllowed (path index) (path (index + 1)))
      measurable_fst.aemeasurable ?_
    rw [show Measure.map Prod.fst source = trajectory by
      dsimp [source]
      rw [Measure.map_fst_prod, measure_univ, one_smul]]
    exact ae_all_manyServerMarkedStateTrajectory_stepAllowed_from_initial
      initial trafficIntensity servers hservers
  filter_upwards [hsteps] with value hvalue
  let steps := PoissonProcess.canonicalRenewalCount time value.2
  change manyServerMarkedStateDeparturePrefix value.1 steps ≤
    FiniteHorizonMarkedPoisson.discardedInMarks
      (fun index : Fin steps => (value.1 index).2)
  exact manyServerMarkedStateDeparturePrefix_le_discardedInMarks
    value.1 hvalue steps

/-- The completed-service count is at most the potential-service count at
every real time on one common full-measure marked canonical trajectory event. -/
theorem ae_forall_manyServerMarkedCanonical_departureCount_le_potentialServiceCount_from_initial
    {initial : PMF ℕ} (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers : ℕ) (hservers : 0 < servers) (hserviceRate : 0 < serviceRate) :
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    ∀ᵐ value ∂((stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)).prod
      (PoissonProcess.exponentialInterarrivalMeasure rate)),
      ∀ time : ℝ,
        manyServerMarkedCanonicalDepartureCount time value ≤
          manyServerMarkedCanonicalPotentialServiceCount time value := by
  dsimp only
  let rate : ℝ := manyServerUniformizationRate
    (trafficIntensity : ℝ) serviceRate servers
  let trajectory : Measure (ℕ → ℕ × Bool) := stationaryTrajMeasure
    (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
    (manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers)
  let gaps : Measure (ℕ → ℝ) :=
    PoissonProcess.exponentialInterarrivalMeasure rate
  let source : Measure ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := trajectory.prod gaps
  have hrate : 0 < rate := by
    exact manyServerUniformizationRate_pos trafficIntensity serviceRate
      servers hservers hserviceRate
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsProbabilityMeasure gaps :=
    PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  change ∀ᵐ value ∂source, ∀ time : ℝ,
    manyServerMarkedCanonicalDepartureCount time value ≤
      manyServerMarkedCanonicalPotentialServiceCount time value
  have hsteps : ∀ᵐ value ∂source,
      ∀ index : ℕ,
        ManyServerMarkedStateStepAllowed (value.1 index) (value.1 (index + 1)) := by
    refine ae_of_ae_map (μ := source) (f := Prod.fst)
      (p := fun path : ℕ → ℕ × Bool =>
        ∀ index : ℕ,
          ManyServerMarkedStateStepAllowed (path index) (path (index + 1)))
      measurable_fst.aemeasurable ?_
    rw [show Measure.map Prod.fst source = trajectory by
      dsimp [source]
      rw [Measure.map_fst_prod, measure_univ, one_smul]]
    exact ae_all_manyServerMarkedStateTrajectory_stepAllowed_from_initial
      initial trafficIntensity servers hservers
  filter_upwards [hsteps] with value hvalue
  intro time
  let steps := PoissonProcess.canonicalRenewalCount time value.2
  change manyServerMarkedStateDeparturePrefix value.1 steps ≤
    FiniteHorizonMarkedPoisson.discardedInMarks
      (fun index : Fin steps => (value.1 index).2)
  exact manyServerMarkedStateDeparturePrefix_le_discardedInMarks
    value.1 hvalue steps

/-- On the common full-measure canonical marked-path event, the queue length
is bounded below by its initial value plus arrivals minus potential-service
events.  This deliberately uses potential service rather than completed
service, so it holds for every initial queue law and at every physical time. -/
theorem ae_forall_manyServerMarkedCanonical_queueLength_ge_initial_add_arrival_sub_potential_from_initial
    {initial : PMF ℕ} (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers : ℕ) (hservers : 0 < servers) (hserviceRate : 0 < serviceRate) :
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    ∀ᵐ value ∂((stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)).prod
      (PoissonProcess.exponentialInterarrivalMeasure rate)),
      ∀ time : ℝ,
        (value.1 0).1 + manyServerMarkedCanonicalArrivalCount time value -
            manyServerMarkedCanonicalPotentialServiceCount time value ≤
          manyServerMarkedCanonicalQueueLength time value := by
  have hbalance := ae_forall_manyServerMarkedCanonical_queue_balance_from_initial
    (initial := initial) trafficIntensity serviceRate servers hservers hserviceRate
  have hservice :=
    ae_forall_manyServerMarkedCanonical_departureCount_le_potentialServiceCount_from_initial
      (initial := initial) trafficIntensity serviceRate servers hservers hserviceRate
  filter_upwards [hbalance, hservice] with value hbalanceValue hserviceValue
  intro time
  have hbalanceTime := hbalanceValue time
  have hserviceTime := hserviceValue time
  omega

/-- On the common full-measure canonical marked-path event, the queue length
is bounded above by its initial value plus the cumulative arrival count.  This
uses only nonnegativity of completed departures and is valid for every
initial queue law. -/
theorem ae_forall_manyServerMarkedCanonical_queueLength_le_initial_add_arrival_from_initial
    {initial : PMF ℕ} (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers : ℕ) (hservers : 0 < servers) (hserviceRate : 0 < serviceRate) :
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    ∀ᵐ value ∂((stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)).prod
      (PoissonProcess.exponentialInterarrivalMeasure rate)),
      ∀ time : ℝ,
        manyServerMarkedCanonicalQueueLength time value ≤
          (value.1 0).1 + manyServerMarkedCanonicalArrivalCount time value := by
  have hbalance := ae_forall_manyServerMarkedCanonical_queue_balance_from_initial
    (initial := initial) trafficIntensity serviceRate servers hservers hserviceRate
  filter_upwards [hbalance] with value hbalanceValue
  intro time
  have hbalanceTime := hbalanceValue time
  omega

/-- On each compact left-bounded time interval, the canonical queue is bounded
above by its initial state plus the arrival count at the interval's right
endpoint.  This is the pathwise upper compact-containment reduction: all
randomness on the interval is reduced to one initial coordinate and one
Poisson-marginal count. -/
theorem ae_forall_manyServerMarkedCanonical_queueLength_le_initial_add_arrival_at_horizon_from_initial
    {initial : PMF ℕ} (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers : ℕ) (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    (horizon : ℝ) :
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    ∀ᵐ value ∂((stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)).prod
      (PoissonProcess.exponentialInterarrivalMeasure rate)),
      ∀ time : ℝ, time ≤ horizon →
        manyServerMarkedCanonicalQueueLength time value ≤
          (value.1 0).1 + manyServerMarkedCanonicalArrivalCount horizon value := by
  dsimp only
  have hqueue :=
    ae_forall_manyServerMarkedCanonical_queueLength_le_initial_add_arrival_from_initial
      (initial := initial) trafficIntensity serviceRate servers hservers hserviceRate
  have harrivals :=
    ae_forall_monotone_manyServerMarkedCanonicalArrivalCount_from_initial
      (initial := initial) trafficIntensity serviceRate servers hservers hserviceRate
  filter_upwards [hqueue, harrivals] with value hqueueValue harrivalsValue
  intro time htime
  exact (hqueueValue time).trans
    (Nat.add_le_add_left (harrivalsValue htime) _)

/-- The idle fraction along the canonical queue path is bounded by the idle
fraction at the pathwise arrival-minus-potential-service lower bound.  This
is the monotone localization step used to control unused-service noise from
initial tightness and primitive-clock bounds, without assuming stationarity. -/
theorem ae_forall_one_sub_manyServerMarkedCanonical_busyFraction_le_initial_add_arrival_sub_potential_from_initial
    {initial : PMF ℕ} (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers : ℕ) (hservers : 0 < servers) (hserviceRate : 0 < serviceRate) :
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    ∀ᵐ value ∂((stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)).prod
      (PoissonProcess.exponentialInterarrivalMeasure rate)),
      ∀ time : ℝ,
        1 - (manyServerBusyFraction servers
          (manyServerMarkedCanonicalQueueLength time value) : ℝ) ≤
        1 - (manyServerBusyFraction servers
          ((value.1 0).1 + manyServerMarkedCanonicalArrivalCount time value -
            manyServerMarkedCanonicalPotentialServiceCount time value) : ℝ) := by
  have hlower :=
    ae_forall_manyServerMarkedCanonical_queueLength_ge_initial_add_arrival_sub_potential_from_initial
      (initial := initial) trafficIntensity serviceRate servers hservers hserviceRate
  filter_upwards [hlower] with value hlowerValue
  intro time
  exact antitone_one_sub_manyServerBusyFraction servers (hlowerValue time)

/-- The potential-service count decomposes into completed services and the
unrealized potential-service count on the canonical path. -/
theorem ae_manyServerMarkedCanonical_potentialServiceCount_eq_departure_add_unrealized_from_initial
    {initial : PMF ℕ} (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers : ℕ) (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    (time : ℝ) :
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    ∀ᵐ value ∂((stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)).prod
      (PoissonProcess.exponentialInterarrivalMeasure rate)),
      manyServerMarkedCanonicalDepartureCount time value +
          manyServerMarkedCanonicalUnrealizedPotentialServiceCount time value =
        manyServerMarkedCanonicalPotentialServiceCount time value := by
  dsimp only
  have hle := ae_manyServerMarkedCanonical_departureCount_le_potentialServiceCount_from_initial
    (initial := initial) trafficIntensity serviceRate servers hservers hserviceRate time
  filter_upwards [hle] with value hvalue
  exact Nat.add_sub_of_le hvalue

/-- The canonical marked uniformization has independent finite-horizon arrival
and potential-service counts before identifying their physical rates. -/
theorem stationaryManyServerMarkedCanonicalArrivalPotentialCounts_hasLaw
    {initial : PMF ℕ} (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers : ℕ) (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    {time : ℝ} (htime : 0 ≤ time) :
    let rate := manyServerUniformizationRate
      (trafficIntensity : ℝ) serviceRate servers
    let mean : ℝ≥0 := ⟨rate * time, mul_nonneg
      (le_of_lt (manyServerUniformizationRate_pos trafficIntensity serviceRate
        servers hservers hserviceRate)) htime⟩
    let arrivalProbability := uniformizedBirthProbability trafficIntensity
    HasLaw (manyServerMarkedCanonicalArrivalPotentialCounts time)
      ((ProbabilityTheory.poissonMeasure (mean * arrivalProbability)).prod
        (ProbabilityTheory.poissonMeasure
          (mean * (1 - arrivalProbability))))
      ((stationaryTrajMeasure
        (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
        (manyServerMarkedStateUniformizationMeasureKernel
          trafficIntensity servers hservers)).prod
        (PoissonProcess.exponentialInterarrivalMeasure rate)) := by
  dsimp only
  let rate : ℝ := manyServerUniformizationRate
    (trafficIntensity : ℝ) serviceRate servers
  let mean : ℝ≥0 := ⟨rate * time, mul_nonneg
    (le_of_lt (manyServerUniformizationRate_pos trafficIntensity serviceRate
      servers hservers hserviceRate)) htime⟩
  let arrivalProbability : ℝ≥0 := uniformizedBirthProbability trafficIntensity
  let arrivalProbability_le_one : arrivalProbability ≤ 1 :=
    uniformizedBirthProbability_le_one trafficIntensity
  let trajectory : Measure (ℕ → ℕ × Bool) := stationaryTrajMeasure
    (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
    (manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers)
  let gaps : Measure (ℕ → ℝ) :=
    PoissonProcess.exponentialInterarrivalMeasure rate
  let source : Measure ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := trajectory.prod gaps
  have hsample : HasLaw (manyServerMarkedCanonicalHorizonSample time)
      (FiniteHorizonMarkedPoisson.jointPMF mean arrivalProbability
        arrivalProbability_le_one).toMeasure source := by
    simpa [source, trajectory, gaps, rate, mean, arrivalProbability,
      arrivalProbability_le_one] using
      (stationaryManyServerMarkedCanonicalHorizonSample_hasLaw
        (initial := initial) trafficIntensity serviceRate servers hservers hserviceRate htime)
  simpa [manyServerMarkedCanonicalArrivalPotentialCounts, Function.comp_def]
    using (FiniteHorizonMarkedPoisson.splitCounts_hasLaw mean arrivalProbability
      arrivalProbability_le_one).comp hsample

/-- The arrival mean obtained by thinning the canonical potential-event clock
is the physical many-server arrival rate times the horizon. -/
theorem manyServerMarkedCanonical_arrivalMean_eq_rateExposure
    (trafficIntensity : ℝ≥0) (serviceRate : ℝ) (servers : ℕ)
    (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    {time : ℝ} (htime : 0 ≤ time) :
    PoissonProcess.rateExposureParam
      (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers) time
      (mul_nonneg
        (le_of_lt (manyServerUniformizationRate_pos trafficIntensity serviceRate
          servers hservers hserviceRate)) htime) *
      uniformizedBirthProbability trafficIntensity =
    PoissonProcess.rateExposureParam
      ((servers : ℝ) * (trafficIntensity : ℝ) * serviceRate) time
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by positivity) (by positivity))
          (le_of_lt hserviceRate)) htime) := by
  apply NNReal.eq
  change
    (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers * time) *
        (uniformizedBirthProbability trafficIntensity : ℝ) =
      ((servers : ℝ) * (trafficIntensity : ℝ) * serviceRate) * time
  calc
    (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers * time) *
        (uniformizedBirthProbability trafficIntensity : ℝ) =
        (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers *
          (uniformizedBirthProbability trafficIntensity : ℝ)) * time := by ring
    _ = ((servers : ℝ) * (trafficIntensity : ℝ) * serviceRate) * time := by
      rw [show (uniformizedBirthProbability trafficIntensity : ℝ) =
        (trafficIntensity : ℝ) / (1 + (trafficIntensity : ℝ)) by
          simp [uniformizedBirthProbability],
        manyServerUniformizationRate_birth (trafficIntensity : ℝ) serviceRate servers
          (by positivity)]

/-- The complementary thinned mean is the aggregate potential-service-clock
rate times the horizon. -/
theorem manyServerMarkedCanonical_potentialServiceMean_eq_rateExposure
    (trafficIntensity : ℝ≥0) (serviceRate : ℝ) (servers : ℕ)
    (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    {time : ℝ} (htime : 0 ≤ time) :
    PoissonProcess.rateExposureParam
      (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers) time
      (mul_nonneg
        (le_of_lt (manyServerUniformizationRate_pos trafficIntensity serviceRate
          servers hservers hserviceRate)) htime) *
      ((1 : ℝ≥0) - uniformizedBirthProbability trafficIntensity) =
    PoissonProcess.rateExposureParam ((servers : ℝ) * serviceRate) time
      (mul_nonneg (mul_nonneg (by positivity) (le_of_lt hserviceRate)) htime) := by
  apply NNReal.eq
  change
    (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers * time) *
        ((1 - uniformizedBirthProbability trafficIntensity : ℝ≥0) : ℝ) =
      ((servers : ℝ) * serviceRate) * time
  calc
    (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers * time) *
        ((1 - uniformizedBirthProbability trafficIntensity : ℝ≥0) : ℝ) =
        (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers *
          ((1 - uniformizedBirthProbability trafficIntensity : ℝ≥0) : ℝ)) * time := by
            ring
    _ = ((servers : ℝ) * serviceRate) * time := by
      rw [manyServerUniformizationRate_potentialService]

/-- At each deterministic horizon, the canonical marked many-server driver
has independent Poisson arrival and potential-service counts at their physical
rates. -/
theorem stationaryManyServerMarkedCanonicalArrivalPotentialCounts_physical_hasLaw
    {initial : PMF ℕ} (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers : ℕ) (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    {time : ℝ} (htime : 0 ≤ time) :
    HasLaw (manyServerMarkedCanonicalArrivalPotentialCounts time)
      ((ProbabilityTheory.poissonMeasure
        (PoissonProcess.rateExposureParam
          ((servers : ℝ) * (trafficIntensity : ℝ) * serviceRate) time
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg (by positivity) (by positivity))
              (le_of_lt hserviceRate)) htime))).prod
        (ProbabilityTheory.poissonMeasure
          (PoissonProcess.rateExposureParam ((servers : ℝ) * serviceRate) time
            (mul_nonneg (mul_nonneg (by positivity) (le_of_lt hserviceRate))
              htime))))
      ((stationaryTrajMeasure
        (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
        (manyServerMarkedStateUniformizationMeasureKernel
          trafficIntensity servers hservers)).prod
        (PoissonProcess.exponentialInterarrivalMeasure
          (manyServerUniformizationRate
            (trafficIntensity : ℝ) serviceRate servers))) := by
  have hcounts :=
    stationaryManyServerMarkedCanonicalArrivalPotentialCounts_hasLaw
      (initial := initial) trafficIntensity serviceRate servers hservers hserviceRate htime
  dsimp only at hcounts
  have harrivalMean := manyServerMarkedCanonical_arrivalMean_eq_rateExposure
    trafficIntensity serviceRate servers hservers hserviceRate htime
  have hpotentialServiceMean :=
    manyServerMarkedCanonical_potentialServiceMean_eq_rateExposure
      trafficIntensity serviceRate servers hservers hserviceRate htime
  simp only [PoissonProcess.rateExposureParam] at harrivalMean hpotentialServiceMean
  rw [harrivalMean, hpotentialServiceMean] at hcounts
  exact hcounts

/-- Over every deterministic physical interval, the actual canonical arrival
and potential-service count increments have the product Poisson law at their
physical rates. -/
theorem stationaryManyServerMarkedCanonicalIntervalArrivalPotentialIncrements_physical_hasLaw
    {initial : PMF ℕ} (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers : ℕ) (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    {start duration : ℝ} (hstart : 0 ≤ start) (hduration : 0 ≤ duration) :
    HasLaw
      (fun value =>
        (manyServerMarkedCanonicalArrivalCount (start + duration) value -
            manyServerMarkedCanonicalArrivalCount start value,
          manyServerMarkedCanonicalPotentialServiceCount (start + duration) value -
            manyServerMarkedCanonicalPotentialServiceCount start value))
      ((ProbabilityTheory.poissonMeasure
        (PoissonProcess.rateExposureParam
          ((servers : ℝ) * (trafficIntensity : ℝ) * serviceRate) duration
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg (by positivity) (by positivity))
              (le_of_lt hserviceRate)) hduration))).prod
        (ProbabilityTheory.poissonMeasure
          (PoissonProcess.rateExposureParam ((servers : ℝ) * serviceRate) duration
            (mul_nonneg (mul_nonneg (by positivity) (le_of_lt hserviceRate))
              hduration))))
      ((stationaryTrajMeasure
        (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
        (manyServerMarkedStateUniformizationMeasureKernel
          trafficIntensity servers hservers)).prod
        (PoissonProcess.exponentialInterarrivalMeasure
          (manyServerUniformizationRate
            (trafficIntensity : ℝ) serviceRate servers))) := by
  let rate : ℝ := manyServerUniformizationRate
    (trafficIntensity : ℝ) serviceRate servers
  let mean : ℝ≥0 := ⟨rate * duration, mul_nonneg
    (le_of_lt (manyServerUniformizationRate_pos trafficIntensity serviceRate
      servers hservers hserviceRate)) hduration⟩
  let arrivalProbability : ℝ≥0 := uniformizedBirthProbability trafficIntensity
  let arrivalProbability_le_one : arrivalProbability ≤ 1 :=
    uniformizedBirthProbability_le_one trafficIntensity
  let trajectory : Measure (ℕ → ℕ × Bool) := stationaryTrajMeasure
    (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
    (manyServerMarkedStateUniformizationMeasureKernel
      trafficIntensity servers hservers)
  let gaps : Measure (ℕ → ℝ) :=
    PoissonProcess.exponentialInterarrivalMeasure rate
  let source : Measure ((ℕ → ℕ × Bool) × (ℕ → ℝ)) := trajectory.prod gaps
  have hsample : HasLaw (manyServerMarkedCanonicalIntervalSample start duration)
      (FiniteHorizonMarkedPoisson.jointPMF mean arrivalProbability
        arrivalProbability_le_one).toMeasure source := by
    simpa [source, trajectory, gaps, rate, mean, arrivalProbability,
      arrivalProbability_le_one] using
      (manyServerMarkedCanonicalIntervalSample_hasLaw
        (initial := initial) trafficIntensity serviceRate servers hservers hserviceRate
        hstart hduration)
  have hsplit : HasLaw
      (FiniteHorizonMarkedPoisson.splitCounts ∘
        manyServerMarkedCanonicalIntervalSample start duration)
      ((ProbabilityTheory.poissonMeasure (mean * arrivalProbability)).prod
        (ProbabilityTheory.poissonMeasure
          (mean * (1 - arrivalProbability)))) source := by
    exact (FiniteHorizonMarkedPoisson.splitCounts_hasLaw mean arrivalProbability
      arrivalProbability_le_one).comp hsample
  have hincrements :
      (fun value =>
        (manyServerMarkedCanonicalArrivalCount (start + duration) value -
            manyServerMarkedCanonicalArrivalCount start value,
          manyServerMarkedCanonicalPotentialServiceCount (start + duration) value -
            manyServerMarkedCanonicalPotentialServiceCount start value)) =ᵐ[source]
        FiniteHorizonMarkedPoisson.splitCounts ∘
          manyServerMarkedCanonicalIntervalSample start duration := by
    filter_upwards [ae_manyServerMarkedCanonicalIntervalSample_splitCounts_eq_increments
      (initial := initial) trafficIntensity serviceRate servers hservers hserviceRate
      (start := start) (duration := duration) hduration] with value hvalue
    exact hvalue.symm
  have hresult := hsplit.congr hincrements
  have harrivalMean := manyServerMarkedCanonical_arrivalMean_eq_rateExposure
    trafficIntensity serviceRate servers hservers hserviceRate hduration
  have hpotentialServiceMean :=
    manyServerMarkedCanonical_potentialServiceMean_eq_rateExposure
      trafficIntensity serviceRate servers hservers hserviceRate hduration
  simp only [PoissonProcess.rateExposureParam] at harrivalMean hpotentialServiceMean
  rw [harrivalMean, hpotentialServiceMean] at hresult
  simpa [source, trajectory, gaps, rate, mean, arrivalProbability,
    arrivalProbability_le_one] using hresult

/-- The physical arrival and potential-service counts in the horizon through
`start` and in the following interval are independent Poisson pairs at their
respective physical rates. -/
theorem stationaryManyServerMarkedCanonicalHorizon_intervalArrivalPotential_physical_hasLaw
    {initial : PMF ℕ} (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers : ℕ) (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    {start duration : ℝ} (hstart : 0 ≤ start) (hduration : 0 ≤ duration) :
    HasLaw (fun value : ((ℕ → ℕ × Bool) × (ℕ → ℝ)) =>
      (manyServerMarkedCanonicalArrivalPotentialCounts start value,
        (manyServerMarkedCanonicalArrivalCount (start + duration) value -
            manyServerMarkedCanonicalArrivalCount start value,
          manyServerMarkedCanonicalPotentialServiceCount (start + duration) value -
            manyServerMarkedCanonicalPotentialServiceCount start value)))
      (Measure.prod
        ((ProbabilityTheory.poissonMeasure
          (PoissonProcess.rateExposureParam
            ((servers : ℝ) * (trafficIntensity : ℝ) * serviceRate) start
            (mul_nonneg
              (mul_nonneg
                (mul_nonneg (by positivity) (by positivity))
                (le_of_lt hserviceRate)) hstart))).prod
          (ProbabilityTheory.poissonMeasure
            (PoissonProcess.rateExposureParam ((servers : ℝ) * serviceRate) start
              (mul_nonneg (mul_nonneg (by positivity) (le_of_lt hserviceRate))
                hstart))))
        ((ProbabilityTheory.poissonMeasure
          (PoissonProcess.rateExposureParam
            ((servers : ℝ) * (trafficIntensity : ℝ) * serviceRate) duration
            (mul_nonneg
              (mul_nonneg
                (mul_nonneg (by positivity) (by positivity))
                (le_of_lt hserviceRate)) hduration))).prod
          (ProbabilityTheory.poissonMeasure
            (PoissonProcess.rateExposureParam ((servers : ℝ) * serviceRate) duration
              (mul_nonneg (mul_nonneg (by positivity) (le_of_lt hserviceRate))
                hduration)))))
      ((stationaryTrajMeasure
        (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
        (manyServerMarkedStateUniformizationMeasureKernel
          trafficIntensity servers hservers)).prod
        (PoissonProcess.exponentialInterarrivalMeasure
          (manyServerUniformizationRate
            (trafficIntensity : ℝ) serviceRate servers))) := by
  let rate : ℝ := manyServerUniformizationRate
    (trafficIntensity : ℝ) serviceRate servers
  let firstMean : ℝ≥0 := ⟨rate * start, mul_nonneg
    (le_of_lt (manyServerUniformizationRate_pos trafficIntensity serviceRate
      servers hservers hserviceRate)) hstart⟩
  let secondMean : ℝ≥0 := ⟨rate * duration, mul_nonneg
    (le_of_lt (manyServerUniformizationRate_pos trafficIntensity serviceRate
      servers hservers hserviceRate)) hduration⟩
  let arrivalProbability : ℝ≥0 := uniformizedBirthProbability trafficIntensity
  let source : Measure ((ℕ → ℕ × Bool) × (ℕ → ℝ)) :=
    (stationaryTrajMeasure
      (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
      (manyServerMarkedStateUniformizationMeasureKernel
        trafficIntensity servers hservers)).prod
      (PoissonProcess.exponentialInterarrivalMeasure rate)
  have hsplit := manyServerMarkedCanonicalHorizon_intervalSplitCounts_hasLaw
    (initial := initial) trafficIntensity serviceRate servers hservers hserviceRate
    hstart hduration
  dsimp only at hsplit
  have hactual :
      (fun value : ((ℕ → ℕ × Bool) × (ℕ → ℝ)) =>
        (manyServerMarkedCanonicalArrivalPotentialCounts start value,
          (manyServerMarkedCanonicalArrivalCount (start + duration) value -
              manyServerMarkedCanonicalArrivalCount start value,
            manyServerMarkedCanonicalPotentialServiceCount (start + duration) value -
              manyServerMarkedCanonicalPotentialServiceCount start value))) =ᵐ[source]
        (fun value =>
          (FiniteHorizonMarkedPoisson.splitCounts
            (manyServerMarkedCanonicalHorizonSample start value),
            FiniteHorizonMarkedPoisson.splitCounts
              (manyServerMarkedCanonicalIntervalSample start duration value))) := by
    filter_upwards [ae_manyServerMarkedCanonicalIntervalSample_splitCounts_eq_increments
      (initial := initial) trafficIntensity serviceRate servers hservers hserviceRate
      (start := start) (duration := duration) hduration] with value hvalue
    exact Prod.ext rfl hvalue.symm
  have hresult := hsplit.congr hactual
  have harrivalFirst := manyServerMarkedCanonical_arrivalMean_eq_rateExposure
    trafficIntensity serviceRate servers hservers hserviceRate hstart
  have hpotentialFirst := manyServerMarkedCanonical_potentialServiceMean_eq_rateExposure
    trafficIntensity serviceRate servers hservers hserviceRate hstart
  have harrivalSecond := manyServerMarkedCanonical_arrivalMean_eq_rateExposure
    trafficIntensity serviceRate servers hservers hserviceRate hduration
  have hpotentialSecond := manyServerMarkedCanonical_potentialServiceMean_eq_rateExposure
    trafficIntensity serviceRate servers hservers hserviceRate hduration
  simp only [PoissonProcess.rateExposureParam] at harrivalFirst hpotentialFirst
  simp only [PoissonProcess.rateExposureParam] at harrivalSecond hpotentialSecond
  rw [harrivalFirst, hpotentialFirst, harrivalSecond, hpotentialSecond] at hresult
  simpa [source, rate, firstMean, secondMean, arrivalProbability,
    PoissonProcess.rateExposureParam] using hresult

/-- At a deterministic physical horizon, the arrival count of the canonical
marked many-server driver has its physical-rate Poisson law. -/
theorem stationaryManyServerMarkedCanonicalArrivalCount_physical_hasLaw
    {initial : PMF ℕ} (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers : ℕ) (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    {time : ℝ} (htime : 0 ≤ time) :
    HasLaw (manyServerMarkedCanonicalArrivalCount time)
      (ProbabilityTheory.poissonMeasure
        (PoissonProcess.rateExposureParam
          ((servers : ℝ) * (trafficIntensity : ℝ) * serviceRate) time
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg (by positivity) (by positivity))
              (le_of_lt hserviceRate)) htime)))
      ((stationaryTrajMeasure
        (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
        (manyServerMarkedStateUniformizationMeasureKernel
          trafficIntensity servers hservers)).prod
        (PoissonProcess.exponentialInterarrivalMeasure
          (manyServerUniformizationRate
            (trafficIntensity : ℝ) serviceRate servers))) := by
  have hpairs := stationaryManyServerMarkedCanonicalArrivalPotentialCounts_physical_hasLaw
    (initial := initial) trafficIntensity serviceRate servers hservers hserviceRate htime
  let arrivalMean : ℝ≥0 :=
    PoissonProcess.rateExposureParam
      ((servers : ℝ) * (trafficIntensity : ℝ) * serviceRate) time
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by positivity) (by positivity))
          (le_of_lt hserviceRate)) htime)
  let potentialServiceMean : ℝ≥0 :=
    PoissonProcess.rateExposureParam ((servers : ℝ) * serviceRate) time
      (mul_nonneg (mul_nonneg (by positivity) (le_of_lt hserviceRate)) htime)
  have hfst : HasLaw Prod.fst (ProbabilityTheory.poissonMeasure arrivalMean)
      ((ProbabilityTheory.poissonMeasure arrivalMean).prod
        (ProbabilityTheory.poissonMeasure potentialServiceMean)) := by
    refine ⟨measurable_fst.aemeasurable, ?_⟩
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  have hresult := hfst.comp hpairs
  simpa [manyServerMarkedCanonicalArrivalPotentialCounts,
    manyServerMarkedCanonicalArrivalCount, Function.comp_def,
    arrivalMean, potentialServiceMean] using hresult

/-- At a deterministic physical horizon, the potential-service count of the
canonical marked many-server driver has its physical-rate Poisson law. -/
theorem stationaryManyServerMarkedCanonicalPotentialServiceCount_physical_hasLaw
    {initial : PMF ℕ} (trafficIntensity : ℝ≥0) (serviceRate : ℝ)
    (servers : ℕ) (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    {time : ℝ} (htime : 0 ≤ time) :
    HasLaw (manyServerMarkedCanonicalPotentialServiceCount time)
      (ProbabilityTheory.poissonMeasure
        (PoissonProcess.rateExposureParam ((servers : ℝ) * serviceRate) time
          (mul_nonneg (mul_nonneg (by positivity) (le_of_lt hserviceRate)) htime)))
      ((stationaryTrajMeasure
        (manyServerMarkedStatePMF initial trafficIntensity).toMeasure
        (manyServerMarkedStateUniformizationMeasureKernel
          trafficIntensity servers hservers)).prod
        (PoissonProcess.exponentialInterarrivalMeasure
          (manyServerUniformizationRate
            (trafficIntensity : ℝ) serviceRate servers))) := by
  have hpairs := stationaryManyServerMarkedCanonicalArrivalPotentialCounts_physical_hasLaw
    (initial := initial) trafficIntensity serviceRate servers hservers hserviceRate htime
  let arrivalMean : ℝ≥0 :=
    PoissonProcess.rateExposureParam
      ((servers : ℝ) * (trafficIntensity : ℝ) * serviceRate) time
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by positivity) (by positivity))
          (le_of_lt hserviceRate)) htime)
  let potentialServiceMean : ℝ≥0 :=
    PoissonProcess.rateExposureParam ((servers : ℝ) * serviceRate) time
      (mul_nonneg (mul_nonneg (by positivity) (le_of_lt hserviceRate)) htime)
  have hsnd : HasLaw Prod.snd (ProbabilityTheory.poissonMeasure potentialServiceMean)
      ((ProbabilityTheory.poissonMeasure arrivalMean).prod
        (ProbabilityTheory.poissonMeasure potentialServiceMean)) := by
    refine ⟨measurable_snd.aemeasurable, ?_⟩
    rw [Measure.map_snd_prod, measure_univ, one_smul]
  have hresult := hsnd.comp hpairs
  simpa [manyServerMarkedCanonicalArrivalPotentialCounts,
    manyServerMarkedCanonicalPotentialServiceCount, Function.comp_def,
    arrivalMean, potentialServiceMean] using hresult

end

end AppliedModelingLib.Probability.Queueing
