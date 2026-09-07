import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalBoundedStoppingBlock

/-!
# Finite-block regeneration after a total renewal stopping index

This module extends the bounded stopped-renewal theorem to a total
`ℕ`-valued stopping index.  The only stopping assumption is that every level
event `{τ = n}` is measurable from the interarrival prefix through `n`.
Because `τ` is total and `ℕ` is countable, those level events form an exactly
disjoint measurable partition of the whole canonical path space.  The proof
uses countable additivity on that partition; no boundedness, integrability, or
separate almost-sure finiteness hypothesis is needed.

It proves the iid law of every *finite* post-stop block.  It deliberately does
not assert an infinite-tail law, a conditional-law version, or a process-level
strong Markov theorem.
-/

namespace AppliedModelingLib.Probability.PoissonProcess

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

/--
A total discrete stopping index on the canonical interarrival path.  At level
`n`, the event `τ = n` may inspect exactly the coordinates through `n`; the
uninspected block therefore begins at coordinate `n + 1`.
-/
structure PrefixStoppingIndex where
  toFun : (ℕ → ℝ) → ℕ
  event_prefix_measurable : ∀ n,
    MeasurableSet[MeasurableSpace.comap (interarrivalPrefix n) inferInstance]
      {ω | toFun ω = n}

namespace PrefixStoppingIndex

instance : CoeFun PrefixStoppingIndex (fun _ => (ℕ → ℝ) → ℕ) := ⟨toFun⟩

def event (τ : PrefixStoppingIndex) (n : ℕ) : Set (ℕ → ℝ) :=
  {ω | τ ω = n}

theorem measurableSet_event (τ : PrefixStoppingIndex) (n : ℕ) :
    MeasurableSet (τ.event n) := by
  change MeasurableSet {ω | τ ω = n}
  rcases τ.event_prefix_measurable n with ⟨u, hu, hpre⟩
  rw [← hpre]
  exact (measurable_interarrivalPrefix n) hu

theorem event_pairwiseDisjoint (τ : PrefixStoppingIndex) :
    Pairwise (Function.onFun Disjoint τ.event) := by
  intro n m hnm
  refine Set.disjoint_left.2 ?_
  intro ω hωn hωm
  change τ ω = n at hωn
  change τ ω = m at hωm
  exact hnm (hωn.symm.trans hωm)

theorem iUnion_event_eq_univ (τ : PrefixStoppingIndex) :
    ⋃ n, τ.event n = Set.univ := by
  ext ω
  simp [event]

/-- The first `q` uninspected coordinates after a total prefix stopping index. -/
def postInterarrivalBlock (τ : PrefixStoppingIndex) (q : ℕ) :
    (ℕ → ℝ) → Fin q → ℝ :=
  fun ω i => interarrival (τ ω + 1 + i) ω

private theorem measurable_postInterarrivalBlock_coordinate
    (τ : PrefixStoppingIndex) (q : ℕ) (i : Fin q) :
    Measurable (fun ω => postInterarrivalBlock τ q ω i) := by
  let h : ∀ ω : ℕ → ℝ, ∃ n, τ ω = n := fun ω => ⟨τ ω, rfl⟩
  have hmeas : Measurable (fun ω => interarrival (Nat.find (h ω) + 1 + i) ω) :=
    Measurable.find
      (fun n => measurable_interarrival (n + 1 + i))
      (fun n => τ.measurableSet_event n)
      h
  convert hmeas using 1
  funext ω
  have hfind : Nat.find (h ω) = τ ω := (Nat.find_spec (h ω)).symm
  simp [postInterarrivalBlock, hfind]

theorem measurable_postInterarrivalBlock (τ : PrefixStoppingIndex) (q : ℕ) :
    Measurable (postInterarrivalBlock τ q) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_postInterarrivalBlock_coordinate τ q i

/-- At a fixed stopping level, the uninspected finite block factors from the prefix. -/
theorem event_inter_block_measure_eq_mul
    {rate : ℝ} (hrate : 0 < rate)
    (τ : PrefixStoppingIndex) (n q : ℕ)
    (s : Fin q → Set ℝ) (hs : ∀ i, MeasurableSet (s i)) :
    exponentialInterarrivalMeasure rate
      (τ.event n ∩ {ω | ∀ i, interarrivalBlock (n + 1) q ω i ∈ s i}) =
      exponentialInterarrivalMeasure rate (τ.event n) *
        ∏ i : Fin q, ProbabilityTheory.expMeasure rate (s i) := by
  have hindep := indepFun_interarrivalPrefix_interarrivalBlock hrate n q
  have hrect : {ω | ∀ i, interarrivalBlock (n + 1) q ω i ∈ s i} =
      interarrivalBlock (n + 1) q ⁻¹' Set.univ.pi s := by
    ext ω
    simp
  have hright : MeasurableSet[
      MeasurableSpace.comap (interarrivalBlock (n + 1) q) inferInstance]
      {ω | ∀ i, interarrivalBlock (n + 1) q ω i ∈ s i} := by
    rw [hrect]
    exact MeasurableSpace.measurableSet_comap.2
      ⟨Set.univ.pi s, MeasurableSet.univ_pi hs, rfl⟩
  have hfactor := hindep.meas_inter (τ.event_prefix_measurable n) hright
  calc
    exponentialInterarrivalMeasure rate
        (τ.event n ∩ {ω | ∀ i, interarrivalBlock (n + 1) q ω i ∈ s i}) =
        exponentialInterarrivalMeasure rate (τ.event n) *
          exponentialInterarrivalMeasure rate
            {ω | ∀ i, interarrivalBlock (n + 1) q ω i ∈ s i} := hfactor
    _ = exponentialInterarrivalMeasure rate (τ.event n) *
          ∏ i : Fin q, ProbabilityTheory.expMeasure rate (s i) := by
      rw [measure_interarrivalBlock_mem_eq hrate (n + 1) q s hs]

/--
Every measurable rectangular event in a finite post-stop block has the iid
exponential product probability.  This is the countable-partition extension
of `BoundedPrefixStoppingIndex.measure_postInterarrivalBlock_mem_eq`.
-/
theorem measure_postInterarrivalBlock_mem_eq
    {rate : ℝ} (hrate : 0 < rate)
    (τ : PrefixStoppingIndex) (q : ℕ)
    (s : Fin q → Set ℝ) (hs : ∀ i, MeasurableSet (s i)) :
    exponentialInterarrivalMeasure rate
      {ω | ∀ i, postInterarrivalBlock τ q ω i ∈ s i} =
      ∏ i : Fin q, ProbabilityTheory.expMeasure rate (s i) := by
  let μ : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rate
  letI : IsProbabilityMeasure μ := by
    simpa [μ] using isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  let pieces : ℕ → Set (ℕ → ℝ) := fun n =>
    τ.event n ∩ {ω | ∀ i, interarrivalBlock (n + 1) q ω i ∈ s i}
  have hblock_meas : ∀ n, MeasurableSet
      {ω | ∀ i, interarrivalBlock (n + 1) q ω i ∈ s i} := by
    intro n
    have hrect : {ω | ∀ i, interarrivalBlock (n + 1) q ω i ∈ s i} =
        interarrivalBlock (n + 1) q ⁻¹' Set.univ.pi s := by
      ext ω
      simp
    rw [hrect]
    exact (measurable_interarrivalBlock (n + 1) q) (MeasurableSet.univ_pi hs)
  have hpieces_meas : ∀ n, MeasurableSet (pieces n) := by
    intro n
    exact (τ.measurableSet_event n).inter (hblock_meas n)
  have hpieces_disjoint : Pairwise (Function.onFun Disjoint pieces) := by
    intro n m hnm
    refine Set.disjoint_left.2 ?_
    intro ω hωn hωm
    have hEn : ω ∈ τ.event n := hωn.1
    have hEm : ω ∈ τ.event m := hωm.1
    change τ ω = n at hEn
    change τ ω = m at hEm
    exact hnm (hEn.symm.trans hEm)
  have hpieces_union :
      ⋃ n, pieces n = {ω | ∀ i, postInterarrivalBlock τ q ω i ∈ s i} := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_inter_iff, pieces, event, Set.mem_setOf_eq]
    constructor
    · rintro ⟨n, hτ, hblock⟩
      simpa [postInterarrivalBlock, hτ] using hblock
    · intro hmem
      refine ⟨τ ω, rfl, ?_⟩
      simpa [postInterarrivalBlock] using hmem
  have hmeasure_pieces :
      μ {ω | ∀ i, postInterarrivalBlock τ q ω i ∈ s i} =
        ∑' n, μ (pieces n) := by
    rw [← hpieces_union]
    exact measure_iUnion hpieces_disjoint hpieces_meas
  have hsum_event : ∑' n, μ (τ.event n) = 1 := by
    calc
      ∑' n, μ (τ.event n) = μ (⋃ n, τ.event n) :=
        (measure_iUnion τ.event_pairwiseDisjoint τ.measurableSet_event).symm
      _ = μ Set.univ := congrArg μ τ.iUnion_event_eq_univ
      _ = 1 := measure_univ
  have hpieces_factor :
      (∑' n, μ (pieces n)) =
        ∑' n, μ (τ.event n) * ∏ i : Fin q, ProbabilityTheory.expMeasure rate (s i) := by
    apply tsum_congr
    intro n
    exact τ.event_inter_block_measure_eq_mul hrate n q s hs
  change μ {ω | ∀ i, postInterarrivalBlock τ q ω i ∈ s i} = _
  calc
    μ {ω | ∀ i, postInterarrivalBlock τ q ω i ∈ s i} =
        ∑' n, μ (pieces n) := hmeasure_pieces
    _ = ∑' n, μ (τ.event n) * ∏ i : Fin q, ProbabilityTheory.expMeasure rate (s i) :=
      hpieces_factor
    _ = (∑' n, μ (τ.event n)) *
          ∏ i : Fin q, ProbabilityTheory.expMeasure rate (s i) := by
      exact ENNReal.tsum_mul_right
    _ = ∏ i : Fin q, ProbabilityTheory.expMeasure rate (s i) := by
      simp [hsum_event]

/--
The finite post-stop interarrival block has the iid exponential product law.
The index is total `ℕ`-valued, and its prefix-level events are assumed
measurable; no boundedness or extra a.s.-finiteness assumption is required.
-/
theorem postInterarrivalBlock_hasLaw
    {rate : ℝ} (hrate : 0 < rate)
    (τ : PrefixStoppingIndex) (q : ℕ) :
    ProbabilityTheory.HasLaw (postInterarrivalBlock τ q)
      (Measure.pi (fun _ : Fin q => ProbabilityTheory.expMeasure rate))
      (exponentialInterarrivalMeasure rate) := by
  letI : ∀ i : Fin q, IsProbabilityMeasure (ProbabilityTheory.expMeasure rate) :=
    fun _ => ProbabilityTheory.isProbabilityMeasure_expMeasure hrate
  refine ⟨(measurable_postInterarrivalBlock τ q).aemeasurable, ?_⟩
  apply (Measure.pi_eq (μ := fun _ : Fin q => ProbabilityTheory.expMeasure rate)
    (μ' := (exponentialInterarrivalMeasure rate).map (postInterarrivalBlock τ q)) ?_).symm
  intro s hs
  have hrect : postInterarrivalBlock τ q ⁻¹' Set.univ.pi s =
      {ω | ∀ i, postInterarrivalBlock τ q ω i ∈ s i} := by
    ext ω
    simp
  calc
    (exponentialInterarrivalMeasure rate).map (postInterarrivalBlock τ q)
        (Set.univ.pi s) =
        exponentialInterarrivalMeasure rate
          (postInterarrivalBlock τ q ⁻¹' Set.univ.pi s) :=
      Measure.map_apply (measurable_postInterarrivalBlock τ q)
        (MeasurableSet.univ_pi hs)
    _ = exponentialInterarrivalMeasure rate
          {ω | ∀ i, postInterarrivalBlock τ q ω i ∈ s i} := congrArg _ hrect
    _ = ∏ i : Fin q, ProbabilityTheory.expMeasure rate (s i) :=
      measure_postInterarrivalBlock_mem_eq hrate τ q s hs

/-- The first interarrival left uninspected by a prefix stopping index.  This
is the first coordinate of the finite post-stop block, rather than a
random-index substitution in the original path. -/
def postInterarrival (τ : PrefixStoppingIndex) : (ℕ → ℝ) → ℝ :=
  fun ω => postInterarrivalBlock τ 1 ω 0

/-- The first uninspected interarrival is Borel measurable. -/
theorem measurable_postInterarrival (τ : PrefixStoppingIndex) :
    Measurable (postInterarrival τ) := by
  simpa [postInterarrival] using
    measurable_postInterarrivalBlock_coordinate τ 1 (0 : Fin 1)

/-- A total prefix stopping index leaves an exponential next interarrival.
This is a direct one-coordinate consequence of the proved finite-block
regeneration law. -/
theorem postInterarrival_hasLaw
    {rate : ℝ} (hrate : 0 < rate) (τ : PrefixStoppingIndex) :
    ProbabilityTheory.HasLaw (postInterarrival τ)
      (ProbabilityTheory.expMeasure rate) (exponentialInterarrivalMeasure rate) := by
  let μ : Fin 1 → Measure ℝ := fun _ => ProbabilityTheory.expMeasure rate
  have hprob : ∀ k : Fin 1, IsProbabilityMeasure (μ k) := fun _ =>
    ProbabilityTheory.isProbabilityMeasure_expMeasure hrate
  have heval : ProbabilityTheory.HasLaw (Function.eval (0 : Fin 1)) (μ 0)
      (Measure.pi μ) :=
    (@measurePreserving_eval (Fin 1) (fun _ : Fin 1 => ℝ) inferInstance
      (fun _ => inferInstance) μ hprob (0 : Fin 1)).hasLaw
  simpa [postInterarrival, μ, Function.comp_def] using
    heval.comp (postInterarrivalBlock_hasLaw hrate τ 1)

/-- The first uninspected interarrival is integrable at every positive rate. -/
theorem integrable_postInterarrival
    {rate : ℝ} (hrate : 0 < rate) (τ : PrefixStoppingIndex) :
    Integrable (postInterarrival τ) (exponentialInterarrivalMeasure rate) := by
  let M : Exponential.Model := Exponential.Model.mk rate hrate
  have hExp : Integrable (fun x : ℝ => x) (ProbabilityTheory.expMeasure rate) := by
    simpa [Exponential.Model.measure, M] using M.integrable_id
  have hmap : Measure.map (postInterarrival τ) (exponentialInterarrivalMeasure rate) =
      ProbabilityTheory.expMeasure rate :=
    (postInterarrival_hasLaw hrate τ).map_eq
  have hmapInt : Integrable (fun x : ℝ => x)
      (Measure.map (postInterarrival τ) (exponentialInterarrivalMeasure rate)) := by
    rw [hmap]
    exact hExp
  simpa [Function.comp_def] using
    (integrable_map_measure aestronglyMeasurable_id
      (postInterarrival_hasLaw hrate τ).aemeasurable).mp hmapInt

/-- The mean first interarrival left uninspected by a total prefix stopping
index is the reciprocal rate. -/
theorem integral_postInterarrival_eq_inv_rate
    {rate : ℝ} (hrate : 0 < rate) (τ : PrefixStoppingIndex) :
    ∫ ω, postInterarrival τ ω ∂exponentialInterarrivalMeasure rate = 1 / rate := by
  let M : Exponential.Model := Exponential.Model.mk rate hrate
  calc
    ∫ ω, postInterarrival τ ω ∂exponentialInterarrivalMeasure rate =
        ∫ x, x ∂ProbabilityTheory.expMeasure rate :=
      (postInterarrival_hasLaw hrate τ).integral_eq
    _ = M.expectedMaxValue 1 := by
      simpa [Exponential.Model.measure, M] using M.integral_id_eq_expectedMaxValue_one
    _ = 1 / rate := by
      simp [Exponential.Model.expectedMaxValue,
        Exponential.expectedMaxValueOfRate_one, M]

end PrefixStoppingIndex

end

end AppliedModelingLib.Probability.PoissonProcess
