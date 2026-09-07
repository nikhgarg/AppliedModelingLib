import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalBoundedStopping

/-!
# Finite-block regeneration after bounded renewal stopping indices

This module strengthens the single-gap bounded stopping theorem: every finite
block after a bounded prefix-measurable stopping index has the iid exponential
product law.  It is deliberately finite and bounded; it does not claim the
law of an infinite shifted tail or an unbounded almost-surely finite stop.
-/

namespace AppliedModelingLib.Probability.PoissonProcess

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

/-- A finite deterministic block of consecutive canonical interarrival coordinates. -/
def interarrivalBlock (start q : ℕ) : (ℕ → ℝ) → Fin q → ℝ :=
  fun ω i => interarrival (start + i) ω

theorem measurable_interarrivalBlock (start q : ℕ) :
    Measurable (interarrivalBlock start q) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_interarrival (start + i)

theorem iIndepFun_interarrivalBlock {rate : ℝ} (hrate : 0 < rate)
    (start q : ℕ) :
    ProbabilityTheory.iIndepFun (fun (i : Fin q) ω => interarrivalBlock start q ω i)
      (exponentialInterarrivalMeasure rate) := by
  simpa [interarrivalBlock] using
    (ProbabilityTheory.iIndepFun.precomp (g := fun i : Fin q => start + i)
      (by
        intro a b hab
        exact Fin.ext (Nat.add_left_cancel hab))
      (iIndepFun_interarrival hrate))

/-- A deterministic finite block has the product of its exponential coordinate laws. -/
theorem interarrivalBlock_hasLaw {rate : ℝ} (hrate : 0 < rate)
    (start q : ℕ) :
    ProbabilityTheory.HasLaw (interarrivalBlock start q)
      (Measure.pi (fun _ : Fin q => ProbabilityTheory.expMeasure rate))
      (exponentialInterarrivalMeasure rate) := by
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure rate) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  refine ⟨(measurable_interarrivalBlock start q).aemeasurable, ?_⟩
  have hmap :=
    (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
      (f := fun (i : Fin q) ω => interarrivalBlock start q ω i)
      (μ := exponentialInterarrivalMeasure rate)
      (fun i => (measurable_interarrival (start + i)).aemeasurable)).mp
      (iIndepFun_interarrivalBlock hrate start q)
  calc
    (exponentialInterarrivalMeasure rate).map (interarrivalBlock start q) =
        Measure.pi (fun i : Fin q =>
          (exponentialInterarrivalMeasure rate).map
            (fun ω => interarrivalBlock start q ω i)) := by
      simpa only using hmap
    _ = Measure.pi (fun _ : Fin q => ProbabilityTheory.expMeasure rate) := by
      congr 1
      funext i
      exact (interarrival_hasLaw hrate (start + i)).map_eq

/-- The inspected prefix through `n` is independent of every finite block after it. -/
theorem indepFun_interarrivalPrefix_interarrivalBlock
    {rate : ℝ} (hrate : 0 < rate) (n q : ℕ) :
    ProbabilityTheory.IndepFun (interarrivalPrefix n) (interarrivalBlock (n + 1) q)
      (exponentialInterarrivalMeasure rate) := by
  have hdisjoint : Disjoint (Finset.range (n + 1)) (Finset.Ico (n + 1) (n + 1 + q)) := by
    rw [Finset.disjoint_left]
    intro i hi hj
    have hil : i < n + 1 := Finset.mem_range.mp hi
    have hir : n + 1 ≤ i := (Finset.mem_Ico.mp hj).1
    omega
  have hraw := (iIndepFun_interarrival hrate).indepFun_finset
    (Finset.range (n + 1)) (Finset.Ico (n + 1) (n + 1 + q)) hdisjoint
    (fun i => measurable_interarrival i)
  let e : Fin q → (Finset.Ico (n + 1) (n + 1 + q)) := fun i =>
    ⟨n + 1 + i, Finset.mem_Ico.mpr ⟨Nat.le_add_right _ _, by omega⟩⟩
  let reindex : ((Finset.Ico (n + 1) (n + 1 + q)) → ℝ) → Fin q → ℝ :=
    fun g i => g (e i)
  have hreindex : Measurable reindex := by
    apply measurable_pi_lambda
    intro i
    exact measurable_pi_apply (e i)
  have hcomp := hraw.comp measurable_id hreindex
  simpa [interarrivalPrefix, interarrivalBlock, reindex, e, Function.comp_def] using hcomp

/-- Measurable rectangular events of a deterministic finite block factor coordinatewise. -/
theorem measure_interarrivalBlock_mem_eq {rate : ℝ} (hrate : 0 < rate)
    (start q : ℕ) (s : Fin q → Set ℝ) (hs : ∀ i, MeasurableSet (s i)) :
    exponentialInterarrivalMeasure rate
      {ω | ∀ i, interarrivalBlock start q ω i ∈ s i} =
      ∏ i : Fin q, ProbabilityTheory.expMeasure rate (s i) := by
  have hrect : {ω | ∀ i, interarrivalBlock start q ω i ∈ s i} =
      interarrivalBlock start q ⁻¹' Set.univ.pi s := by
    ext ω
    simp
  letI : ∀ i : Fin q, IsProbabilityMeasure (ProbabilityTheory.expMeasure rate) :=
    fun _ => ProbabilityTheory.isProbabilityMeasure_expMeasure hrate
  rw [hrect]
  calc
    exponentialInterarrivalMeasure rate
        (interarrivalBlock start q ⁻¹' Set.univ.pi s) =
        (exponentialInterarrivalMeasure rate).map (interarrivalBlock start q)
          (Set.univ.pi s) :=
      (Measure.map_apply (measurable_interarrivalBlock start q)
        (MeasurableSet.univ_pi hs)).symm
    _ = Measure.pi (fun _ : Fin q => ProbabilityTheory.expMeasure rate)
          (Set.univ.pi s) := by
      rw [(interarrivalBlock_hasLaw hrate start q).map_eq]
    _ = ∏ i : Fin q, ProbabilityTheory.expMeasure rate (s i) := by
      rw [Measure.pi_pi]

namespace BoundedPrefixStoppingIndex

/-- The first `q` uninspected coordinates after a bounded prefix stopping index. -/
def postInterarrivalBlock {bound : ℕ} (τ : BoundedPrefixStoppingIndex bound) (q : ℕ) :
    (ℕ → ℝ) → Fin q → ℝ :=
  fun ω i => interarrival (τ ω + 1 + i) ω

theorem postInterarrivalBlock_apply_eq_sum_indicator {bound : ℕ}
    (τ : BoundedPrefixStoppingIndex bound) (q : ℕ) (i : Fin q) :
    (fun ω => postInterarrivalBlock τ q ω i) = fun ω =>
      ∑ n ∈ Finset.range (bound + 1),
        (τ.event n).indicator (interarrival (n + 1 + i)) ω := by
  funext ω
  unfold postInterarrivalBlock
  symm
  rw [Finset.sum_eq_single_of_mem (τ ω)
    (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (τ.le_bound ω)))]
  · simp [event]
  · intro n hn hne
    rw [Set.indicator_of_notMem]
    intro hmem
    change τ ω = n at hmem
    exact hne hmem.symm

theorem measurable_postInterarrivalBlock {bound : ℕ}
    (τ : BoundedPrefixStoppingIndex bound) (q : ℕ) :
    Measurable (postInterarrivalBlock τ q) := by
  apply measurable_pi_lambda
  intro i
  rw [postInterarrivalBlock_apply_eq_sum_indicator τ q i]
  exact (Finset.range (bound + 1)).measurable_sum fun n hn =>
    (measurable_interarrival (n + 1 + i)).indicator
      (τ.measurableSet_event n (Nat.le_of_lt_succ (by simpa using hn)))

/-- At a fixed stopping-index level, the uninspected finite block factors from the prefix. -/
theorem event_inter_block_measure_eq_mul
    {rate : ℝ} (hrate : 0 < rate) {bound : ℕ}
    (τ : BoundedPrefixStoppingIndex bound) (n : ℕ) (hn : n ≤ bound)
    (q : ℕ) (s : Fin q → Set ℝ) (hs : ∀ i, MeasurableSet (s i)) :
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
  have hfactor := hindep.meas_inter (τ.event_prefix_measurable n hn) hright
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
Finite-valued renewal regeneration for the first finite block after a bounded
prefix stopping index.  Every measurable rectangular event of that block has
the iid exponential product probability.
-/
theorem measure_postInterarrivalBlock_mem_eq
    {rate : ℝ} (hrate : 0 < rate) {bound : ℕ}
    (τ : BoundedPrefixStoppingIndex bound) (q : ℕ)
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
  have hpieces_meas : ∀ n ∈ Finset.range (bound + 1), MeasurableSet (pieces n) := by
    intro n hn
    exact (τ.measurableSet_event n (Nat.le_of_lt_succ (by simpa using hn))).inter
      (hblock_meas n)
  have hpieces_disjoint :
      (↑(Finset.range (bound + 1)) : Set ℕ).PairwiseDisjoint pieces := by
    intro n hn m hm hnm
    refine Set.disjoint_left.2 ?_
    intro ω hωn hωm
    have hEn : ω ∈ τ.event n := hωn.1
    have hEm : ω ∈ τ.event m := hωm.1
    change τ ω = n at hEn
    change τ ω = m at hEm
    exact hnm (hEn.symm.trans hEm)
  have hpieces_union :
      ⋃ n ∈ Finset.range (bound + 1), pieces n =
        {ω | ∀ i, postInterarrivalBlock τ q ω i ∈ s i} := by
    ext ω
    simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_inter_iff, pieces, event,
      Set.mem_setOf_eq]
    constructor
    · rintro ⟨n, hn, hτ, hblock⟩
      simpa [postInterarrivalBlock, hτ] using hblock
    · intro hmem
      refine ⟨τ ω, Nat.lt_succ_iff.mpr (τ.le_bound ω), rfl, ?_⟩
      simpa [postInterarrivalBlock] using hmem
  have hmeasure_pieces :
      μ {ω | ∀ i, postInterarrivalBlock τ q ω i ∈ s i} =
        ∑ n ∈ Finset.range (bound + 1), μ (pieces n) := by
    rw [← hpieces_union]
    exact measure_biUnion_finset hpieces_disjoint hpieces_meas
  have hevent_meas : ∀ n ∈ Finset.range (bound + 1), MeasurableSet (τ.event n) := by
    intro n hn
    exact τ.measurableSet_event n (Nat.le_of_lt_succ (by simpa using hn))
  have hevent_disjoint :
      (↑(Finset.range (bound + 1)) : Set ℕ).PairwiseDisjoint τ.event :=
    τ.event_pairwiseDisjoint.subset (by intro n _; exact Set.mem_univ n)
  have hsum_event :
      ∑ n ∈ Finset.range (bound + 1), μ (τ.event n) = 1 := by
    calc
      ∑ n ∈ Finset.range (bound + 1), μ (τ.event n) =
          μ (⋃ n ∈ Finset.range (bound + 1), τ.event n) :=
        (measure_biUnion_finset hevent_disjoint hevent_meas).symm
      _ = μ Set.univ := congrArg μ τ.biUnion_event_eq_univ
      _ = 1 := measure_univ
  have hpieces_factor :
      ∑ n ∈ Finset.range (bound + 1), μ (pieces n) =
        ∑ n ∈ Finset.range (bound + 1),
          μ (τ.event n) * ∏ i : Fin q, ProbabilityTheory.expMeasure rate (s i) := by
    apply Finset.sum_congr rfl
    intro n hn
    exact τ.event_inter_block_measure_eq_mul hrate n
      (Nat.le_of_lt_succ (by simpa using hn)) q s hs
  change μ {ω | ∀ i, postInterarrivalBlock τ q ω i ∈ s i} = _
  calc
    μ {ω | ∀ i, postInterarrivalBlock τ q ω i ∈ s i} =
        ∑ n ∈ Finset.range (bound + 1), μ (pieces n) := hmeasure_pieces
    _ = ∑ n ∈ Finset.range (bound + 1),
          μ (τ.event n) * ∏ i : Fin q, ProbabilityTheory.expMeasure rate (s i) :=
      hpieces_factor
    _ = (∑ n ∈ Finset.range (bound + 1), μ (τ.event n)) *
          ∏ i : Fin q, ProbabilityTheory.expMeasure rate (s i) := by
      rw [Finset.sum_mul]
    _ = ∏ i : Fin q, ProbabilityTheory.expMeasure rate (s i) := by
      simp [hsum_event]

/--
The finite future block after a bounded prefix stopping index has the iid
exponential product law.  This is a finite bounded-index regeneration theorem;
it does not yet cover an unbounded almost-surely finite stopping index.
-/
theorem postInterarrivalBlock_hasLaw
    {rate : ℝ} (hrate : 0 < rate) {bound : ℕ}
    (τ : BoundedPrefixStoppingIndex bound) (q : ℕ) :
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

end BoundedPrefixStoppingIndex

end

end AppliedModelingLib.Probability.PoissonProcess
