import AppliedModelingLib.Foundations.Probability.ExponentialInterarrival

/-!
# Bounded stopping-index regeneration for canonical exponential interarrivals

For a bounded discrete index whose level event `{τ = n}` is measurable from
the interarrival coordinates through `n`, the first uninspected coordinate
`X_(τ+1)` has the original exponential law.  This is a proved finite stopping
result, not a stand-in for the full random-index strong Markov theorem: it does
not yet establish independence of the entire future tail or treat an unbounded
almost-surely finite index.
-/

namespace AppliedModelingLib.Probability.PoissonProcess

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

/-- The finite prefix of a canonical interarrival path through index `n`. -/
def interarrivalPrefix (n : ℕ) : (ℕ → ℝ) → ((Finset.range (n + 1)) → ℝ) :=
  fun ω i => interarrival i ω

theorem measurable_interarrivalPrefix (n : ℕ) : Measurable (interarrivalPrefix n) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_interarrival i

/--
A bounded discrete stopping index, with the event `τ = n` certified measurable
with respect to exactly the coordinate prefix through `n`.

The next unused interarrival is therefore coordinate `τ + 1`.
-/
structure BoundedPrefixStoppingIndex (bound : ℕ) where
  toFun : (ℕ → ℝ) → ℕ
  le_bound : ∀ ω, toFun ω ≤ bound
  event_prefix_measurable : ∀ n, n ≤ bound →
    MeasurableSet[MeasurableSpace.comap (interarrivalPrefix n) inferInstance]
      {ω | toFun ω = n}

namespace BoundedPrefixStoppingIndex

instance {bound : ℕ} : CoeFun (BoundedPrefixStoppingIndex bound)
    (fun _ => (ℕ → ℝ) → ℕ) := ⟨toFun⟩

def event {bound : ℕ} (τ : BoundedPrefixStoppingIndex bound) (n : ℕ) : Set (ℕ → ℝ) :=
  {ω | τ ω = n}

theorem event_prefix_measurable_of_le {bound : ℕ} (τ : BoundedPrefixStoppingIndex bound)
    (n : ℕ) (hn : n ≤ bound) :
    MeasurableSet[MeasurableSpace.comap (interarrivalPrefix n) inferInstance] (τ.event n) :=
  τ.event_prefix_measurable n hn

theorem measurableSet_event {bound : ℕ} (τ : BoundedPrefixStoppingIndex bound)
    (n : ℕ) (hn : n ≤ bound) : MeasurableSet (τ.event n) := by
  change MeasurableSet {ω | τ ω = n}
  rcases τ.event_prefix_measurable n hn with ⟨u, hu, hpre⟩
  rw [← hpre]
  exact (measurable_interarrivalPrefix n) hu

theorem event_pairwiseDisjoint {bound : ℕ} (τ : BoundedPrefixStoppingIndex bound) :
    (Set.univ : Set ℕ).PairwiseDisjoint τ.event := by
  intro n _ m _ hnm
  refine Set.disjoint_left.2 ?_
  intro ω hωn hωm
  change τ ω = n at hωn
  change τ ω = m at hωm
  exact hnm (hωn.symm.trans hωm)

theorem biUnion_event_eq_univ {bound : ℕ} (τ : BoundedPrefixStoppingIndex bound) :
    ⋃ n ∈ Finset.range (bound + 1), τ.event n = Set.univ := by
  ext ω
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  refine ⟨τ ω, Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (τ.le_bound ω)), rfl⟩

theorem event_inter_next_measure_eq_mul
    {rate : ℝ} (hrate : 0 < rate) {bound : ℕ}
    (τ : BoundedPrefixStoppingIndex bound) (n : ℕ) (hn : n ≤ bound)
    (s : Set ℝ) (hs : MeasurableSet s) :
    exponentialInterarrivalMeasure rate
      (τ.event n ∩ interarrival (n + 1) ⁻¹' s) =
      exponentialInterarrivalMeasure rate (τ.event n) *
        ProbabilityTheory.expMeasure rate s := by
  have hindep : ProbabilityTheory.IndepFun (interarrivalPrefix n) (interarrival (n + 1))
      (exponentialInterarrivalMeasure rate) := by
    have hdisjoint : Disjoint (Finset.range (n + 1)) ({n + 1} : Finset ℕ) := by
      simp
    have hraw := (iIndepFun_interarrival hrate).indepFun_finset (Finset.range (n + 1)) {n + 1} hdisjoint
      (fun i => measurable_interarrival i)
    let iNext : ({n + 1} : Finset ℕ) := ⟨n + 1, Finset.mem_singleton_self _⟩
    simpa [interarrivalPrefix, iNext] using
      hraw.comp measurable_id (measurable_pi_apply iNext)
  have hright : MeasurableSet[MeasurableSpace.comap (interarrival (n + 1)) inferInstance]
      (interarrival (n + 1) ⁻¹' s) :=
    MeasurableSpace.measurableSet_comap.2 ⟨s, hs, rfl⟩
  have hfactor :
      exponentialInterarrivalMeasure rate
        (τ.event n ∩ interarrival (n + 1) ⁻¹' s) =
      exponentialInterarrivalMeasure rate (τ.event n) *
        exponentialInterarrivalMeasure rate (interarrival (n + 1) ⁻¹' s) :=
    hindep.meas_inter (τ.event_prefix_measurable n hn) hright
  have hcoord :
      exponentialInterarrivalMeasure rate (interarrival (n + 1) ⁻¹' s) =
        (ProbabilityTheory.expMeasure rate) s := by
    exact (Measure.map_apply (measurable_interarrival (n + 1)) hs).symm.trans
      (congrArg (fun ν : Measure ℝ => ν s) (interarrival_hasLaw hrate (n + 1)).map_eq)
  exact hfactor.trans
    (congrArg (fun x => exponentialInterarrivalMeasure rate (τ.event n) * x) hcoord)

/-- The first coordinate not inspected by a bounded discrete stopping index. -/
def postInterarrival {bound : ℕ} (τ : BoundedPrefixStoppingIndex bound) : (ℕ → ℝ) → ℝ :=
  fun ω => interarrival (τ ω + 1) ω

theorem postInterarrival_eq_sum_indicator {bound : ℕ} (τ : BoundedPrefixStoppingIndex bound) :
    postInterarrival τ = fun ω =>
      ∑ n ∈ Finset.range (bound + 1),
        (τ.event n).indicator (interarrival (n + 1)) ω := by
  funext ω
  unfold postInterarrival
  symm
  rw [Finset.sum_eq_single_of_mem (τ ω)
    (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (τ.le_bound ω)))]
  · simp [event]
  · intro n hn hne
    rw [Set.indicator_of_notMem]
    intro hmem
    change τ ω = n at hmem
    exact hne hmem.symm

theorem measurable_postInterarrival {bound : ℕ} (τ : BoundedPrefixStoppingIndex bound) :
    Measurable (postInterarrival τ) := by
  rw [postInterarrival_eq_sum_indicator]
  exact (Finset.range (bound + 1)).measurable_sum fun n hn =>
    (measurable_interarrival (n + 1)).indicator
      (τ.measurableSet_event n (Nat.le_of_lt_succ (by simpa using hn)))

/--
Finite-valued discrete regeneration for the canonical iid exponential path.
If `τ` is bounded and each event `τ = n` is measurable with respect to the
coordinates through `n`, then the first untouched interarrival `X_(τ+1)` has
the original exponential law.
-/
theorem measure_postInterarrival_mem_eq
    {rate : ℝ} (hrate : 0 < rate) {bound : ℕ}
    (τ : BoundedPrefixStoppingIndex bound)
    (s : Set ℝ) (hs : MeasurableSet s) :
    exponentialInterarrivalMeasure rate
      {ω | interarrival (τ ω + 1) ω ∈ s} =
      ProbabilityTheory.expMeasure rate s := by
  let μ : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rate
  letI : IsProbabilityMeasure μ := by
    simpa [μ] using isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  let pieces : ℕ → Set (ℕ → ℝ) :=
    fun n => τ.event n ∩ interarrival (n + 1) ⁻¹' s
  have hpieces_meas : ∀ n ∈ Finset.range (bound + 1), MeasurableSet (pieces n) := by
    intro n hn
    exact (τ.measurableSet_event n (Nat.le_of_lt_succ (by simpa using hn))).inter
      ((measurable_interarrival (n + 1)) hs)
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
        {ω | interarrival (τ ω + 1) ω ∈ s} := by
    ext ω
    simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_inter_iff, pieces, event,
      Set.mem_preimage, Set.mem_setOf_eq]
    constructor
    · rintro ⟨n, hn, hτ, hnmem⟩
      simpa [hτ] using hnmem
    · intro hmem
      refine ⟨τ ω, Nat.lt_succ_iff.mpr (τ.le_bound ω), rfl, ?_⟩
      simpa using hmem
  have hmeasure_pieces :
      μ {ω | interarrival (τ ω + 1) ω ∈ s} =
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
          μ (τ.event n) * ProbabilityTheory.expMeasure rate s := by
    apply Finset.sum_congr rfl
    intro n hn
    exact τ.event_inter_next_measure_eq_mul hrate n
      (Nat.le_of_lt_succ (by simpa using hn)) s hs
  change μ {ω | interarrival (τ ω + 1) ω ∈ s} = _
  calc
    μ {ω | interarrival (τ ω + 1) ω ∈ s} =
        ∑ n ∈ Finset.range (bound + 1), μ (pieces n) := hmeasure_pieces
    _ = ∑ n ∈ Finset.range (bound + 1),
          μ (τ.event n) * ProbabilityTheory.expMeasure rate s := hpieces_factor
    _ = (∑ n ∈ Finset.range (bound + 1), μ (τ.event n)) *
          ProbabilityTheory.expMeasure rate s := by
      rw [Finset.sum_mul]
    _ = ProbabilityTheory.expMeasure rate s := by simp [hsum_event]

/-- The bounded stopped future coordinate has the original exponential law. -/
theorem postInterarrival_hasLaw
    {rate : ℝ} (hrate : 0 < rate) {bound : ℕ}
    (τ : BoundedPrefixStoppingIndex bound) :
    ProbabilityTheory.HasLaw (postInterarrival τ)
      (ProbabilityTheory.expMeasure rate) (exponentialInterarrivalMeasure rate) := by
  refine ⟨(measurable_postInterarrival τ).aemeasurable, ?_⟩
  ext s hs
  simpa [postInterarrival] using
    (Measure.map_apply (measurable_postInterarrival τ) hs).trans
      (measure_postInterarrival_mem_eq hrate τ s hs)

end BoundedPrefixStoppingIndex

end

end PoissonProcess
end Probability
end AppliedModelingLib
