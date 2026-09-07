import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalForwardPoisson
import AppliedModelingLib.Foundations.Probability.ForwardPoissonTransport
import AppliedModelingLib.Foundations.Probability.FiniteProductCoordinateFactors

/-!
# Independent finite-class forward Poisson input

This module constructs a finite family of independent forward homogeneous
Poisson processes on one product probability space.  Each class owns a full
interarrival path; independence is consequently an independence statement
about complete paths, not just about one selected count or a named wrapper.

It is the forward-input layer for finite-class queueing models.  It does not
make a stationarity, Palm, thinning, service-mark, or scheduling claim.
-/

namespace AppliedModelingLib.Probability.PoissonProcess

open MeasureTheory Filter

noncomputable section

variable {Class : Type*} [Fintype Class]

local instance multiclassForwardPoissonDecidableEq : DecidableEq Class := Classical.decEq Class

/-- Product law carrying one canonical exponential-interarrival path for each
class of a finite queueing system. -/
def multiclassForwardArrivalMeasure (rate : Class → ℝ) :
    Measure (Class → ℕ → ℝ) :=
  Measure.pi fun i => exponentialInterarrivalMeasure (rate i)

/-- The finite-class product carrier is a probability space when every class
has a positive arrival rate. -/
theorem isProbabilityMeasure_multiclassForwardArrivalMeasure
    (rate : Class → ℝ) (hrate : ∀ i, 0 < rate i) :
    IsProbabilityMeasure (multiclassForwardArrivalMeasure rate) := by
  let μ : Class → Measure (ℕ → ℝ) :=
    fun i => exponentialInterarrivalMeasure (rate i)
  letI : ∀ i, IsProbabilityMeasure (μ i) := fun i =>
    isProbabilityMeasure_exponentialInterarrivalMeasure (hrate i)
  simpa [multiclassForwardArrivalMeasure, μ] using
    (inferInstance : IsProbabilityMeasure (Measure.pi μ))

/-- The concrete forward Poisson process of one class, carried by the joint
finite-class input space. -/
def multiclassForwardPoissonCountingProcess
    (rate : Class → ℝ) (hrate : ∀ i, 0 < rate i) (i : Class) :
    ForwardHomogeneousPoissonCountingProcessByLaw (Class → ℕ → ℝ)
      (multiclassForwardArrivalMeasure rate) := by
  let μ : Class → Measure (ℕ → ℝ) :=
    fun j => exponentialInterarrivalMeasure (rate j)
  letI : ∀ j, IsProbabilityMeasure (μ j) := fun j =>
    isProbabilityMeasure_exponentialInterarrivalMeasure (hrate j)
  simpa [multiclassForwardArrivalMeasure, μ] using
    (canonicalForwardHomogeneousPoissonCountingProcessByLaw (hrate i)).compMeasurePreserving
      (Function.eval i) (measurePreserving_eval μ i)

/-- The complete interarrival paths of the finite family are independent.
This is stronger than independence of any individual collection of count
increments and is the input-level independence needed by an eventual GPS
execution. -/
theorem iIndepFun_multiclassForwardArrivalPaths
    (rate : Class → ℝ) (hrate : ∀ i, 0 < rate i) :
    ProbabilityTheory.iIndepFun (fun i (ω : Class → ℕ → ℝ) => ω i)
      (multiclassForwardArrivalMeasure rate) := by
  let μ : Class → Measure (ℕ → ℝ) :=
    fun i => exponentialInterarrivalMeasure (rate i)
  letI : ∀ i, IsProbabilityMeasure (μ i) := fun i =>
    isProbabilityMeasure_exponentialInterarrivalMeasure (hrate i)
  simpa [multiclassForwardArrivalMeasure, μ] using
    (ProbabilityTheory.iIndepFun_pi (X := fun _ : Class => id)
      (fun _ => aemeasurable_id))

/-- Separate all nondistinguished full arrival paths, the selected path's
finite history at a deterministic clock, and that path's residual tail. -/
def multiclassForwardHistoryResidualFactor
    (i : Class) (s : ℝ) :
    (Class → ℕ → ℝ) →
      (({j : Class // j ≠ i} → ℕ → ℝ) × (ℕ × (ℕ → ℝ))) × (ℕ → ℝ) :=
  fun ω =>
    Prod.mk
      (Prod.mk (piWithoutCoordinate (α := ℕ → ℝ) i ω).1
        (canonicalRenewalPastHistory s (ω i)))
      (residualTail s (ω i))

theorem measurable_multiclassForwardHistoryResidualFactor
    (i : Class) (s : ℝ) :
    Measurable (multiclassForwardHistoryResidualFactor i s) := by
  let q := piWithoutCoordinate (α := ℕ → ℝ) i
  have hq : Measurable q := measurable_piWithoutCoordinate i
  exact
    ((measurable_fst.comp hq).prodMk
      ((measurable_canonicalRenewalPastHistory s).comp (measurable_snd.comp hq))).prodMk
      ((measurable_residualTail s).comp (measurable_snd.comp hq))

/-- The finite-class input law factors into the complete paths of the other
classes, the selected path's full pre-clock history, and an independent
fresh residual tail. -/
theorem map_multiclassForwardHistoryResidualFactor
    (rate : Class → ℝ) (hrate : ∀ i, 0 < rate i)
    (i : Class) (s : ℝ) (hs : 0 ≤ s) :
    Measure.map (multiclassForwardHistoryResidualFactor i s)
      (multiclassForwardArrivalMeasure rate) =
      ((Measure.pi fun j : {k : Class // k ≠ i} =>
        exponentialInterarrivalMeasure (rate j.1)).prod
        (Measure.map (canonicalRenewalPastHistory s)
          (exponentialInterarrivalMeasure (rate i)))).prod
        (exponentialInterarrivalMeasure (rate i)) := by
  let μ : Class → Measure (ℕ → ℝ) :=
    fun j => exponentialInterarrivalMeasure (rate j)
  let ρ : Measure ({j : Class // j ≠ i} → ℕ → ℝ) :=
    Measure.pi fun j => μ j.1
  let H : (ℕ → ℝ) → ℕ × (ℕ → ℝ) := canonicalRenewalPastHistory s
  let R : (ℕ → ℝ) → ℕ → ℝ := residualTail s
  let q := piWithoutCoordinate (α := ℕ → ℝ) i
  let f : ({j : Class // j ≠ i} → ℕ → ℝ) × (ℕ → ℝ) →
      (({j : Class // j ≠ i} → ℕ → ℝ) × (ℕ × (ℕ → ℝ))) × (ℕ → ℝ) :=
    fun x => ((x.1, H x.2), R x.2)
  letI : ∀ j : Class, IsProbabilityMeasure (μ j) := by
    intro j
    exact isProbabilityMeasure_exponentialInterarrivalMeasure (hrate j)
  letI : IsProbabilityMeasure ρ := by
    dsimp [ρ]
    infer_instance
  letI : IsProbabilityMeasure (μ i) := by
    dsimp [μ]
    exact isProbabilityMeasure_exponentialInterarrivalMeasure (hrate i)
  have hH : Measurable H := by
    simpa [H] using measurable_canonicalRenewalPastHistory s
  have hR : Measurable R := by
    simpa [R] using measurable_residualTail s
  letI : IsProbabilityMeasure (Measure.map H (μ i)) :=
    Measure.isProbabilityMeasure_map hH.aemeasurable
  have hpair : Measurable (fun ξ : ℕ → ℝ => (H ξ, R ξ)) := hH.prodMk hR
  have hf : Measurable f := by
    exact ((measurable_fst).prodMk (hH.comp measurable_snd)).prodMk
      (hR.comp measurable_snd)
  have hfactor :
      Measure.map f (ρ.prod (μ i)) =
        (ρ.prod (Measure.map H (μ i))).prod (μ i) := by
    let assoc : ({j : Class // j ≠ i} → ℕ → ℝ) ×
        ((ℕ × (ℕ → ℝ)) × (ℕ → ℝ)) →
        (({j : Class // j ≠ i} → ℕ → ℝ) × (ℕ × (ℕ → ℝ))) × (ℕ → ℝ) :=
      (MeasurableEquiv.prodAssoc :
        (({j : Class // j ≠ i} → ℕ → ℝ) × (ℕ × (ℕ → ℝ))) × (ℕ → ℝ) ≃ᵐ
          ({j : Class // j ≠ i} → ℕ → ℝ) × ((ℕ × (ℕ → ℝ)) × (ℕ → ℝ))).symm
    let raw : ({j : Class // j ≠ i} → ℕ → ℝ) × (ℕ → ℝ) →
        ({j : Class // j ≠ i} → ℕ → ℝ) × ((ℕ × (ℕ → ℝ)) × (ℕ → ℝ)) :=
      fun x => (x.1, (H x.2, R x.2))
    have hraw : Measurable raw := measurable_id.prodMap hpair
    have hassoc : Measurable assoc := by
      exact (MeasurableEquiv.prodAssoc :
        (({j : Class // j ≠ i} → ℕ → ℝ) × (ℕ × (ℕ → ℝ))) × (ℕ → ℝ) ≃ᵐ
          ({j : Class // j ≠ i} → ℕ → ℝ) × ((ℕ × (ℕ → ℝ)) × (ℕ → ℝ))).symm.measurable
    have hHR : Measure.map (fun ξ : ℕ → ℝ => (H ξ, R ξ)) (μ i) =
        (Measure.map H (μ i)).prod (μ i) := by
      calc
        Measure.map (fun ξ : ℕ → ℝ => (H ξ, R ξ)) (μ i) =
            (Measure.map H (μ i)).prod (Measure.map R (μ i)) := by
              exact (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
                hH.aemeasurable hR.aemeasurable).mp
                (canonicalRenewalPastHistory_indep_residualTail (hrate i) hs)
        _ = (Measure.map H (μ i)).prod (μ i) := by
              rw [(residualTail_hasLaw_path (hrate i) hs).map_eq]
    change Measure.map (assoc ∘ raw) (ρ.prod (μ i)) = _
    rw [← Measure.map_map hassoc hraw]
    change Measure.map assoc
      (Measure.map (Prod.map id (fun ξ : ℕ → ℝ => (H ξ, R ξ)))
        (ρ.prod (μ i))) = _
    rw [← Measure.map_prod_map ρ (μ i) measurable_id hpair,
      Measure.map_id, hHR]
    exact (measurePreserving_prodAssoc ρ (Measure.map H (μ i)) (μ i)).symm.map_eq
  change Measure.map (f ∘ q) (Measure.pi μ) =
    (ρ.prod (Measure.map H (μ i))).prod (μ i)
  rw [← Measure.map_map hf (measurable_piWithoutCoordinate i),
    map_piWithoutCoordinate μ i]
  change Measure.map f (ρ.prod (μ i)) = _
  exact hfactor

/-- The full-history/residual-tail factor map is measure preserving onto its
explicit product law. -/
theorem multiclassForwardHistoryResidualFactor_measurePreserving
    (rate : Class → ℝ) (hrate : ∀ i, 0 < rate i)
    (i : Class) (s : ℝ) (hs : 0 ≤ s) :
    MeasurePreserving (multiclassForwardHistoryResidualFactor i s)
      (multiclassForwardArrivalMeasure rate)
      (
        ((Measure.pi fun j : {k : Class // k ≠ i} =>
          exponentialInterarrivalMeasure (rate j.1)).prod
          (Measure.map (canonicalRenewalPastHistory s)
            (exponentialInterarrivalMeasure (rate i)))).prod
          (exponentialInterarrivalMeasure (rate i))
      ) := by
  exact ⟨measurable_multiclassForwardHistoryResidualFactor i s,
    map_multiclassForwardHistoryResidualFactor rate hrate i s hs⟩

/-- The finite set of forward arrival indices of one class by a finite time.
It is defined from the concrete renewal path, not inferred from a count law. -/
noncomputable def multiclassForwardArrivalIndices
    (i : Class) (t : ℝ) (ω : Class → ℕ → ℝ) : Finset ℕ :=
  Finset.range (canonicalRenewalCount t (ω i))

/-- On the joint finite-class carrier, each local arrival ledger enumerates
exactly the arrivals of its class that have occurred by its horizon.  The
simultaneous quantifiers are important: this is a finite-class path property,
not a collection of unrelated fixed-time marginal statements. -/
theorem ae_mem_multiclassForwardArrivalIndices_iff
    (rate : Class → ℝ) (hrate : ∀ i, 0 < rate i) :
    ∀ᵐ ω ∂multiclassForwardArrivalMeasure rate, ∀ i : Class, ∀ t : ℝ, ∀ n : ℕ,
      n ∈ multiclassForwardArrivalIndices i t ω ↔ arrivalTime n (ω i) ≤ t := by
  let μ : Class → Measure (ℕ → ℝ) :=
    fun i => exponentialInterarrivalMeasure (rate i)
  letI : ∀ i, IsProbabilityMeasure (μ i) := fun i =>
    isProbabilityMeasure_exponentialInterarrivalMeasure (hrate i)
  rw [ae_all_iff]
  intro i
  have hcoordinate : ∀ᵐ ω ∂Measure.pi μ, ∀ t : ℝ, ∀ n : ℕ,
      n < canonicalRenewalCount t (ω i) ↔ arrivalTime n (ω i) ≤ t := by
    refine ae_of_ae_map (μ := Measure.pi μ) (f := Function.eval i)
      (p := fun ξ : ℕ → ℝ => ∀ t : ℝ, ∀ n : ℕ,
        n < canonicalRenewalCount t ξ ↔ arrivalTime n ξ ≤ t)
      (measurePreserving_eval μ i).measurable.aemeasurable ?_
    rw [(measurePreserving_eval μ i).map_eq]
    exact ae_lt_canonicalRenewalCount_iff_arrivalTime_le (hrate i)
  simpa [multiclassForwardArrivalMeasure, μ, multiclassForwardArrivalIndices,
    Finset.mem_range] using hcoordinate

/-- Every class path in the joint finite-class carrier is nonexplosive and
strictly ordered almost surely.  Together with the finite ledger above, this
is the path-level local-finiteness fact needed before an event-driven scheduler
can be defined. -/
theorem ae_multiclassForwardArrivalPaths_nonexplosive_strict
    (rate : Class → ℝ) (hrate : ∀ i, 0 < rate i) :
    ∀ᵐ ω ∂multiclassForwardArrivalMeasure rate, ∀ i : Class,
      Tendsto (fun n : ℕ => arrivalTime n (ω i)) atTop atTop ∧
        StrictMono (fun n : ℕ => arrivalTime n (ω i)) := by
  let μ : Class → Measure (ℕ → ℝ) :=
    fun i => exponentialInterarrivalMeasure (rate i)
  letI : ∀ i, IsProbabilityMeasure (μ i) := fun i =>
    isProbabilityMeasure_exponentialInterarrivalMeasure (hrate i)
  rw [ae_all_iff]
  intro i
  refine ae_of_ae_map (μ := Measure.pi μ) (f := Function.eval i)
    (p := fun ξ : ℕ → ℝ =>
      Tendsto (fun n : ℕ => arrivalTime n ξ) atTop atTop ∧
        StrictMono (fun n : ℕ => arrivalTime n ξ))
    (measurePreserving_eval μ i).measurable.aemeasurable ?_
  rw [(measurePreserving_eval μ i).map_eq]
  exact (ae_arrivalTime_tendsto_atTop (hrate i)).and
    (ae_arrivalTime_strictMono (hrate i))

/-- On the same good carrier, each class has a strictly later next arrival at
every finite time.  An event scheduler can therefore advance past a current
time even when it batches ties across classes. -/
theorem ae_multiclassForward_nextArrival_gt
    (rate : Class → ℝ) (hrate : ∀ i, 0 < rate i) :
    ∀ᵐ ω ∂multiclassForwardArrivalMeasure rate, ∀ i : Class, ∀ t : ℝ,
      t < arrivalTime (canonicalRenewalCount t (ω i)) (ω i) := by
  filter_upwards [ae_multiclassForwardArrivalPaths_nonexplosive_strict rate hrate]
    with ω hgood
  intro i t
  exact lt_arrivalTime_canonicalRenewalCount t (ω i)
    (exists_arrivalTime_gt_of_tendsto_atTop (ω i) (hgood i).1 t)

omit [Fintype Class] in
/-- The local arrival ledger is finite by construction, with its cardinality
equal to the concrete renewal count. -/
theorem multiclassForwardArrivalIndices_card
    (i : Class) (t : ℝ) (ω : Class → ℕ → ℝ) :
    (multiclassForwardArrivalIndices i t ω).card =
      canonicalRenewalCount t (ω i) := by
  simp [multiclassForwardArrivalIndices]

end

end AppliedModelingLib.Probability.PoissonProcess
