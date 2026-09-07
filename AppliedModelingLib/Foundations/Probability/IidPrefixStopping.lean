import AppliedModelingLib.Foundations.Probability.ExponentialInterarrival

/-!
# Restart after a total IID prefix stop

This module develops the finite-block restart law for a literal countable IID
stream.  A total discrete stopping index may inspect exactly the coordinates
through its reported index.  The finite block following that index, and hence
the complete shifted IID suffix, have the original product law.  The module
does not assert a continuous-time strong-Markov property or an independence
theorem from arbitrary stopped-prefix observables; those require an additional
state model.
-/

namespace AppliedModelingLib.Probability.IIDStream

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

variable {α : Type*} [MeasurableSpace α]

/-- The literal countable IID product law with one common coordinate law. -/
def measure (μ : Measure α) : Measure (ℕ → α) :=
  Measure.infinitePi (fun _ : ℕ => μ)

/-- The `n`th coordinate of an IID stream. -/
def coordinate (n : ℕ) : (ℕ → α) → α := fun ω => ω n

/-- Each IID coordinate is Borel measurable. -/
theorem measurable_coordinate (n : ℕ) : Measurable (coordinate (α := α) n) := by
  simpa [coordinate] using
    (measurable_pi_apply n : Measurable (fun ω : ℕ → α => ω n))

/-- Each IID coordinate has the designated marginal law. -/
theorem coordinate_hasLaw (μ : Measure α) [IsProbabilityMeasure μ] (n : ℕ) :
    HasLaw (coordinate (α := α) n) μ (measure μ) := by
  exact (@measurePreserving_eval_infinitePi ℕ (fun _ : ℕ => α)
    (fun _ => inferInstance) (fun _ : ℕ => μ) (fun _ => inferInstance) n).hasLaw

/-- Every IID coordinate is measure preserving onto its common marginal law. -/
theorem coordinate_measurePreserving (μ : Measure α) [IsProbabilityMeasure μ] (n : ℕ) :
    MeasurePreserving (coordinate (α := α) n) (measure μ) μ := by
  refine ⟨measurable_coordinate n, ?_⟩
  exact (coordinate_hasLaw μ n).map_eq

/-- An integrable reward remains integrable when evaluated at any IID coordinate. -/
theorem integrable_reward_coordinate (μ : Measure α) [IsProbabilityMeasure μ]
    (reward : α → ℝ) (hreward : Integrable reward μ) (n : ℕ) :
    Integrable (fun ω => reward (coordinate (α := α) n ω)) (measure μ) := by
  exact (coordinate_measurePreserving μ n).integrable_comp_of_integrable hreward

/-- The literal IID coordinates are mutually independent. -/
theorem iIndepFun_coordinate (μ : Measure α) [IsProbabilityMeasure μ] :
    iIndepFun (coordinate (α := α)) (measure μ) := by
  simpa [measure, coordinate] using
    (@ProbabilityTheory.iIndepFun_infinitePi ℕ (fun _ : ℕ => α)
      (fun _ => inferInstance) (fun _ : ℕ => α) (fun _ => inferInstance)
      (fun _ : ℕ => μ) (fun _ => inferInstance) (fun _ => id)
      (fun _ => measurable_id))

/-- The inspected finite prefix through `n`. -/
def streamPrefix (n : ℕ) : (ℕ → α) → (Finset.range (n + 1) → α) :=
  fun ω i => coordinate i ω

/-- The finite IID prefix is Borel measurable. -/
theorem measurable_streamPrefix (n : ℕ) : Measurable (streamPrefix (α := α) n) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_coordinate i

/-- A deterministic finite block of consecutive IID coordinates. -/
def block (start q : ℕ) : (ℕ → α) → Fin q → α :=
  fun ω i => coordinate (start + i) ω

/-- Every deterministic finite IID block is Borel measurable. -/
theorem measurable_block (start q : ℕ) : Measurable (block (α := α) start q) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_coordinate (start + i)

/-- The coordinates in a deterministic finite IID block are independent. -/
theorem iIndepFun_block (μ : Measure α) [IsProbabilityMeasure μ]
    (start q : ℕ) :
    iIndepFun (fun (i : Fin q) ω => block (α := α) start q ω i) (measure μ) := by
  simpa [block] using
    (ProbabilityTheory.iIndepFun.precomp (g := fun i : Fin q => start + i)
      (by
        intro a b hab
        exact Fin.ext (Nat.add_left_cancel hab))
      (iIndepFun_coordinate μ))

/-- Pairing two corresponding independent finite coordinate families preserves independence. -/
theorem iIndepFun_pair_prod
    {ι Ω₁ Ω₂ β γ : Type*}
    [Fintype ι]
    [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    [MeasurableSpace β] [MeasurableSpace γ]
    {μ : Measure Ω₁} {ν : Measure Ω₂}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : ι → Ω₁ → β} {Y : ι → Ω₂ → γ}
    (hX : iIndepFun X μ) (hY : iIndepFun Y ν)
    (mX : ∀ i, Measurable (X i)) (mY : ∀ i, Measurable (Y i)) :
    iIndepFun (fun i z => (X i z.1, Y i z.2)) (μ.prod ν) := by
  classical
  let XV : Ω₁ → (ι → β) := fun ω i => X i ω
  let YV : Ω₂ → (ι → γ) := fun ω i => Y i ω
  have mXV : Measurable XV := measurable_pi_lambda _ mX
  have mYV : Measurable YV := measurable_pi_lambda _ mY
  have hmapX : μ.map XV = Measure.pi (fun i => μ.map (X i)) :=
    (iIndepFun_iff_map_fun_eq_pi_map
      (fun i => (mX i).aemeasurable)).mp hX
  have hmapY : ν.map YV = Measure.pi (fun i => ν.map (Y i)) :=
    (iIndepFun_iff_map_fun_eq_pi_map
      (fun i => (mY i).aemeasurable)).mp hY
  apply (iIndepFun_iff_map_fun_eq_pi_map
    (fun i => ((mX i).comp measurable_fst).prodMk
      ((mY i).comp measurable_snd) |>.aemeasurable)).mpr
  let e := MeasurableEquiv.arrowProdEquivProdArrow β γ ι
  calc
    (μ.prod ν).map (fun z i => (X i z.1, Y i z.2)) =
        (μ.prod ν).map (e.symm ∘ Prod.map XV YV) := by
      congr 1
    _ = ((μ.prod ν).map (Prod.map XV YV)).map e.symm := by
      exact (Measure.map_map e.symm.measurable
        (mXV.comp measurable_fst |>.prodMk
          (mYV.comp measurable_snd))).symm
    _ = ((μ.map XV).prod (ν.map YV)).map e.symm := by
      rw [Measure.map_prod_map μ ν mXV mYV]
    _ = ((Measure.pi (fun i => μ.map (X i))).prod
          (Measure.pi (fun i => ν.map (Y i)))).map e.symm := by
      rw [hmapX, hmapY]
    _ = Measure.pi (fun i => (μ.map (X i)).prod (ν.map (Y i))) := by
      exact (measurePreserving_arrowProdEquivProdArrow β γ ι
        (fun i => μ.map (X i)) (fun i => ν.map (Y i))).symm.map_eq
    _ = Measure.pi (fun i =>
          (μ.prod ν).map (fun z => (X i z.1, Y i z.2))) := by
      congr 1
      funext i
      simpa [Prod.map] using Measure.map_prod_map μ ν (mX i) (mY i)

/-- Zip two IID streams into their coordinatewise paired stream. -/
def zip {β : Type*} (ω : (ℕ → α) × (ℕ → β)) : ℕ → α × β :=
  fun n => (ω.1 n, ω.2 n)

/-- The coordinatewise zip of two IID streams is Borel measurable. -/
theorem measurable_zip {β : Type*} [MeasurableSpace β] :
    Measurable (zip (α := α) (β := β)) := by
  apply measurable_pi_lambda
  intro n
  exact ((measurable_pi_apply n).comp measurable_fst).prodMk
    ((measurable_pi_apply n).comp measurable_snd)

/-- Two independent IID streams zip to an IID stream of paired coordinates. -/
theorem zip_hasLaw
    {β : Type*} [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    HasLaw (zip (α := α) (β := β))
      (measure (μ.prod ν)) ((measure μ).prod (measure ν)) := by
  let source : Measure ((ℕ → α) × (ℕ → β)) :=
    (measure μ).prod (measure ν)
  letI : IsProbabilityMeasure (measure μ) := by
    dsimp [measure]
    infer_instance
  letI : IsProbabilityMeasure (measure ν) := by
    dsimp [measure]
    infer_instance
  letI : IsProbabilityMeasure source := by
    dsimp [source, measure]
    infer_instance
  refine ⟨measurable_zip.aemeasurable, ?_⟩
  apply Measure.eq_infinitePi
  intro s t ht
  let pairVector : ((ℕ → α) × (ℕ → β)) → s → α × β :=
    fun ω i => (ω.1 i, ω.2 i)
  have hpairVector_meas : Measurable pairVector := by
    apply measurable_pi_lambda
    intro i
    exact ((measurable_pi_apply (i : ℕ)).comp measurable_fst).prodMk
      ((measurable_pi_apply (i : ℕ)).comp measurable_snd)
  have hX : iIndepFun (fun i : s => coordinate (α := α) i) (measure μ) :=
    (iIndepFun_coordinate μ).precomp (g := Subtype.val) Subtype.val_injective
  have hY : iIndepFun (fun i : s => coordinate (α := β) i) (measure ν) :=
    (iIndepFun_coordinate ν).precomp (g := Subtype.val) Subtype.val_injective
  have hpair : iIndepFun
      (fun (i : s) (ω : (ℕ → α) × (ℕ → β)) =>
        (coordinate (α := α) i ω.1, coordinate (α := β) i ω.2)) source := by
    exact iIndepFun_pair_prod hX hY
      (fun i => measurable_coordinate (α := α) i)
      (fun i => measurable_coordinate (α := β) i)
  have hpair_law : source.map pairVector =
      Measure.pi (fun _ : s => μ.prod ν) := by
    calc
      source.map pairVector = Measure.pi (fun i : s => source.map
          (fun ω : (ℕ → α) × (ℕ → β) =>
            (coordinate (α := α) i ω.1, coordinate (α := β) i ω.2))) := by
        simpa [source, pairVector] using
          (iIndepFun_iff_map_fun_eq_pi_map
            (fun (i : s) => ((measurable_coordinate (α := α) i).comp measurable_fst).prodMk
              ((measurable_coordinate (α := β) i).comp measurable_snd) |>.aemeasurable)).mp
            hpair
      _ = Measure.pi (fun _ : s => μ.prod ν) := by
        congr 1
        funext i
        calc
          source.map
              (fun ω : (ℕ → α) × (ℕ → β) =>
                (coordinate (α := α) i ω.1, coordinate (α := β) i ω.2)) =
              ((measure μ).map (coordinate (α := α) i)).prod
                ((measure ν).map (coordinate (α := β) i)) := by
            symm
            simpa [source, coordinate, Prod.map] using
              Measure.map_prod_map (measure μ) (measure ν)
                (measurable_coordinate (α := α) i)
                (measurable_coordinate (α := β) i)
          _ = μ.prod ν := by
            rw [(coordinate_hasLaw μ i).map_eq, (coordinate_hasLaw ν i).map_eq]
  have hpreimage :
      zip (α := α) (β := β) ⁻¹' Set.pi s t =
        pairVector ⁻¹' Set.univ.pi (fun i : s => t i) := by
    ext ω
    simp [zip, pairVector]
  calc
    source.map (zip (α := α) (β := β)) (Set.pi s t) =
        source (zip (α := α) (β := β) ⁻¹' Set.pi s t) :=
      Measure.map_apply measurable_zip
        (MeasurableSet.pi s.countable_toSet fun i _ => ht i)
    _ = source (pairVector ⁻¹' Set.univ.pi (fun i : s => t i)) := by
      rw [hpreimage]
    _ = source.map pairVector (Set.univ.pi (fun i : s => t i)) :=
      (Measure.map_apply hpairVector_meas (MeasurableSet.univ_pi fun i => ht i)).symm
    _ = Measure.pi (fun _ : s => μ.prod ν) (Set.univ.pi (fun i : s => t i)) := by
      rw [hpair_law]
    _ = ∏ i ∈ s, (μ.prod ν) (t i) := by
      rw [Measure.pi_pi]
      exact Finset.prod_coe_sort (s := s) (fun i => (μ.prod ν) (t i))

/-- A deterministic finite IID block has the product of its coordinate laws. -/
theorem block_hasLaw (μ : Measure α) [IsProbabilityMeasure μ] (start q : ℕ) :
    HasLaw (block (α := α) start q) (Measure.pi (fun _ : Fin q => μ))
      (measure μ) := by
  letI : IsProbabilityMeasure (measure μ) := by
    dsimp [measure]
    infer_instance
  refine ⟨(measurable_block start q).aemeasurable, ?_⟩
  have hmap :=
    (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
      (f := fun (i : Fin q) ω => block (α := α) start q ω i)
      (μ := measure μ)
      (fun i => (measurable_coordinate (α := α) (start + i)).aemeasurable)).mp
      (iIndepFun_block μ start q)
  calc
    (measure μ).map (block (α := α) start q) =
        Measure.pi (fun i : Fin q =>
          (measure μ).map (fun ω => block (α := α) start q ω i)) := by
      simpa only using hmap
    _ = Measure.pi (fun _ : Fin q => μ) := by
      congr 1
      funext i
      exact (coordinate_hasLaw μ (start + i)).map_eq

/-- The inspected prefix through `n` is independent of every finite block after it. -/
theorem indepFun_streamPrefix_block (μ : Measure α) [IsProbabilityMeasure μ]
    (n q : ℕ) :
    IndepFun (streamPrefix (α := α) n) (block (α := α) (n + 1) q) (measure μ) := by
  have hdisjoint : Disjoint (Finset.range (n + 1)) (Finset.Ico (n + 1) (n + 1 + q)) := by
    rw [Finset.disjoint_left]
    intro i hi hj
    have hil : i < n + 1 := Finset.mem_range.mp hi
    have hir : n + 1 ≤ i := (Finset.mem_Ico.mp hj).1
    omega
  have hraw := (iIndepFun_coordinate μ).indepFun_finset
    (Finset.range (n + 1)) (Finset.Ico (n + 1) (n + 1 + q)) hdisjoint
    (fun i => measurable_coordinate (α := α) i)
  let e : Fin q → (Finset.Ico (n + 1) (n + 1 + q)) := fun i =>
    ⟨n + 1 + i, Finset.mem_Ico.mpr ⟨Nat.le_add_right _ _, by omega⟩⟩
  let reindex : ((Finset.Ico (n + 1) (n + 1 + q)) → α) → Fin q → α :=
    fun g i => g (e i)
  have hreindex : Measurable reindex := by
    apply measurable_pi_lambda
    intro i
    exact measurable_pi_apply (e i)
  have hcomp := hraw.comp measurable_id hreindex
  simpa [streamPrefix, block, reindex, e, Function.comp_def] using hcomp

/-- Measurable rectangular events of a deterministic IID block factor coordinatewise. -/
theorem measure_block_mem_eq (μ : Measure α) [IsProbabilityMeasure μ]
    (start q : ℕ) (s : Fin q → Set α) (hs : ∀ i, MeasurableSet (s i)) :
    measure μ {ω | ∀ i, block (α := α) start q ω i ∈ s i} =
      ∏ i : Fin q, μ (s i) := by
  have hrect : {ω | ∀ i, block (α := α) start q ω i ∈ s i} =
      block (α := α) start q ⁻¹' Set.univ.pi s := by
    ext ω
    simp
  letI : ∀ i : Fin q, IsProbabilityMeasure μ := fun _ => inferInstance
  rw [hrect]
  calc
    measure μ (block (α := α) start q ⁻¹' Set.univ.pi s) =
        (measure μ).map (block (α := α) start q) (Set.univ.pi s) :=
      (Measure.map_apply (measurable_block start q) (MeasurableSet.univ_pi hs)).symm
    _ = Measure.pi (fun _ : Fin q => μ) (Set.univ.pi s) := by
      rw [(block_hasLaw μ start q).map_eq]
    _ = ∏ i : Fin q, μ (s i) := by
      rw [Measure.pi_pi]

/-- A total discrete stopping index observable from the prefix through its value. -/
structure PrefixStoppingIndex where
  toFun : (ℕ → α) → ℕ
  event_prefix_measurable : ∀ n,
    MeasurableSet[MeasurableSpace.comap (streamPrefix (α := α) n) inferInstance]
      {ω | toFun ω = n}

namespace PrefixStoppingIndex

instance : CoeFun (PrefixStoppingIndex (α := α))
    (fun _ => (ℕ → α) → ℕ) := ⟨PrefixStoppingIndex.toFun⟩

/-- The `n`th level event of a prefix stopping index. -/
def event (τ : PrefixStoppingIndex (α := α)) (n : ℕ) : Set (ℕ → α) :=
  {ω | τ ω = n}

/-- Every stopping-level event is Borel measurable. -/
theorem measurableSet_event (τ : PrefixStoppingIndex (α := α)) (n : ℕ) :
    MeasurableSet (τ.event n) := by
  change MeasurableSet {ω | τ ω = n}
  rcases τ.event_prefix_measurable n with ⟨u, hu, hpre⟩
  rw [← hpre]
  exact (measurable_streamPrefix n) hu

/-- Distinct stopping-level events are disjoint. -/
theorem event_pairwiseDisjoint (τ : PrefixStoppingIndex (α := α)) :
    Pairwise (Function.onFun Disjoint τ.event) := by
  intro n m hnm
  refine Set.disjoint_left.2 ?_
  intro ω hωn hωm
  change τ ω = n at hωn
  change τ ω = m at hωm
  exact hnm (hωn.symm.trans hωm)

/-- The total stopping-level events cover the IID carrier. -/
theorem iUnion_event_eq_univ (τ : PrefixStoppingIndex (α := α)) :
    ⋃ n, τ.event n = Set.univ := by
  ext ω
  simp [event]

/-- Restrict a longer literal IID prefix to an earlier prefix. -/
def prefixRestriction (m n : ℕ) (hmn : m ≤ n) :
    (Finset.range (n + 1) → α) → (Finset.range (m + 1) → α) :=
  fun x i => x ⟨i, Finset.mem_range.mpr
    (lt_of_lt_of_le (Finset.mem_range.mp i.2) (Nat.succ_le_succ hmn))⟩

/-- Prefix restriction is Borel measurable. -/
theorem measurable_prefixRestriction (m n : ℕ) (hmn : m ≤ n) :
    Measurable (prefixRestriction (α := α) m n hmn) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_pi_apply (⟨i, Finset.mem_range.mpr
    (lt_of_lt_of_le (Finset.mem_range.mp i.2) (Nat.succ_le_succ hmn))⟩ :
      Finset.range (n + 1))

/-- Restricting a longer inspected prefix recovers the earlier prefix. -/
theorem prefixRestriction_streamPrefix (m n : ℕ) (hmn : m ≤ n) :
    prefixRestriction (α := α) m n hmn ∘ streamPrefix n = streamPrefix m := by
  funext ω i
  change ω i = ω i
  rfl

/-- An event observable from an earlier prefix is also observable from every
longer prefix. -/
theorem event_prefix_measurable_mono (τ : PrefixStoppingIndex (α := α))
    {m n : ℕ} (hmn : m ≤ n) :
    MeasurableSet[MeasurableSpace.comap (streamPrefix (α := α) n) inferInstance]
      (τ.event m) := by
  rcases τ.event_prefix_measurable m with ⟨u, hu, hpre⟩
  refine ⟨(prefixRestriction (α := α) m n hmn) ⁻¹' u,
    hu.preimage (measurable_prefixRestriction (α := α) m n hmn), ?_⟩
  change streamPrefix n ⁻¹' (prefixRestriction (α := α) m n hmn ⁻¹' u) =
    {ω | τ ω = m}
  rw [← hpre]
  ext ω
  simp only [Set.mem_preimage]
  change (prefixRestriction (α := α) m n hmn ∘ streamPrefix n) ω ∈ u ↔
    streamPrefix m ω ∈ u
  rw [prefixRestriction_streamPrefix]

/-- The event that a prefix stopping index has not stopped before `n`. -/
def continuationEvent (τ : PrefixStoppingIndex (α := α)) (n : ℕ) :
    Set (ℕ → α) := {ω | n ≤ τ ω}

/-- Not stopping before `n + 1` is measurable from the prefix through `n`.
This is the predictable-event form needed to factor the next IID coordinate
from a stopped history. -/
theorem continuationEvent_succ_prefix_measurable
    (τ : PrefixStoppingIndex (α := α)) (n : ℕ) :
    MeasurableSet[MeasurableSpace.comap (streamPrefix (α := α) n) inferInstance]
      (τ.continuationEvent (n + 1)) := by
  let bad : Set (ℕ → α) := ⋃ m ∈ Finset.range (n + 1), τ.event m
  have hbad : MeasurableSet[
      MeasurableSpace.comap (streamPrefix (α := α) n) inferInstance] bad := by
    exact Finset.measurableSet_biUnion (Finset.range (n + 1))
      (fun m hm => τ.event_prefix_measurable_mono
        (Nat.le_of_lt_succ (Finset.mem_range.mp hm)))
  have heq : τ.continuationEvent (n + 1) = badᶜ := by
    ext ω
    simp only [continuationEvent, Set.mem_setOf_eq, Set.mem_compl_iff, bad,
      Set.mem_iUnion, event]
    constructor
    · intro h hbadMem
      rcases hbadMem with ⟨m, hm, hτ⟩
      have hnm : n + 1 ≤ m := by simpa [hτ] using h
      exact (Nat.not_lt_of_ge hnm) (Finset.mem_range.mp hm)
    · intro h
      by_contra hnot
      have hlt : τ ω < n + 1 := Nat.lt_of_not_ge hnot
      exact h ⟨τ ω, Finset.mem_range.mpr hlt, rfl⟩
  rw [heq]
  exact hbad.compl

/-- The one-step continuation event is Borel measurable on the IID carrier. -/
theorem measurableSet_continuationEvent_succ
    (τ : PrefixStoppingIndex (α := α)) (n : ℕ) :
    MeasurableSet (τ.continuationEvent (n + 1)) := by
  rcases τ.continuationEvent_succ_prefix_measurable n with ⟨u, hu, hpre⟩
  rw [← hpre]
  exact (measurable_streamPrefix n) hu

/-- Before the first coordinate, every prefix rule is still continuing. -/
theorem continuationEvent_zero (τ : PrefixStoppingIndex (α := α)) :
    τ.continuationEvent 0 = Set.univ := by
  ext ω
  simp [continuationEvent]

/-- Every continuation event is Borel measurable. -/
theorem measurableSet_continuationEvent
    (τ : PrefixStoppingIndex (α := α)) (n : ℕ) :
    MeasurableSet (τ.continuationEvent n) := by
  cases n with
  | zero => rw [τ.continuationEvent_zero]; exact MeasurableSet.univ
  | succ n => exact τ.measurableSet_continuationEvent_succ n

/-- A reward at the next IID coordinate factors from the event that the
stopping rule has not already stopped.  This is the one-step predictable
factorization from which stopped renewal-reward identities are obtained by
finite summation and an integrable limiting argument. -/
theorem integral_continuationEvent_succ_indicator_mul_coordinate
    (μ : Measure α) [IsProbabilityMeasure μ]
    (τ : PrefixStoppingIndex (α := α)) (n : ℕ)
    (reward : α → ℝ) (hreward : Integrable reward μ) :
    ∫ ω, (τ.continuationEvent (n + 1)).indicator (fun _ => (1 : ℝ)) ω *
        reward (coordinate (n + 1) ω) ∂measure μ =
      (measure μ).real (τ.continuationEvent (n + 1)) * ∫ x, reward x ∂μ := by
  rcases τ.continuationEvent_succ_prefix_measurable n with ⟨u, hu, hpre⟩
  let F : (Finset.range (n + 1) → α) → ℝ :=
    u.indicator (fun _ => (1 : ℝ))
  let G : (Fin 1 → α) → ℝ := fun block => reward (block 0)
  have hF : Measurable F := by
    exact measurable_const.indicator hu
  have hG : AEStronglyMeasurable G
      ((measure μ).map (block (α := α) (n + 1) 1)) := by
    rw [(block_hasLaw μ (n + 1) 1).map_eq]
    rw [← Measure.infinitePi_eq_pi]
    exact hreward.aestronglyMeasurable.comp_quasiMeasurePreserving
      (measurePreserving_eval_infinitePi (fun _ : Fin 1 => μ) 0).quasiMeasurePreserving
  have hindep := indepFun_streamPrefix_block μ n 1
  have hfactor := hindep.integral_comp_mul_comp
    (measurable_streamPrefix n).aemeasurable
    (measurable_block (α := α) (n + 1) 1).aemeasurable
    hF.aestronglyMeasurable hG
  have hleft :
      (fun ω : ℕ → α => F (streamPrefix n ω) *
          G (block (α := α) (n + 1) 1 ω)) =
        fun ω => (τ.continuationEvent (n + 1)).indicator (fun _ => (1 : ℝ)) ω *
          reward (coordinate (n + 1) ω) := by
    funext ω
    have hmem : streamPrefix n ω ∈ u ↔ ω ∈ τ.continuationEvent (n + 1) := by
      change ω ∈ streamPrefix n ⁻¹' u ↔ ω ∈ τ.continuationEvent (n + 1)
      rw [hpre]
    by_cases h : streamPrefix n ω ∈ u
    · have hcont : ω ∈ τ.continuationEvent (n + 1) := hmem.mp h
      simp [F, G, block, coordinate, Set.indicator, h, hcont]
    · have h' : ω ∉ τ.continuationEvent (n + 1) := by
        intro hcont
        exact h (hmem.mpr hcont)
      simp [F, G, block, coordinate, Set.indicator, h, h']
  have hprefix :
      (∫ ω : ℕ → α, F (streamPrefix n ω) ∂measure μ) =
        (measure μ).real (τ.continuationEvent (n + 1)) := by
    calc
      (∫ ω : ℕ → α, F (streamPrefix n ω) ∂measure μ) =
          ∫ ω : ℕ → α,
            (τ.continuationEvent (n + 1)).indicator (fun _ => (1 : ℝ)) ω
              ∂measure μ := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
            change u.indicator (fun _ => (1 : ℝ)) (streamPrefix n ω) = _
            have hmem : streamPrefix n ω ∈ u ↔
                ω ∈ τ.continuationEvent (n + 1) := by
              change ω ∈ streamPrefix n ⁻¹' u ↔ ω ∈ τ.continuationEvent (n + 1)
              rw [hpre]
            by_cases h : streamPrefix n ω ∈ u
            · have hcont : ω ∈ τ.continuationEvent (n + 1) := by
                exact hmem.mp h
              simp [Set.indicator, h, hcont]
            · have h' : ω ∉ τ.continuationEvent (n + 1) := by
                intro hcont
                exact h (hmem.mpr hcont)
              simp [Set.indicator, h, h']
      _ = (measure μ).real (τ.continuationEvent (n + 1)) := by
        rw [MeasureTheory.integral_indicator
          (τ.measurableSet_continuationEvent_succ n),
          MeasureTheory.setIntegral_const, smul_eq_mul, mul_one]
  have hrewardIntegral :
      (∫ ω : ℕ → α, G (block (α := α) (n + 1) 1 ω) ∂measure μ) =
        ∫ x, reward x ∂μ := by
    simpa [G, block, coordinate] using
      (coordinate_hasLaw μ (n + 1)).integral_comp hreward.aestronglyMeasurable
  calc
    ∫ ω, (τ.continuationEvent (n + 1)).indicator (fun _ => (1 : ℝ)) ω *
        reward (coordinate (n + 1) ω) ∂measure μ =
        ∫ ω : ℕ → α, F (streamPrefix n ω) *
          G (block (α := α) (n + 1) 1 ω) ∂measure μ := by
          rw [hleft]
    _ = (∫ ω : ℕ → α, F (streamPrefix n ω) ∂measure μ) *
          ∫ ω : ℕ → α, G (block (α := α) (n + 1) 1 ω) ∂measure μ := by
          simpa only [Function.comp_apply] using hfactor
    _ = (measure μ).real (τ.continuationEvent (n + 1)) * ∫ x, reward x ∂μ := by
          rw [hprefix, hrewardIntegral]

/-- Every predictable coordinate reward in a stopped IID prefix is integrable
whenever the common-coordinate reward is integrable. -/
theorem integrable_continuationEvent_indicator_mul_coordinate
    (μ : Measure α) [IsProbabilityMeasure μ]
    (τ : PrefixStoppingIndex (α := α)) (n : ℕ)
    (reward : α → ℝ) (hreward : Integrable reward μ) :
    Integrable (fun ω =>
      (τ.continuationEvent n).indicator (fun _ => (1 : ℝ)) ω *
        reward (coordinate n ω)) (measure μ) := by
  have hcoord := integrable_reward_coordinate μ reward hreward n
  have hindicator := hcoord.indicator (τ.measurableSet_continuationEvent n)
  have heq :
      (τ.continuationEvent n).indicator
        (fun ω => reward (coordinate n ω)) =
      fun ω => (τ.continuationEvent n).indicator (fun _ => (1 : ℝ)) ω *
        reward (coordinate n ω) := by
    funext ω
    by_cases h : ω ∈ τ.continuationEvent n <;>
      simp [Set.indicator, h]
  rw [← heq]
  exact hindicator

/-- The reward accrued at inspected coordinates up to a deterministic cap.
On each path this is exactly the reward prefix through the smaller of the
stopping index and the cap. -/
def truncatedStoppedReward (τ : PrefixStoppingIndex (α := α))
    (reward : α → ℝ) (cap : ℕ) : (ℕ → α) → ℝ :=
  fun ω => ∑ n ∈ Finset.range (cap + 1),
    if n ≤ τ ω then reward (coordinate n ω) else 0

/-- The finite predictable-reward identity for a total IID prefix stopping
index.  It is a proved capped form of Wald's calculation; an unbounded
renewal-reward theorem additionally needs a justified limiting argument. -/
theorem integral_truncatedStoppedReward
    (μ : Measure α) [IsProbabilityMeasure μ]
    (τ : PrefixStoppingIndex (α := α))
    (reward : α → ℝ) (hreward : Measurable reward)
    (hintegrable : Integrable reward μ) (cap : ℕ) :
    ∫ ω, truncatedStoppedReward τ reward cap ω ∂measure μ =
      (∑ n ∈ Finset.range (cap + 1),
        (measure μ).real (τ.continuationEvent n)) * ∫ x, reward x ∂μ := by
  unfold truncatedStoppedReward
  rw [MeasureTheory.integral_finset_sum]
  · have htermIntegral (n : ℕ) :
        ∫ ω, (if n ≤ τ ω then reward (coordinate n ω) else 0) ∂measure μ =
          (measure μ).real (τ.continuationEvent n) * ∫ x, reward x ∂μ := by
      letI : IsProbabilityMeasure (measure μ) := by
        dsimp [measure]
        infer_instance
      cases n with
      | zero =>
          have hcoord := (coordinate_hasLaw μ 0).integral_comp
            hreward.aestronglyMeasurable
          rw [τ.continuationEvent_zero]
          calc
            ∫ ω, (if 0 ≤ τ ω then reward (coordinate 0 ω) else 0) ∂measure μ =
                ∫ ω, reward (coordinate 0 ω) ∂measure μ := by simp
            _ = ∫ x, reward x ∂μ := hcoord
            _ = (measure μ).real Set.univ * ∫ x, reward x ∂μ := by
              rw [MeasureTheory.measureReal_def, measure_univ]
              simp
      | succ n =>
          have hterm := integral_continuationEvent_succ_indicator_mul_coordinate
            (α := α) μ τ n reward hintegrable
          simpa [continuationEvent, Set.indicator] using hterm
    simp_rw [htermIntegral]
    rw [Finset.sum_mul]
  · intro n _
    have hterm := integrable_continuationEvent_indicator_mul_coordinate
      (α := α) μ τ n reward hintegrable
    simpa [continuationEvent, Set.indicator] using hterm

/-- The capped stopped reward is the literal finite reward prefix through
`min τ cap`; this is a pathwise equality, with no expectation assumption. -/
theorem truncatedStoppedReward_eq_sum_range_min
    (τ : PrefixStoppingIndex (α := α)) (reward : α → ℝ)
    (cap : ℕ) (ω : ℕ → α) :
    truncatedStoppedReward τ reward cap ω =
      ∑ n ∈ Finset.range (min (τ ω) cap + 1), reward (coordinate n ω) := by
  have hfilter : (Finset.range (cap + 1)).filter (fun n => n ≤ τ ω) =
      Finset.range (min (τ ω) cap + 1) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [truncatedStoppedReward, ← Finset.sum_filter, hfilter]

/-- The first `q` uninspected IID coordinates after a total prefix stop. -/
def postBlock (τ : PrefixStoppingIndex (α := α)) (q : ℕ) :
    (ℕ → α) → Fin q → α :=
  fun ω i => coordinate (τ ω + 1 + i) ω

private theorem measurable_postBlock_coordinate
    (τ : PrefixStoppingIndex (α := α)) (q : ℕ) (i : Fin q) :
    Measurable (fun ω => postBlock τ q ω i) := by
  let h : ∀ ω : ℕ → α, ∃ n, τ ω = n := fun ω => ⟨τ ω, rfl⟩
  have hmeas : Measurable (fun ω => coordinate (Nat.find (h ω) + 1 + i) ω) :=
    Measurable.find
      (fun n => measurable_coordinate (α := α) (n + 1 + i))
      (fun n => τ.measurableSet_event n)
      h
  convert hmeas using 1
  funext ω
  have hfind : Nat.find (h ω) = τ ω := (Nat.find_spec (h ω)).symm
  simp [postBlock, hfind]

/-- The finite IID block after a total prefix stop is Borel measurable. -/
theorem measurable_postBlock (τ : PrefixStoppingIndex (α := α)) (q : ℕ) :
    Measurable (postBlock τ q) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_postBlock_coordinate τ q i

/-- At a fixed stopping level, the uninspected IID block factors from the prefix. -/
theorem event_inter_block_measure_eq_mul
    (μ : Measure α) [IsProbabilityMeasure μ]
    (τ : PrefixStoppingIndex (α := α)) (n q : ℕ)
    (s : Fin q → Set α) (hs : ∀ i, MeasurableSet (s i)) :
    measure μ (τ.event n ∩ {ω | ∀ i, block (α := α) (n + 1) q ω i ∈ s i}) =
      measure μ (τ.event n) * ∏ i : Fin q, μ (s i) := by
  have hindep := indepFun_streamPrefix_block μ n q
  have hrect : {ω | ∀ i, block (α := α) (n + 1) q ω i ∈ s i} =
      block (α := α) (n + 1) q ⁻¹' Set.univ.pi s := by
    ext ω
    simp
  have hright : MeasurableSet[
      MeasurableSpace.comap (block (α := α) (n + 1) q) inferInstance]
      {ω | ∀ i, block (α := α) (n + 1) q ω i ∈ s i} := by
    rw [hrect]
    exact MeasurableSpace.measurableSet_comap.2
      ⟨Set.univ.pi s, MeasurableSet.univ_pi hs, rfl⟩
  have hfactor := hindep.meas_inter (τ.event_prefix_measurable n) hright
  calc
    measure μ (τ.event n ∩ {ω | ∀ i, block (α := α) (n + 1) q ω i ∈ s i}) =
        measure μ (τ.event n) *
          measure μ {ω | ∀ i, block (α := α) (n + 1) q ω i ∈ s i} := hfactor
    _ = measure μ (τ.event n) * ∏ i : Fin q, μ (s i) := by
      rw [measure_block_mem_eq μ (n + 1) q s hs]

/-- Every measurable rectangular event in a finite post-stop block has the IID law. -/
theorem measure_postBlock_mem_eq
    (μ : Measure α) [IsProbabilityMeasure μ]
    (τ : PrefixStoppingIndex (α := α)) (q : ℕ)
    (s : Fin q → Set α) (hs : ∀ i, MeasurableSet (s i)) :
    measure μ {ω | ∀ i, postBlock τ q ω i ∈ s i} =
      ∏ i : Fin q, μ (s i) := by
  let ν : Measure (ℕ → α) := measure μ
  letI : IsProbabilityMeasure ν := by
    dsimp [ν, measure]
    infer_instance
  let pieces : ℕ → Set (ℕ → α) := fun n =>
    τ.event n ∩ {ω | ∀ i, block (α := α) (n + 1) q ω i ∈ s i}
  have hblock_meas : ∀ n, MeasurableSet
      {ω | ∀ i, block (α := α) (n + 1) q ω i ∈ s i} := by
    intro n
    have hrect : {ω | ∀ i, block (α := α) (n + 1) q ω i ∈ s i} =
        block (α := α) (n + 1) q ⁻¹' Set.univ.pi s := by
      ext ω
      simp
    rw [hrect]
    exact (measurable_block (n + 1) q) (MeasurableSet.univ_pi hs)
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
      ⋃ n, pieces n = {ω | ∀ i, postBlock τ q ω i ∈ s i} := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_inter_iff, pieces, event, Set.mem_setOf_eq]
    constructor
    · rintro ⟨n, hτ, hblock⟩
      simpa [postBlock, hτ] using hblock
    · intro hmem
      refine ⟨τ ω, rfl, ?_⟩
      simpa [postBlock] using hmem
  have hmeasure_pieces :
      ν {ω | ∀ i, postBlock τ q ω i ∈ s i} =
        ∑' n, ν (pieces n) := by
    rw [← hpieces_union]
    exact measure_iUnion hpieces_disjoint hpieces_meas
  have hsum_event : ∑' n, ν (τ.event n) = 1 := by
    calc
      ∑' n, ν (τ.event n) = ν (⋃ n, τ.event n) :=
        (measure_iUnion τ.event_pairwiseDisjoint τ.measurableSet_event).symm
      _ = ν Set.univ := congrArg ν τ.iUnion_event_eq_univ
      _ = 1 := measure_univ
  have hpieces_factor :
      (∑' n, ν (pieces n)) =
        ∑' n, ν (τ.event n) * ∏ i : Fin q, μ (s i) := by
    apply tsum_congr
    intro n
    exact τ.event_inter_block_measure_eq_mul μ n q s hs
  change ν {ω | ∀ i, postBlock τ q ω i ∈ s i} = _
  calc
    ν {ω | ∀ i, postBlock τ q ω i ∈ s i} =
        ∑' n, ν (pieces n) := hmeasure_pieces
    _ = ∑' n, ν (τ.event n) * ∏ i : Fin q, μ (s i) := hpieces_factor
    _ = (∑' n, ν (τ.event n)) * ∏ i : Fin q, μ (s i) := by
      exact ENNReal.tsum_mul_right
    _ = ∏ i : Fin q, μ (s i) := by
      simp [hsum_event]

/-- The finite IID block after a total prefix stop has its original product law. -/
theorem postBlock_hasLaw
    (μ : Measure α) [IsProbabilityMeasure μ]
    (τ : PrefixStoppingIndex (α := α)) (q : ℕ) :
    HasLaw (postBlock τ q) (Measure.pi (fun _ : Fin q => μ)) (measure μ) := by
  letI : IsProbabilityMeasure (measure μ) := by
    dsimp [measure]
    infer_instance
  refine ⟨(measurable_postBlock τ q).aemeasurable, ?_⟩
  apply (Measure.pi_eq (μ := fun _ : Fin q => μ)
    (μ' := (measure μ).map (postBlock τ q)) ?_).symm
  intro s hs
  have hrect : postBlock τ q ⁻¹' Set.univ.pi s =
      {ω | ∀ i, postBlock τ q ω i ∈ s i} := by
    ext ω
    simp
  calc
    (measure μ).map (postBlock τ q) (Set.univ.pi s) =
        measure μ (postBlock τ q ⁻¹' Set.univ.pi s) :=
      Measure.map_apply (measurable_postBlock τ q) (MeasurableSet.univ_pi hs)
    _ = measure μ {ω | ∀ i, postBlock τ q ω i ∈ s i} := congrArg _ hrect
    _ = ∏ i : Fin q, μ (s i) :=
      measure_postBlock_mem_eq μ τ q s hs

/-- The complete uninspected IID suffix following a total prefix stop.  Its
coordinate `n` is the `(τ + 1 + n)`th coordinate of the original stream. -/
def postTail (τ : PrefixStoppingIndex (α := α)) :
    (ℕ → α) → ℕ → α :=
  fun ω n => coordinate (τ ω + 1 + n) ω

/-- The complete uninspected suffix is Borel measurable. -/
theorem measurable_postTail (τ : PrefixStoppingIndex (α := α)) :
    Measurable (postTail τ) := by
  apply measurable_pi_lambda
  intro n
  simpa [postTail, postBlock] using
    (measurable_postBlock_coordinate τ (n + 1) (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)))

/-- The first `q` coordinates of the uninspected suffix are the corresponding
finite post-stop block. -/
theorem postTail_restrict_eq_postBlock
    (τ : PrefixStoppingIndex (α := α)) (q : ℕ) (ω : ℕ → α) :
    (fun i : Fin q => postTail τ ω i) = postBlock τ q ω := by
  funext i
  rfl

/-- A total prefix stop leaves a whole IID suffix with the original product
law.  This is stronger than the finite-block statement: it is the restart law
needed to iterate a cycle construction. -/
theorem postTail_hasLaw
    (μ : Measure α) [IsProbabilityMeasure μ]
    (τ : PrefixStoppingIndex (α := α)) :
    HasLaw (postTail τ) (measure μ) (measure μ) := by
  letI : IsProbabilityMeasure (measure μ) := by
    dsimp [measure]
    infer_instance
  refine ⟨(measurable_postTail τ).aemeasurable, ?_⟩
  apply Measure.eq_infinitePi
  intro s t ht
  classical
  by_cases hs : s.Nonempty
  · let q : ℕ := s.max' hs + 1
    let u : Fin q → Set α := fun i =>
      if (i : ℕ) ∈ s then t i else Set.univ
    have hq : ∀ i, i ∈ s → i < q := by
      intro i hi
      dsimp [q]
      exact Nat.lt_succ_of_le (Finset.le_max' s i hi)
    have hu : ∀ i, MeasurableSet (u i) := by
      intro i
      by_cases hi : (i : ℕ) ∈ s
      · simpa [u, hi] using ht i
      · simp [u, hi]
    have hevent :
        postTail τ ⁻¹' Set.pi s t =
          postBlock τ q ⁻¹' Set.univ.pi u := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_pi]
      constructor
      · intro h i
        by_cases hi : (i : ℕ) ∈ s
        · have hmem := h i hi
          simpa [postTail, postBlock, u, hi] using hmem
        · simp [u, hi]
      · intro h i hi
        let ii : Fin q := ⟨i, hq i hi⟩
        have hmem : postBlock τ q ω ii ∈ u ii := h ii (by simp)
        change coordinate (τ ω + 1 + i) ω ∈ t i
        change coordinate (τ ω + 1 + i) ω ∈
          (if (ii : ℕ) ∈ s then t ii else Set.univ) at hmem
        have hii : (ii : ℕ) ∈ s := by simpa [ii] using hi
        have hmem' : coordinate (τ ω + 1 + i) ω ∈ t (ii : ℕ) := by
          simpa [hii] using hmem
        simpa [ii] using hmem'
    calc
      (measure μ).map (postTail τ) (Set.pi s t) =
          measure μ (postTail τ ⁻¹' Set.pi s t) :=
        Measure.map_apply (measurable_postTail τ)
          (MeasurableSet.pi s.countable_toSet (fun i _ => ht i))
      _ = measure μ (postBlock τ q ⁻¹' Set.univ.pi u) := by rw [hevent]
      _ = (measure μ).map (postBlock τ q) (Set.univ.pi u) :=
        (Measure.map_apply (measurable_postBlock τ q)
          (MeasurableSet.univ_pi hu)).symm
      _ = Measure.pi (fun _ : Fin q => μ) (Set.univ.pi u) := by
        rw [(postBlock_hasLaw μ τ q).map_eq]
      _ = ∏ i : Fin q, μ (u i) := by
        rw [Measure.pi_pi]
      _ = ∏ i ∈ s, μ (t i) := by
        calc
          ∏ i : Fin q, μ (u i) =
              ∏ i : Fin q, (if (i : ℕ) ∈ s then μ (t i) else 1) := by
            apply Finset.prod_congr rfl
            intro i _
            dsimp [u]
            split_ifs <;> simp
          _ = ∏ i ∈ Finset.range q, if i ∈ s then μ (t i) else 1 :=
            (Finset.prod_range (fun i : ℕ =>
              if i ∈ s then μ (t i) else 1)).symm
        rw [Finset.prod_ite_mem]
        congr 2
        apply Finset.inter_eq_right.mpr
        intro i hi
        exact Finset.mem_range.mpr (hq i hi)
  · have hs_empty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    rw [hs_empty]
    simpa only [Finset.coe_empty, Set.empty_pi, Finset.prod_empty,
      Set.preimage_univ, measure_univ] using
      (Measure.map_apply (μ := measure μ) (measurable_postTail τ)
        (MeasurableSet.univ))

end PrefixStoppingIndex

/-- A measurable countable path has the canonical iid product law whenever
each nonempty finite initial prefix has the corresponding finite product law.
This packages the cylinder-set extension used to promote finite-dimensional
iid constructions to an actual iid stream. -/
theorem hasLaw_iidPath_of_hasLaw_positive_prefixes
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (path : Ω → ℕ → α) (hpath : Measurable path)
    (hprefix : ∀ q : ℕ, 0 < q →
      HasLaw (fun (omega : Ω) (i : Fin q) => path omega i)
        (Measure.pi (fun _ : Fin q => μ)) P) :
    HasLaw path (measure μ) P := by
  letI : IsProbabilityMeasure (measure μ) := by
    dsimp [measure]
    infer_instance
  refine ⟨hpath.aemeasurable, ?_⟩
  apply Measure.eq_infinitePi
  intro s t ht
  classical
  by_cases hs : s.Nonempty
  · let q : ℕ := s.max' hs + 1
    let u : Fin q → Set α := fun i =>
      if (i : ℕ) ∈ s then t i else Set.univ
    have hq : ∀ i, i ∈ s → i < q := by
      intro i hi
      dsimp [q]
      exact Nat.lt_succ_of_le (Finset.le_max' s i hi)
    have hq_pos : 0 < q := by
      dsimp [q]
      omega
    have hu : ∀ i, MeasurableSet (u i) := by
      intro i
      by_cases hi : (i : ℕ) ∈ s
      · simpa [u, hi] using ht i
      · simp [u, hi]
    have hpreimage :
        path ⁻¹' Set.pi s t =
          (fun (omega : Ω) (i : Fin q) => path omega i) ⁻¹' Set.univ.pi u := by
      ext omega
      simp only [Set.mem_preimage, Set.mem_pi]
      constructor
      · intro h i
        by_cases hi : (i : ℕ) ∈ s
        · have hmem := h i hi
          simpa [u, hi] using hmem
        · simp [u, hi]
      · intro h i hi
        let ii : Fin q := ⟨i, hq i hi⟩
        have hmem : path omega ii ∈ u ii := h ii (by simp)
        change path omega i ∈ t i
        change path omega i ∈ (if (ii : ℕ) ∈ s then t ii else Set.univ) at hmem
        have hii : (ii : ℕ) ∈ s := by simpa [ii] using hi
        have hmem' : path omega i ∈ t (ii : ℕ) := by
          simpa [hii, ii] using hmem
        simpa [ii] using hmem'
    have hprefixMeas : Measurable (fun (omega : Ω) (i : Fin q) => path omega i) := by
      apply measurable_pi_lambda
      intro i
      exact (measurable_pi_apply (i : ℕ)).comp hpath
    calc
      P.map path (Set.pi s t) = P (path ⁻¹' Set.pi s t) :=
        Measure.map_apply hpath
          (MeasurableSet.pi s.countable_toSet (fun i _ => ht i))
      _ = P ((fun (omega : Ω) (i : Fin q) => path omega i) ⁻¹' Set.univ.pi u) := by
        rw [hpreimage]
      _ = P.map (fun (omega : Ω) (i : Fin q) => path omega i) (Set.univ.pi u) :=
        (Measure.map_apply hprefixMeas (MeasurableSet.univ_pi hu)).symm
      _ = Measure.pi (fun _ : Fin q => μ) (Set.univ.pi u) := by
        rw [(hprefix q hq_pos).map_eq]
      _ = ∏ i : Fin q, μ (u i) := by
        rw [Measure.pi_pi]
      _ = ∏ i ∈ s, μ (t i) := by
        calc
          ∏ i : Fin q, μ (u i) =
              ∏ i : Fin q, (if (i : ℕ) ∈ s then μ (t i) else 1) := by
            apply Finset.prod_congr rfl
            intro i _
            dsimp [u]
            split_ifs <;> simp
          _ = ∏ i ∈ Finset.range q, if i ∈ s then μ (t i) else 1 :=
            (Finset.prod_range (fun i : ℕ =>
              if i ∈ s then μ (t i) else 1)).symm
        rw [Finset.prod_ite_mem]
        congr 2
        apply Finset.inter_eq_right.mpr
        intro i hi
        exact Finset.mem_range.mpr (hq i hi)
  · have hs_empty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    rw [hs_empty]
    simpa only [Finset.coe_empty, Set.empty_pi, Finset.prod_empty,
      Set.preimage_univ, measure_univ] using
      (Measure.map_apply (μ := P) hpath (MeasurableSet.univ))

end

end AppliedModelingLib.Probability.IIDStream
