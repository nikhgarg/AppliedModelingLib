import AppliedModelingLib.Foundations.Probability.IidPrefixStopping
import Mathlib.MeasureTheory.Constructions.Cylinders

/-!
# IID restart at an almost-sure first hit

This module turns a measurable positive-probability hit set in an IID stream
into a source-neutral stopped-process interface.  The first hit is totalized
only on the null no-hit event.  The results therefore prove both the law of
the uninspected whole tail and its independence from an explicitly
prefix-observable stopped history; they do not postulate a strong-Markov
property.
-/

namespace AppliedModelingLib.Probability.IIDStream

open MeasureTheory ProbabilityTheory Filter

noncomputable section

variable {α : Type*} [MeasurableSpace α]

/-- The event that coordinate `n` is the first member of `hit`. -/
def firstHitEvent (hit : Set α) (n : Nat) : Set (Nat -> α) :=
  {omega | omega n ∈ hit ∧ ∀ m < n, omega m ∉ hit}

/-- The event that the IID path never enters `hit`. -/
def neverHits (hit : Set α) : Set (Nat -> α) :=
  {omega | ∀ n, omega n ∉ hit}

/-- The first coordinate in `hit`, with an arbitrary value only on the
null no-hit event. -/
noncomputable def firstHit (hit : Set α) (omega : Nat -> α) : Nat := by
  classical
  exact if h : ∃ n, omega n ∈ hit then Nat.find h else 0

/-- The value observed at the totalized first hit. -/
noncomputable def firstHitValue (hit : Set α) (omega : Nat -> α) : α :=
  omega (firstHit hit omega)

/-- The complete IID suffix immediately after the totalized first hit. -/
noncomputable def postFirstHitTail (hit : Set α) : (Nat -> α) -> Nat -> α :=
  fun omega n => coordinate (firstHit hit omega + 1 + n) omega

private theorem measurable_prefix_firstHitEvent
    (hit : Set α) (hhit : MeasurableSet hit) (n : Nat) :
    MeasurableSet {x : Finset.range (n + 1) -> α |
      x ⟨n, Finset.mem_range.mpr (Nat.lt_succ_self n)⟩ ∈ hit ∧
        ∀ m : Fin n,
          x ⟨m, Finset.mem_range.mpr (Nat.lt_trans m.isLt
            (Nat.lt_succ_self n))⟩ ∉ hit} := by
  let last : Finset.range (n + 1) :=
    ⟨n, Finset.mem_range.mpr (Nat.lt_succ_self n)⟩
  let embed : Fin n -> Finset.range (n + 1) := fun m =>
    ⟨m, Finset.mem_range.mpr (Nat.lt_trans m.isLt (Nat.lt_succ_self n))⟩
  change MeasurableSet {x : Finset.range (n + 1) -> α |
    x last ∈ hit ∧ ∀ m : Fin n, x (embed m) ∉ hit}
  have hlast : MeasurableSet {x : Finset.range (n + 1) -> α | x last ∈ hit} :=
    (measurable_pi_apply last) hhit
  have hprior : MeasurableSet {x : Finset.range (n + 1) -> α |
      ∀ m : Fin n, x (embed m) ∉ hit} := by
    rw [show {x : Finset.range (n + 1) -> α |
        ∀ m : Fin n, x (embed m) ∉ hit} =
        ⋂ m : Fin n, {x | x (embed m) ∈ hitᶜ} by
      ext x
      simp]
    apply MeasurableSet.iInter
    intro m
    exact (measurable_pi_apply (embed m)) hhit.compl
  exact hlast.inter hprior

theorem firstHitEvent_prefix_measurable
    (hit : Set α) (hhit : MeasurableSet hit) (n : Nat) :
    MeasurableSet[MeasurableSpace.comap (streamPrefix (α := α) n)
      inferInstance] (firstHitEvent hit n) := by
  let prefixEvent : Set (Finset.range (n + 1) -> α) :=
    {x | x ⟨n, Finset.mem_range.mpr (Nat.lt_succ_self n)⟩ ∈ hit ∧
      ∀ m : Fin n,
        x ⟨m, Finset.mem_range.mpr (Nat.lt_trans m.isLt
          (Nat.lt_succ_self n))⟩ ∉ hit}
  refine MeasurableSpace.measurableSet_comap.2
    ⟨prefixEvent, measurable_prefix_firstHitEvent hit hhit n, ?_⟩
  ext omega
  simp only [Set.mem_preimage, Set.mem_setOf_eq, firstHitEvent]
  constructor
  · rintro ⟨hnow, hprior⟩
    refine ⟨hnow, ?_⟩
    intro m hm
    exact hprior ⟨m, hm⟩
  · rintro ⟨hnow, hprior⟩
    refine ⟨hnow, ?_⟩
    intro m
    exact hprior m m.isLt

theorem measurableSet_firstHitEvent
    (hit : Set α) (hhit : MeasurableSet hit) (n : Nat) :
    MeasurableSet (firstHitEvent hit n) := by
  rcases firstHitEvent_prefix_measurable hit hhit n with ⟨s, hs, hpre⟩
  rw [← hpre]
  exact (measurable_streamPrefix (α := α) n) hs

omit [MeasurableSpace α] in
theorem firstHitEvent_pairwiseDisjoint (hit : Set α) :
    Pairwise (Function.onFun Disjoint (firstHitEvent hit)) := by
  intro n m hne
  refine Set.disjoint_left.2 ?_
  intro omega hn hm
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact (hm.2 n hlt) hn.1
  · exact (hn.2 m hgt) hm.1

omit [MeasurableSpace α] in
theorem iUnion_firstHitEvent_eq_exists (hit : Set α) :
    ⋃ n, firstHitEvent hit n = {omega | ∃ n, omega n ∈ hit} := by
  classical
  ext omega
  simp only [Set.mem_iUnion, Set.mem_setOf_eq]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, hn.1⟩
  · rintro ⟨n, hn⟩
    let h : ∃ m, omega m ∈ hit := ⟨n, hn⟩
    refine ⟨Nat.find h, Nat.find_spec h, ?_⟩
    intro m hm hmem
    exact (Nat.find_min h hm) hmem

omit [MeasurableSpace α] in
theorem firstHit_eq_of_mem_firstHitEvent
    {hit : Set α} {n : Nat} {omega : Nat -> α}
    (hmem : omega ∈ firstHitEvent hit n) :
    firstHit hit omega = n := by
  classical
  let hexists : ∃ m, omega m ∈ hit := ⟨n, hmem.1⟩
  rw [firstHit, dif_pos hexists]
  apply Nat.le_antisymm
  · exact Nat.find_min' hexists (m := n) hmem.1
  · apply le_of_not_gt
    intro hlt
    exact hmem.2 (Nat.find hexists) hlt (Nat.find_spec hexists)

omit [MeasurableSpace α] in
theorem firstHit_eq_zero_of_mem_neverHits
    {hit : Set α} {omega : Nat -> α} (hmem : omega ∈ neverHits hit) :
    firstHit hit omega = 0 := by
  classical
  have hnone : ¬ ∃ n, omega n ∈ hit := by
    rintro ⟨n, hn⟩
    exact hmem n hn
  simp [firstHit, hnone]

omit [MeasurableSpace α] in
theorem firstHit_event_zero (hit : Set α) :
    {omega | firstHit hit omega = 0} = firstHitEvent hit 0 ∪ neverHits hit := by
  ext omega
  classical
  constructor
  · intro hzero
    change firstHit hit omega = 0 at hzero
    by_cases hexists : ∃ n, omega n ∈ hit
    · left
      have hfind : Nat.find hexists = 0 := by
        simp only [firstHit, dif_pos hexists] at hzero
        exact hzero
      refine ⟨?_, ?_⟩
      · simpa [hfind] using Nat.find_spec hexists
      · intro m hm hmem
        have hlt : m < Nat.find hexists := by
          rw [hfind]
          exact hm
        exact (Nat.find_min hexists hlt) hmem
    · right
      intro n hmem
      exact hexists ⟨n, hmem⟩
  · rintro (hfirst | hnever)
    · exact firstHit_eq_of_mem_firstHitEvent hfirst
    · exact firstHit_eq_zero_of_mem_neverHits hnever

omit [MeasurableSpace α] in
theorem firstHit_event_succ (hit : Set α) (n : Nat) :
    {omega | firstHit hit omega = n + 1} = firstHitEvent hit (n + 1) := by
  ext omega
  classical
  constructor
  · intro hsuccess
    change firstHit hit omega = n + 1 at hsuccess
    by_cases hexists : ∃ m, omega m ∈ hit
    · have hfind : Nat.find hexists = n + 1 := by
        simp only [firstHit, dif_pos hexists] at hsuccess
        exact hsuccess
      refine ⟨?_, ?_⟩
      · simpa [hfind] using Nat.find_spec hexists
      · intro m hm hmem
        have hlt : m < Nat.find hexists := by simpa [hfind] using hm
        exact (Nat.find_min hexists hlt) hmem
    · exfalso
      have hzero : firstHit hit omega = 0 := by simp [firstHit, hexists]
      exact Nat.succ_ne_zero n (hzero.symm.trans hsuccess).symm
  · intro hfirst
    exact firstHit_eq_of_mem_firstHitEvent hfirst

theorem measurableSet_firstHit_event
    (hit : Set α) (hhit : MeasurableSet hit) (n : Nat) :
    MeasurableSet {omega | firstHit hit omega = n} := by
  cases n with
  | zero =>
      rw [firstHit_event_zero]
      apply (measurableSet_firstHitEvent hit hhit 0).union
      rw [show neverHits hit = ⋂ n, {omega | omega n ∈ hitᶜ} by
        ext omega
        simp [neverHits]]
      apply MeasurableSet.iInter
      intro n
      exact (measurable_pi_apply n) hhit.compl
  | succ n =>
      rw [firstHit_event_succ]
      exact measurableSet_firstHitEvent hit hhit (n + 1)

theorem measurable_firstHit (hit : Set α) (hhit : MeasurableSet hit) :
    Measurable (firstHit hit) := by
  apply measurable_to_nat
  intro omega
  exact measurableSet_firstHit_event hit hhit (firstHit hit omega)

theorem measurable_firstHitValue (hit : Set α) (hhit : MeasurableSet hit) :
    Measurable (firstHitValue hit) := by
  let h : ∀ omega : Nat -> α, ∃ n, firstHit hit omega = n :=
    fun omega => ⟨firstHit hit omega, rfl⟩
  have hmeas : Measurable (fun omega : Nat -> α =>
      coordinate (Nat.find (h omega)) omega) :=
    Measurable.find
      (fun n => measurable_coordinate (α := α) n)
      (fun n => (measurable_firstHit hit hhit)
        (measurableSet_singleton n)) h
  convert hmeas using 1
  funext omega
  have hfind : Nat.find (h omega) = firstHit hit omega :=
    (Nat.find_spec (h omega)).symm
  simp only [firstHitValue, hfind, coordinate]

theorem measurable_postFirstHitTail (hit : Set α) (hhit : MeasurableSet hit) :
    Measurable (postFirstHitTail hit) := by
  apply measurable_pi_lambda
  intro n
  let h : ∀ omega : Nat -> α, ∃ m, firstHit hit omega + 1 + n = m :=
    fun omega => ⟨firstHit hit omega + 1 + n, rfl⟩
  have hmeas : Measurable (fun omega : Nat -> α =>
      coordinate (Nat.find (h omega)) omega) :=
    Measurable.find
      (fun m => measurable_coordinate (α := α) m)
      (fun m => ((measurable_firstHit hit hhit).add_const 1).add_const n
        (measurableSet_singleton m)) h
  convert hmeas using 1
  funext omega
  have hfind : Nat.find (h omega) = firstHit hit omega + 1 + n :=
    (Nat.find_spec (h omega)).symm
  simp [postFirstHitTail, hfind]

/-- A stopped-history event is observable at each first-hit level from the
prefix through that hit. -/
def FirstHitPrefixEvent (hit : Set α) (A : Set (Nat -> α)) : Prop :=
  ∀ n, MeasurableSet[MeasurableSpace.comap (streamPrefix (α := α) n)
    inferInstance] (A ∩ firstHitEvent hit n)

private theorem firstHitPrefixEvent_inter_block_measure_eq_mul
    (mu : Measure α) [IsProbabilityMeasure mu]
    (hit : Set α)
    (A : Set (Nat -> α)) (hA : FirstHitPrefixEvent hit A)
    (n q : Nat) (s : Fin q -> Set α) (hs : ∀ i, MeasurableSet (s i)) :
    measure mu (A ∩ firstHitEvent hit n ∩
      {omega | ∀ i, block (α := α) (n + 1) q omega i ∈ s i}) =
      measure mu (A ∩ firstHitEvent hit n) * ∏ i : Fin q, mu (s i) := by
  let hleft : MeasurableSet[MeasurableSpace.comap
      (streamPrefix (α := α) n) inferInstance]
      (A ∩ firstHitEvent hit n) := hA n
  have hright : MeasurableSet[MeasurableSpace.comap
      (fun omega : Nat -> α => block (α := α) (n + 1) q omega) inferInstance]
      {omega | ∀ i, block (α := α) (n + 1) q omega i ∈ s i} := by
    rw [show {omega | ∀ i, block (α := α) (n + 1) q omega i ∈ s i} =
      (fun omega : Nat -> α => block (α := α) (n + 1) q omega) ⁻¹'
        Set.univ.pi s by ext omega; simp]
    exact MeasurableSpace.measurableSet_comap.2
      ⟨Set.univ.pi s, MeasurableSet.univ_pi hs, rfl⟩
  have hfactor := indepFun_streamPrefix_block mu n q |>.meas_inter hleft hright
  calc
    measure mu (A ∩ firstHitEvent hit n ∩
        {omega | ∀ i, block (α := α) (n + 1) q omega i ∈ s i}) =
        measure mu (A ∩ firstHitEvent hit n) *
          measure mu {omega | ∀ i, block (α := α) (n + 1) q omega i ∈ s i} :=
      hfactor
    _ = measure mu (A ∩ firstHitEvent hit n) * ∏ i : Fin q, mu (s i) := by
      congr 1
      exact measure_block_mem_eq mu (n + 1) q s hs

/-- A measurable positive-probability IID hit is eventually observed almost
surely.  This is an event-level fact; it does not turn the totalized
`firstHit` value into a pathwise finite stopping index on the null no-hit
event. -/
theorem measure_neverHits_eq_zero
    (mu : Measure α) [IsProbabilityMeasure mu]
    (hit : Set α) (hhit : MeasurableSet hit) (hpos : 0 < mu hit) :
    measure mu (neverHits hit) = 0 := by
  let nu : Measure (Nat -> α) := measure mu
  let c : ENNReal := mu hitᶜ
  have hcompl : c = 1 - mu hit := by
    dsimp [c]
    rw [measure_compl hhit (measure_ne_top mu hit), measure_univ]
  have hlt : c < 1 := by
    rw [hcompl]
    exact ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hpos.ne'
  let noHitPrefix : Nat -> Set (Nat -> α) := fun count =>
    {omega | ∀ i : Fin count, block (α := α) 0 count omega i ∈ hitᶜ}
  have hsubset : ∀ count, neverHits hit ⊆ noHitPrefix count := by
    intro count omega hnever i
    simpa [noHitPrefix, block, coordinate] using hnever i
  have hmeasure : ∀ count, nu (noHitPrefix count) = c ^ count := by
    intro count
    dsimp [nu, noHitPrefix, c]
    rw [measure_block_mem_eq mu 0 count (fun _ : Fin count => hitᶜ)
      (fun _ => hhit.compl)]
    simp
  have hbound : ∀ count, nu (neverHits hit) ≤ c ^ count := by
    intro count
    calc
      nu (neverHits hit) ≤ nu (noHitPrefix count) := measure_mono (hsubset count)
      _ = c ^ count := hmeasure count
  have hpow : Tendsto (fun count : Nat => c ^ count) atTop (nhds 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hlt
  apply le_antisymm
  · exact le_of_tendsto_of_tendsto' tendsto_const_nhds hpow hbound
  · exact bot_le

/-- Under a positive measurable IID hit probability, some coordinate hits
almost surely. -/
theorem ae_exists_firstHit
    (mu : Measure α) [IsProbabilityMeasure mu]
    (hit : Set α) (hhit : MeasurableSet hit) (hpos : 0 < mu hit) :
    ∀ᵐ omega ∂measure mu, ∃ n, omega n ∈ hit := by
  rw [MeasureTheory.ae_iff]
  simpa [neverHits] using measure_neverHits_eq_zero mu hit hhit hpos

private theorem measure_firstHitPrefixEvent_inter_tail_preimage_pi_eq_mul
    (mu : Measure α) [IsProbabilityMeasure mu]
    (hit : Set α) (hhit : MeasurableSet hit) (hpos : 0 < mu hit)
    (A : Set (Nat -> α)) (hA : FirstHitPrefixEvent hit A)
    (s : Finset Nat) (t : Nat -> Set α) (ht : ∀ i, MeasurableSet (t i)) :
    measure mu (A ∩ postFirstHitTail hit ⁻¹' Set.pi s t) =
      measure mu A * (measure mu) (Set.pi s t) := by
  classical
  let nu : Measure (Nat -> α) := measure mu
  letI : IsProbabilityMeasure nu := by
    dsimp [nu, measure]
    infer_instance
  by_cases hs : s.Nonempty
  · let q : Nat := s.max' hs + 1
    let u : Fin q -> Set α := fun i => if (i : Nat) ∈ s then t i else Set.univ
    have hq : ∀ i, i ∈ s -> i < q := by
      intro i hi
      exact Nat.lt_succ_of_le (Finset.le_max' s i hi)
    have hu : ∀ i, MeasurableSet (u i) := by
      intro i
      by_cases hi : (i : Nat) ∈ s
      · simpa [u, hi] using ht i
      · simp [u, hi]
    let pieces : Nat -> Set (Nat -> α) := fun n =>
      A ∩ firstHitEvent hit n ∩
        {omega | ∀ i, block (α := α) (n + 1) q omega i ∈ u i}
    have hblock_meas : ∀ n, MeasurableSet
        {omega | ∀ i, block (α := α) (n + 1) q omega i ∈ u i} := by
      intro n
      rw [show {omega | ∀ i, block (α := α) (n + 1) q omega i ∈ u i} =
        (fun omega : Nat -> α => block (α := α) (n + 1) q omega) ⁻¹'
          Set.univ.pi u by ext omega; simp]
      exact (measurable_block (α := α) (n + 1) q)
        (MeasurableSet.univ_pi hu)
    have hhistory_meas : ∀ n, MeasurableSet (A ∩ firstHitEvent hit n) := by
      intro n
      rcases hA n with ⟨v, hv, hpre⟩
      rw [← hpre]
      exact (measurable_streamPrefix (α := α) n) hv
    have hpieces_meas : ∀ n, MeasurableSet (pieces n) := by
      intro n
      exact (hhistory_meas n).inter (hblock_meas n)
    have hpieces_disjoint : Pairwise (Function.onFun Disjoint pieces) := by
      intro n m hnm
      refine Set.disjoint_left.2 ?_
      intro omega hn hm
      exact (Set.disjoint_left.1 (firstHitEvent_pairwiseDisjoint hit hnm))
        hn.1.2 hm.1.2
    let good : Set (Nat -> α) := ⋃ n, firstHitEvent hit n
    have hgood_ae : ∀ᵐ omega ∂nu, omega ∈ good := by
      filter_upwards [ae_exists_firstHit mu hit hhit hpos] with omega hhitomega
      change omega ∈ ⋃ n, firstHitEvent hit n
      rw [iUnion_firstHitEvent_eq_exists]
      exact hhitomega
    have hpieces_union : ⋃ n, pieces n =
        A ∩ postFirstHitTail hit ⁻¹' Set.pi s t ∩ good := by
      ext omega
      simp only [Set.mem_iUnion, Set.mem_inter_iff, pieces, good,
        Set.mem_preimage, Set.mem_pi, Set.mem_setOf_eq]
      constructor
      · rintro ⟨n, ⟨hAomega, hfirst⟩, hblock⟩
        refine ⟨⟨hAomega, ?_⟩, ⟨n, hfirst⟩⟩
        intro i hi
        let ii : Fin q := ⟨i, hq i hi⟩
        have hmem := hblock ii
        change coordinate (firstHit hit omega + 1 + i) omega ∈ t i
        change coordinate (n + 1 + i) omega ∈
          (if (ii : Nat) ∈ s then t ii else Set.univ) at hmem
        have hii : (ii : Nat) ∈ s := by simpa [ii] using hi
        have hmem' : coordinate (n + 1 + i) omega ∈ t (ii : Nat) := by
          simpa [hii] using hmem
        simpa [firstHit_eq_of_mem_firstHitEvent hfirst, ii] using hmem'
      · rintro ⟨⟨hAomega, htail⟩, ⟨n, hfirst⟩⟩
        refine ⟨n, ⟨hAomega, hfirst⟩, ?_⟩
        intro i
        by_cases hi : (i : Nat) ∈ s
        · have hmem := htail (i : Nat) hi
          change coordinate (firstHit hit omega + 1 + (i : Nat)) omega ∈
            t (i : Nat) at hmem
          simpa [u, hi, firstHit_eq_of_mem_firstHitEvent hfirst] using hmem
        · simp [u, hi]
    have hmeasure_pieces :
        nu (A ∩ postFirstHitTail hit ⁻¹' Set.pi s t) = ∑' n, nu (pieces n) := by
      calc
        nu (A ∩ postFirstHitTail hit ⁻¹' Set.pi s t) =
            nu (A ∩ postFirstHitTail hit ⁻¹' Set.pi s t ∩ good) := by
          apply measure_congr
          filter_upwards [hgood_ae] with omega hgood
          apply propext
          constructor
          · intro h
            exact ⟨h, hgood⟩
          · exact fun h => h.1
        _ = nu (⋃ n, pieces n) := by rw [hpieces_union]
        _ = ∑' n, nu (pieces n) := measure_iUnion hpieces_disjoint hpieces_meas
    have hAevent_disjoint : Pairwise (Function.onFun Disjoint
        fun n => A ∩ firstHitEvent hit n) := by
      intro n m hnm
      refine Set.disjoint_left.2 ?_
      intro omega hn hm
      exact (Set.disjoint_left.1 (firstHitEvent_pairwiseDisjoint hit hnm)) hn.2 hm.2
    have hA_union : ⋃ n, A ∩ firstHitEvent hit n = A ∩ good := by
      change (⋃ n, A ∩ firstHitEvent hit n) = A ∩ ⋃ n, firstHitEvent hit n
      exact (Set.inter_iUnion _ _).symm
    have hsum_A : ∑' n, nu (A ∩ firstHitEvent hit n) = nu A := by
      calc
        ∑' n, nu (A ∩ firstHitEvent hit n) = nu (⋃ n, A ∩ firstHitEvent hit n) :=
          (measure_iUnion hAevent_disjoint hhistory_meas).symm
        _ = nu (A ∩ good) := by rw [hA_union]
        _ = nu A := by
          apply measure_congr
          filter_upwards [hgood_ae] with omega hgood
          apply propext
          constructor
          · exact fun h => h.1
          · intro h
            exact ⟨h, hgood⟩
    have hpieces_factor : (∑' n, nu (pieces n)) =
        ∑' n, nu (A ∩ firstHitEvent hit n) * ∏ i : Fin q, mu (u i) := by
      apply tsum_congr
      intro n
      exact firstHitPrefixEvent_inter_block_measure_eq_mul mu hit A hA n q u hu
    change nu (A ∩ postFirstHitTail hit ⁻¹' Set.pi s t) = _
    calc
      nu (A ∩ postFirstHitTail hit ⁻¹' Set.pi s t) = ∑' n, nu (pieces n) :=
        hmeasure_pieces
      _ = ∑' n, nu (A ∩ firstHitEvent hit n) * ∏ i : Fin q, mu (u i) :=
        hpieces_factor
      _ = (∑' n, nu (A ∩ firstHitEvent hit n)) * ∏ i : Fin q, mu (u i) := by
        exact ENNReal.tsum_mul_right
      _ = nu A * ∏ i : Fin q, mu (u i) := by rw [hsum_A]
      _ = nu A * ∏ i ∈ s, mu (t i) := by
        congr 1
        calc
          ∏ i : Fin q, mu (u i) =
              ∏ i : Fin q, (if (i : Nat) ∈ s then mu (t i) else 1) := by
            apply Finset.prod_congr rfl
            intro i _
            dsimp [u]
            split_ifs <;> simp
          _ = ∏ i ∈ Finset.range q, if i ∈ s then mu (t i) else 1 :=
            (Finset.prod_range (fun i : Nat => if i ∈ s then mu (t i) else 1)).symm
        rw [Finset.prod_ite_mem]
        congr 2
        apply Finset.inter_eq_right.mpr
        intro i hi
        exact Finset.mem_range.mpr (hq i hi)
      _ = nu A * (measure mu) (Set.pi s t) := by
        change nu A * ∏ i ∈ s, mu (t i) =
          nu A * Measure.infinitePi (fun _ : Nat => mu) (Set.pi s t)
        rw [Measure.infinitePi_pi (fun _ : Nat => mu) (fun i hi => ht i)]
  · have hs_empty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    rw [hs_empty]
    simp

/-- Restricting an IID stream to a first-hit-prefix event leaves its complete
uninspected tail at the original product law, scaled by the history event. -/
theorem map_postFirstHitTail_restrict_eq_smul
    (mu : Measure α) [IsProbabilityMeasure mu]
    (hit : Set α) (hhit : MeasurableSet hit) (hpos : 0 < mu hit)
    (A : Set (Nat -> α)) (hAmeas : MeasurableSet A)
    (hA : FirstHitPrefixEvent hit A) :
    Measure.map (postFirstHitTail hit) ((measure mu).restrict A) =
      (measure mu) A • (measure mu) := by
  classical
  let nu : Measure (Nat -> α) := measure mu
  letI : IsProbabilityMeasure nu := by
    dsimp [nu, measure]
    infer_instance
  let C : Set (Set (Nat -> α)) := squareCylinders
    (fun _ : Nat => {s : Set α | MeasurableSet s})
  refine ext_of_generate_finite C ?_ ?_ ?_ ?_
  · exact generateFrom_squareCylinders.symm
  · exact isPiSystem_squareCylinders
      (fun _ => MeasurableSpace.isPiSystem_measurableSet) (by simp)
  · rintro S ⟨s, t, ht, rfl⟩
    have ht' : ∀ i, MeasurableSet (t i) := fun i => ht i (Set.mem_univ i)
    have hpi : MeasurableSet ((s : Set Nat).pi t) :=
      MeasurableSet.pi (Finset.countable_toSet s) (fun i _ => ht' i)
    change Measure.map (postFirstHitTail hit) (nu.restrict A)
        ((s : Set Nat).pi t) = (nu A • measure mu) ((s : Set Nat).pi t)
    rw [Measure.map_apply (measurable_postFirstHitTail hit hhit) hpi,
      Measure.restrict_apply' hAmeas, Measure.smul_apply]
    · simpa [Set.inter_comm] using
        measure_firstHitPrefixEvent_inter_tail_preimage_pi_eq_mul
          mu hit hhit hpos A hA s t ht'
  · rw [Measure.map_apply (measurable_postFirstHitTail hit hhit)
      MeasurableSet.univ, Measure.restrict_apply' hAmeas, Measure.smul_apply]
    · simp

/-- A first-hit-prefix event factors from every measurable event of the full
post-hit IID tail. -/
theorem measure_firstHitPrefixEvent_inter_tail_preimage_eq_mul
    (mu : Measure α) [IsProbabilityMeasure mu]
    (hit : Set α) (hhit : MeasurableSet hit) (hpos : 0 < mu hit)
    (A : Set (Nat -> α)) (hAmeas : MeasurableSet A)
    (hA : FirstHitPrefixEvent hit A)
    (T : Set (Nat -> α)) (hT : MeasurableSet T) :
    measure mu (A ∩ postFirstHitTail hit ⁻¹' T) =
      measure mu A * (measure mu) T := by
  let nu : Measure (Nat -> α) := measure mu
  have hmap := map_postFirstHitTail_restrict_eq_smul mu hit hhit hpos A hAmeas hA
  have hpreimage : MeasurableSet (postFirstHitTail hit ⁻¹' T) :=
    hT.preimage (measurable_postFirstHitTail hit hhit)
  change nu (A ∩ postFirstHitTail hit ⁻¹' T) = nu A * (measure mu) T
  calc
    nu (A ∩ postFirstHitTail hit ⁻¹' T) =
        Measure.map (postFirstHitTail hit) (nu.restrict A) T := by
      rw [Measure.map_apply (measurable_postFirstHitTail hit hhit) hT,
        Measure.restrict_apply hpreimage]
      exact congrArg nu (Set.inter_comm _ _)
    _ = (nu A • (measure mu)) T := by rw [hmap]
    _ = nu A * (measure mu) T := by
      rw [Measure.smul_apply]
      rfl

/-- A positive-probability first hit regenerates the complete IID tail. -/
theorem postFirstHitTail_hasLaw
    (mu : Measure α) [IsProbabilityMeasure mu]
    (hit : Set α) (hhit : MeasurableSet hit) (hpos : 0 < mu hit) :
    HasLaw (postFirstHitTail hit) (measure mu) (measure mu) := by
  letI : IsProbabilityMeasure (measure mu) := by
    dsimp [measure]
    infer_instance
  refine ⟨(measurable_postFirstHitTail hit hhit).aemeasurable, ?_⟩
  calc
    Measure.map (postFirstHitTail hit) (measure mu) =
        (measure mu) Set.univ • measure mu := by
      simpa only [Measure.restrict_univ] using
        map_postFirstHitTail_restrict_eq_smul mu hit hhit hpos Set.univ
          MeasurableSet.univ (fun n => by
            rw [Set.univ_inter]
            exact firstHitEvent_prefix_measurable hit hhit n)
    _ = (1 : ENNReal) • measure mu := by rw [measure_univ]
    _ = measure mu := one_smul ENNReal (measure mu)

/-- Any stopped observation whose measurable preimages are visible through
the first-hit prefix is independent of the complete post-hit IID tail. -/
theorem indepFun_of_firstHitPrefixEvent_tail
    {β : Type*} [MeasurableSpace β]
    (mu : Measure α) [IsProbabilityMeasure mu]
    (hit : Set α) (hhit : MeasurableSet hit) (hpos : 0 < mu hit)
    (f : (Nat -> α) -> β)
    (hfmeas : Measurable f)
    (hf : ∀ S : Set β, MeasurableSet S -> FirstHitPrefixEvent hit (f ⁻¹' S)) :
    IndepFun f (postFirstHitTail hit) (measure mu) := by
  letI : IsProbabilityMeasure (measure mu) := by
    dsimp [measure]
    infer_instance
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro S T hS hT
  calc
    measure mu (f ⁻¹' S ∩ postFirstHitTail hit ⁻¹' T) =
        measure mu (f ⁻¹' S) * (measure mu) T :=
      measure_firstHitPrefixEvent_inter_tail_preimage_eq_mul
        mu hit hhit hpos (f ⁻¹' S) (hfmeas hS) (hf S hS) T hT
    _ = measure mu (f ⁻¹' S) * measure mu (postFirstHitTail hit ⁻¹' T) := by
      congr 1
      have htail : Measure.map (postFirstHitTail hit) (measure mu) = measure mu := by
        calc
          Measure.map (postFirstHitTail hit) (measure mu) =
              (measure mu) Set.univ • measure mu := by
            simpa only [Measure.restrict_univ] using
              map_postFirstHitTail_restrict_eq_smul mu hit hhit hpos Set.univ
                MeasurableSet.univ (fun n => by
                  rw [Set.univ_inter]
                  exact firstHitEvent_prefix_measurable hit hhit n)
          _ = (1 : ENNReal) • measure mu := by rw [measure_univ]
          _ = measure mu := one_smul ENNReal (measure mu)
      rw [← Measure.map_apply (measurable_postFirstHitTail hit hhit) hT, htail]

/-- The first-hit index together with the hit value is an explicitly
stopped-prefix observable. -/
theorem firstHit_index_value_prefixEvent
    (hit : Set α) (hhit : MeasurableSet hit)
    (S : Set (Nat × α)) (hS : MeasurableSet S) :
    FirstHitPrefixEvent hit
      ((fun omega : Nat -> α => (firstHit hit omega, firstHitValue hit omega)) ⁻¹' S) := by
  intro n
  let last : Finset.range (n + 1) :=
    ⟨n, Finset.mem_range.mpr (Nat.lt_succ_self n)⟩
  let prefixPair : (Finset.range (n + 1) -> α) -> Nat × α :=
    fun pref => (n, pref last)
  have hprefixPair : Measurable prefixPair :=
    measurable_const.prodMk (measurable_pi_apply last)
  rcases firstHitEvent_prefix_measurable hit hhit n with ⟨E, hE, hpreE⟩
  refine MeasurableSpace.measurableSet_comap.2
    ⟨prefixPair ⁻¹' S ∩ E, (hprefixPair hS).inter hE, ?_⟩
  ext omega
  simp only [Set.mem_preimage, Set.mem_inter_iff]
  constructor
  · rintro ⟨hpair, hfirst⟩
    have hfirst' : omega ∈ firstHitEvent hit n := by
      rw [← hpreE]
      exact hfirst
    have hindex : firstHit hit omega = n := firstHit_eq_of_mem_firstHitEvent hfirst'
    refine ⟨?_, hfirst'⟩
    simpa only [prefixPair, last, streamPrefix, coordinate, firstHitValue,
      hindex] using hpair
  · rintro ⟨hpair, hfirst⟩
    have hfirst' : streamPrefix n omega ∈ E := by
      change omega ∈ streamPrefix n ⁻¹' E
      rw [hpreE]
      exact hfirst
    refine ⟨?_, hfirst'⟩
    have hindex : firstHit hit omega = n := firstHit_eq_of_mem_firstHitEvent hfirst
    simpa only [prefixPair, last, streamPrefix, coordinate, firstHitValue,
      hindex] using hpair

/-- The stopped first-hit index and hit value are jointly independent of the
complete uninspected IID tail. -/
theorem indepFun_firstHit_index_value_postFirstHitTail
    (mu : Measure α) [IsProbabilityMeasure mu]
    (hit : Set α) (hhit : MeasurableSet hit) (hpos : 0 < mu hit) :
    IndepFun (fun omega : Nat -> α => (firstHit hit omega, firstHitValue hit omega))
      (postFirstHitTail hit) (measure mu) := by
  apply indepFun_of_firstHitPrefixEvent_tail mu hit hhit hpos
  · exact (measurable_firstHit hit hhit).prodMk
      (measurable_firstHitValue hit hhit)
  · intro S hS
    exact firstHit_index_value_prefixEvent hit hhit S hS

end

end AppliedModelingLib.Probability.IIDStream
