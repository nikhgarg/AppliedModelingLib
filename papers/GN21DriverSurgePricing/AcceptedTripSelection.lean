import GN21DriverSurgePricing.RawMarkedStoppedPathBridge
import AppliedModelingLib.Foundations.Probability.IidFirstHitRestart

/-!
# First accepted trip mark on a literal IID stream

This module isolates the mark-selection half of GN21 marked thinning.  It
proves that the actual first raw trip mark accepted by a measurable policy has
the conditional source mark law.  The clock/time-change half of all-time
Poisson thinning is intentionally separate.
-/

namespace GN21DriverSurgePricing

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal ProbabilityTheory

noncomputable section

namespace AcceptedTripSelection

/-- Repackage a raw mark stream as the Boolean-marked stream consumed by the
stopped-path API.  The dummy real coordinate is never used for selection. -/
def acceptancePairStream (sigma : TripPolicy) :
    (Nat -> TripLength) -> Nat -> MarkedRestart.Step :=
  fun marks n => (0, gn21AcceptanceMark sigma (marks n))

/-- The first raw request index whose trip mark is accepted, totalized at zero
only on the null event of no accepted marks. -/
noncomputable def firstAcceptedIndex (sigma : TripPolicy) :
    (Nat -> TripLength) -> Nat :=
  MarkedRestart.firstSuccess ∘ acceptancePairStream sigma

/-- The actual raw trip mark at the first accepted index. -/
noncomputable def firstAcceptedTripMark (sigma : TripPolicy) :
    (Nat -> TripLength) -> TripLength :=
  fun marks => marks (firstAcceptedIndex sigma marks)

/-- The complete uninspected raw-mark stream after the first accepted trip.
Unlike the older Boolean-mark tail, this retains continuous trip marks and is
therefore suitable for renewal-cycle regeneration. -/
noncomputable def firstAcceptedTripTail (sigma : TripPolicy) :
    (Nat -> TripLength) -> Nat -> TripLength :=
  AppliedModelingLib.Probability.IIDStream.postFirstHitTail sigma

theorem measurable_firstAcceptedTripTail
    (sigma : TripPolicy) (hsigma : MeasurableSet sigma) :
    Measurable (firstAcceptedTripTail sigma) := by
  simpa only [firstAcceptedTripTail] using
    AppliedModelingLib.Probability.IIDStream.measurable_postFirstHitTail sigma hsigma

theorem firstAcceptedIndex_eq_firstHit
    (sigma : TripPolicy) (marks : Nat -> TripLength) :
    firstAcceptedIndex sigma marks =
      AppliedModelingLib.Probability.IIDStream.firstHit sigma marks := by
  classical
  unfold firstAcceptedIndex MarkedRestart.firstSuccess acceptancePairStream
    AppliedModelingLib.Probability.IIDStream.firstHit
  by_cases h : ∃ n, marks n ∈ sigma
  · have hacc : ∃ n, MarkedRestart.accepted
        (fun n => (0, gn21AcceptanceMark sigma (marks n))) n := by
        simpa [MarkedRestart.accepted, gn21AcceptanceMark] using h
    simp only [Function.comp_apply, dif_pos hacc, dif_pos h]
    apply Nat.le_antisymm
    · exact Nat.find_min' hacc (by
        simpa [MarkedRestart.accepted, gn21AcceptanceMark] using Nat.find_spec h)
    · exact Nat.find_min' h (by
        simpa [MarkedRestart.accepted, gn21AcceptanceMark] using Nat.find_spec hacc)
  · simp [MarkedRestart.accepted, gn21AcceptanceMark, h]

theorem firstAcceptedTripMark_eq_firstHitValue
    (sigma : TripPolicy) (marks : Nat -> TripLength) :
    firstAcceptedTripMark sigma marks =
      AppliedModelingLib.Probability.IIDStream.firstHitValue sigma marks := by
  simp only [firstAcceptedTripMark,
    AppliedModelingLib.Probability.IIDStream.firstHitValue]
  rw [firstAcceptedIndex_eq_firstHit]

theorem measurable_acceptancePairStream
    (sigma : TripPolicy) (hsigma : MeasurableSet sigma) :
    Measurable (acceptancePairStream sigma) := by
  apply measurable_pi_lambda
  intro n
  exact measurable_const.prodMk
    ((measurable_gn21AcceptanceMark sigma hsigma).comp (measurable_pi_apply n))

theorem firstAcceptedIndex_eq_firstSuccess
    (sigma : TripPolicy) (marks : Nat -> TripLength) :
    firstAcceptedIndex sigma marks =
      MarkedRestart.firstSuccess (acceptancePairStream sigma marks) := rfl

theorem firstAcceptedIndex_eq_of_firstSuccessEvent
    (sigma : TripPolicy) {marks : Nat -> TripLength} {n : Nat}
    (h : acceptancePairStream sigma marks ∈ MarkedRestart.firstSuccessEvent n) :
    firstAcceptedIndex sigma marks = n := by
  exact MarkedRestart.firstSuccess_eq_of_mem_firstSuccessEvent h

theorem measurableSet_firstAcceptedIndex_event
    (sigma : TripPolicy) (hsigma : MeasurableSet sigma) (n : Nat) :
    MeasurableSet {marks : Nat -> TripLength | firstAcceptedIndex sigma marks = n} := by
  change MeasurableSet
    (acceptancePairStream sigma ⁻¹'
      {pairs | MarkedRestart.firstSuccess pairs = n})
  exact (MarkedRestart.measurableSet_firstSuccess_event n).preimage
    (measurable_acceptancePairStream sigma hsigma)

theorem measurable_firstAcceptedIndex
    (sigma : TripPolicy) (hsigma : MeasurableSet sigma) :
    Measurable (firstAcceptedIndex sigma) := by
  apply measurable_to_nat
  intro marks
  exact measurableSet_firstAcceptedIndex_event sigma hsigma
    (firstAcceptedIndex sigma marks)

theorem measurable_firstAcceptedTripMark
    (sigma : TripPolicy) (hsigma : MeasurableSet sigma) :
    Measurable (firstAcceptedTripMark sigma) := by
  let h : forall marks : Nat -> TripLength,
      exists n, firstAcceptedIndex sigma marks = n :=
    fun marks => ⟨firstAcceptedIndex sigma marks, rfl⟩
  have hmeas : Measurable (fun marks : Nat -> TripLength =>
      marks (Nat.find (h marks))) :=
    Measurable.find
      (fun n => measurable_pi_apply n)
      (fun n => measurableSet_firstAcceptedIndex_event sigma hsigma n)
      h
  convert hmeas using 1
  funext marks
  have hfind : Nat.find (h marks) = firstAcceptedIndex sigma marks :=
    (Nat.find_spec (h marks)).symm
  simp [firstAcceptedTripMark, hfind]

/-- The exact raw-mark characterization of a first accepted-index event. -/
theorem mem_firstSuccessEvent_iff
    (sigma : TripPolicy) (marks : Nat -> TripLength) (n : Nat) :
    acceptancePairStream sigma marks ∈ MarkedRestart.firstSuccessEvent n ↔
      marks n ∈ sigma ∧ ∀ m < n, marks m ∉ sigma := by
  classical
  simp [acceptancePairStream, MarkedRestart.firstSuccessEvent,
    MarkedRestart.accepted, gn21AcceptanceMark]

/-- The exact event that raw mark `n` is the first accepted request. -/
def firstAcceptedEvent (sigma : TripPolicy) (n : Nat) : Set (Nat -> TripLength) :=
  acceptancePairStream sigma ⁻¹' MarkedRestart.firstSuccessEvent n

/-- The event that no raw request mark is accepted. -/
def neverAccepted (sigma : TripPolicy) : Set (Nat -> TripLength) :=
  {marks | ∀ n, marks n ∉ sigma}

/-- The finite prefix event that all raw request marks are rejected. -/
def noAcceptedPrefix (sigma : TripPolicy) (count : Nat) : Set (Nat -> TripLength) :=
  {marks | ∀ i : Fin count,
    IIDStream.block (α := TripLength) 0 count marks i ∈ sigmaᶜ}

theorem measurableSet_firstAcceptedEvent
    (sigma : TripPolicy) (hsigma : MeasurableSet sigma) (n : Nat) :
    MeasurableSet (firstAcceptedEvent sigma n) := by
  exact MarkedRestart.measurableSet_firstSuccessEvent n |>.preimage
    (measurable_acceptancePairStream sigma hsigma)

theorem mem_firstAcceptedEvent_iff
    (sigma : TripPolicy) (marks : Nat -> TripLength) (n : Nat) :
    marks ∈ firstAcceptedEvent sigma n ↔
      marks n ∈ sigma ∧ ∀ m < n, marks m ∉ sigma := by
  exact mem_firstSuccessEvent_iff sigma marks n

theorem measure_noAcceptedPrefix
    (mu : Measure TripLength) [IsProbabilityMeasure mu]
    (sigma : TripPolicy) (hsigma : MeasurableSet sigma) (count : Nat) :
    IIDStream.measure mu (noAcceptedPrefix sigma count) = (mu sigmaᶜ) ^ count := by
  unfold noAcceptedPrefix
  rw [IIDStream.measure_block_mem_eq mu 0 count
    (fun _ : Fin count => sigmaᶜ) (fun _ => hsigma.compl)]
  simp

theorem neverAccepted_subset_noAcceptedPrefix
  (sigma : TripPolicy) (count : Nat) :
    neverAccepted sigma ⊆ noAcceptedPrefix sigma count := by
  intro marks hnever i
  simpa [noAcceptedPrefix, IIDStream.block, IIDStream.coordinate] using hnever i

/-- Positive source policy mass implies that an actual raw mark stream has an
accepted request almost surely. -/
theorem ae_exists_accepted
    (mu : Measure TripLength) [IsProbabilityMeasure mu]
    (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hmass : 0 < singleStateTripMass mu sigma) :
    ∀ᵐ marks ∂IIDStream.measure mu, ∃ n, marks n ∈ sigma := by
  let nu : Measure (Nat -> TripLength) := IIDStream.measure mu
  let c : ENNReal := mu sigmaᶜ
  have hmass' : 0 < mu sigma :=
    measure_pos_of_singleStateTripMass_pos mu sigma hmass
  have hcompl : c = 1 - mu sigma := by
    dsimp [c]
    rw [measure_compl hsigma (measure_ne_top mu sigma), measure_univ]
  have hlt : c < 1 := by
    rw [hcompl]
    exact ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hmass'.ne'
  have hsubset : ∀ count : Nat,
      neverAccepted sigma ⊆ noAcceptedPrefix sigma count :=
    neverAccepted_subset_noAcceptedPrefix sigma
  have hbound : ∀ count : Nat, nu (neverAccepted sigma) ≤ c ^ count := by
    intro count
    calc
      nu (neverAccepted sigma) ≤ nu (noAcceptedPrefix sigma count) :=
        measure_mono (hsubset count)
      _ = c ^ count := by
        simpa [nu, c] using measure_noAcceptedPrefix mu sigma hsigma count
  have hpow : Tendsto (fun count : Nat => c ^ count) atTop (nhds 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hlt
  have hzero : nu (neverAccepted sigma) = 0 := by
    apply le_antisymm
    · exact le_of_tendsto_of_tendsto' tendsto_const_nhds hpow hbound
    · exact bot_le
  rw [MeasureTheory.ae_iff]
  simpa [nu, neverAccepted] using hzero

/-- A finite raw-prefix calculation: the `n`th request is the first accepted
one and lies in `s` exactly when the earlier raw marks are outside `sigma` and
the `n`th raw mark lies in `sigma ∩ s`. -/
theorem measure_firstAcceptedEvent_inter_coordinate_preimage
    (mu : Measure TripLength) [IsProbabilityMeasure mu]
    (sigma : TripPolicy) (hsigma : MeasurableSet sigma) (n : Nat)
    (s : Set TripLength) (hs : MeasurableSet s) :
    IIDStream.measure mu
      (firstAcceptedEvent sigma n ∩ {marks | marks n ∈ s}) =
        (mu sigmaᶜ) ^ n * mu (sigma ∩ s) := by
  classical
  let sets : Fin (n + 1) -> Set TripLength := fun i =>
    if (i : Nat) < n then sigmaᶜ else sigma ∩ s
  have hsets : forall i, MeasurableSet (sets i) := by
    intro i
    by_cases hi : (i : Nat) < n
    · simp [sets, hi, hsigma.compl]
    · simp [sets, hi, hsigma.inter hs]
  have hrect :
      firstAcceptedEvent sigma n ∩ {marks | marks n ∈ s} =
        {marks | forall i : Fin (n + 1),
          IIDStream.block (α := TripLength) 0 (n + 1) marks i ∈ sets i} := by
    ext marks
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hfirst, hmem⟩
      rw [mem_firstAcceptedEvent_iff] at hfirst
      intro i
      by_cases hi : (i : Nat) < n
      · simpa [sets, hi, IIDStream.block, IIDStream.coordinate] using
          hfirst.2 (i : Nat) hi
      · have hin : (i : Nat) = n := by omega
        simpa [sets, hi, hin, IIDStream.block, IIDStream.coordinate] using
          And.intro hfirst.1 hmem
    · intro hrectmem
      rw [mem_firstAcceptedEvent_iff]
      have hlast := hrectmem (Fin.last n)
      have hlast' : marks n ∈ sigma ∩ s := by
        simpa [sets, IIDStream.block, IIDStream.coordinate] using hlast
      refine ⟨⟨hlast'.1, ?_⟩, hlast'.2⟩
      intro m hm
      let i : Fin (n + 1) :=
        ⟨m, Nat.lt_trans hm (Nat.lt_succ_self n)⟩
      have hprior := hrectmem i
      have hi : (i : Nat) < n := by simpa [i] using hm
      simpa [sets, hi, i, IIDStream.block, IIDStream.coordinate] using hprior
  have hprod : (∏ i : Fin (n + 1), mu (sets i)) =
      (mu sigmaᶜ) ^ n * mu (sigma ∩ s) := by
    rw [Fin.prod_univ_castSucc]
    simp [sets]
  rw [hrect, IIDStream.measure_block_mem_eq mu 0 (n + 1) sets hsets]
  exact hprod

theorem firstAcceptedEvent_pairwiseDisjoint (sigma : TripPolicy) :
    Pairwise (Function.onFun Disjoint (firstAcceptedEvent sigma)) := by
  intro n m hne
  refine Set.disjoint_left.2 ?_
  intro marks hn hm
  exact (Set.disjoint_left.1
    (MarkedRestart.firstSuccessEvent_pairwiseDisjoint hne)) hn hm

theorem iUnion_firstAcceptedEvent_eq_exists (sigma : TripPolicy) :
    ⋃ n, firstAcceptedEvent sigma n =
      {marks : Nat -> TripLength | ∃ n, marks n ∈ sigma} := by
  classical
  ext marks
  simp only [Set.mem_iUnion, Set.mem_setOf_eq]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, (mem_firstAcceptedEvent_iff sigma marks n).mp hn |>.1⟩
  · rintro ⟨n, hn⟩
    let h : ∃ m, marks m ∈ sigma := ⟨n, hn⟩
    refine ⟨Nat.find h, ?_⟩
    rw [mem_firstAcceptedEvent_iff]
    refine ⟨Nat.find_spec h, ?_⟩
    intro m hm
    exact Nat.find_min h hm

theorem measure_firstAcceptedEvent
    (mu : Measure TripLength) [IsProbabilityMeasure mu]
    (sigma : TripPolicy) (hsigma : MeasurableSet sigma) (n : Nat) :
    IIDStream.measure mu (firstAcceptedEvent sigma n) =
      (mu sigmaᶜ) ^ n * mu sigma := by
  simpa using measure_firstAcceptedEvent_inter_coordinate_preimage
    mu sigma hsigma n Set.univ MeasurableSet.univ

theorem tsum_measure_firstAcceptedEvent_eq_one
    (mu : Measure TripLength) [IsProbabilityMeasure mu]
    (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hmass : 0 < singleStateTripMass mu sigma) :
    ∑' n, IIDStream.measure mu (firstAcceptedEvent sigma n) = 1 := by
  let nu : Measure (Nat -> TripLength) := IIDStream.measure mu
  let good : Set (Nat -> TripLength) := {marks | ∃ n, marks n ∈ sigma}
  letI : IsProbabilityMeasure nu := by
    dsimp [nu, IIDStream.measure]
    infer_instance
  have hgood_ae : ∀ᵐ marks ∂nu, marks ∈ good := by
    simpa [nu, good] using ae_exists_accepted mu sigma hsigma hmass
  have hgood_compl_zero : nu goodᶜ = 0 := by
    rw [MeasureTheory.ae_iff] at hgood_ae
    change nu goodᶜ = 0 at hgood_ae
    exact hgood_ae
  have hgood_measure : nu good = 1 := by
    calc
      nu good = nu Set.univ := measure_of_measure_compl_eq_zero hgood_compl_zero
      _ = 1 := measure_univ
  calc
    ∑' n, IIDStream.measure mu (firstAcceptedEvent sigma n) =
        nu (⋃ n, firstAcceptedEvent sigma n) := by
      symm
      exact measure_iUnion (firstAcceptedEvent_pairwiseDisjoint sigma)
        (measurableSet_firstAcceptedEvent sigma hsigma)
    _ = nu good := by
      rw [iUnion_firstAcceptedEvent_eq_exists]
    _ = 1 := hgood_measure

theorem iUnion_firstAcceptedEvent_inter_coordinate_preimage_eq
    (sigma : TripPolicy) (s : Set TripLength) :
    ⋃ n, firstAcceptedEvent sigma n ∩ {marks | marks n ∈ s} =
      {marks | firstAcceptedTripMark sigma marks ∈ s} ∩
        {marks | ∃ n, marks n ∈ sigma} := by
  classical
  ext marks
  simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨n, hfirst, hmem⟩
    refine ⟨?_, ⟨n, (mem_firstAcceptedEvent_iff sigma marks n).mp hfirst |>.1⟩⟩
    change marks (firstAcceptedIndex sigma marks) ∈ s
    have hindex := firstAcceptedIndex_eq_of_firstSuccessEvent sigma hfirst
    simpa [hindex] using hmem
  · rintro ⟨hselected, ⟨n, hn⟩⟩
    let h : ∃ m, marks m ∈ sigma := ⟨n, hn⟩
    let k := Nat.find h
    have hfirst : marks ∈ firstAcceptedEvent sigma k := by
      rw [mem_firstAcceptedEvent_iff]
      refine ⟨?_, ?_⟩
      · simpa [k] using Nat.find_spec h
      · intro m hm
        exact Nat.find_min h hm
    refine ⟨k, hfirst, ?_⟩
    change marks (firstAcceptedIndex sigma marks) ∈ s at hselected
    have hindex := firstAcceptedIndex_eq_of_firstSuccessEvent sigma hfirst
    simpa [hindex] using hselected

/-- On the literal raw IID trip stream, the first accepted trip mark has the
source law conditioned on acceptance.  The totalization of the selector at
zero is harmless because positive accepted mass makes the no-acceptance event
null, proved explicitly above. -/
theorem measure_firstAcceptedTripMark_preimage_eq_cond
    (mu : Measure TripLength) [IsProbabilityMeasure mu]
    (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hmass : 0 < singleStateTripMass mu sigma)
    (s : Set TripLength) (hs : MeasurableSet s) :
    IIDStream.measure mu ((firstAcceptedTripMark sigma) ⁻¹' s) =
      gn21AcceptedTripLaw mu sigma s := by
  classical
  let nu : Measure (Nat -> TripLength) := IIDStream.measure mu
  let good : Set (Nat -> TripLength) := {marks | ∃ n, marks n ∈ sigma}
  let pieces : Nat -> Set (Nat -> TripLength) := fun n =>
    firstAcceptedEvent sigma n ∩ {marks | marks n ∈ s}
  letI : IsProbabilityMeasure nu := by
    dsimp [nu, IIDStream.measure]
    infer_instance
  have hmass' : 0 < mu sigma :=
    measure_pos_of_singleStateTripMass_pos mu sigma hmass
  have hmass_ne : mu sigma ≠ 0 := ne_of_gt hmass'
  have hmass_ne_top : mu sigma ≠ ∞ := measure_ne_top mu sigma
  have hgood_ae : ∀ᵐ marks ∂nu, marks ∈ good := by
    simpa [nu, good] using ae_exists_accepted mu sigma hsigma hmass
  have hselected_ae : ∀ᵐ marks ∂nu,
      (marks ∈ ((firstAcceptedTripMark sigma) ⁻¹' s)) =
        (marks ∈ (((firstAcceptedTripMark sigma) ⁻¹' s) ∩ good)) := by
    filter_upwards [hgood_ae] with marks hmarks
    simp [hmarks]
  have hpieces_meas : forall n, MeasurableSet (pieces n) := by
    intro n
    exact (measurableSet_firstAcceptedEvent sigma hsigma n).inter
      ((measurable_pi_apply n) hs)
  have hpieces_disjoint : Pairwise (Function.onFun Disjoint pieces) := by
    intro n m hne
    refine Set.disjoint_left.2 ?_
    intro marks hn hm
    exact (Set.disjoint_left.1 (firstAcceptedEvent_pairwiseDisjoint sigma hne))
      hn.1 hm.1
  have hpieces_union : ⋃ n, pieces n =
      ((firstAcceptedTripMark sigma) ⁻¹' s) ∩ good := by
    change ⋃ n, firstAcceptedEvent sigma n ∩ {marks | marks n ∈ s} =
      {marks | firstAcceptedTripMark sigma marks ∈ s} ∩
        {marks | ∃ n, marks n ∈ sigma}
    exact iUnion_firstAcceptedEvent_inter_coordinate_preimage_eq sigma s
  have hpieces_factor : forall n,
      nu (pieces n) = nu (firstAcceptedEvent sigma n) *
        gn21AcceptedTripLaw mu sigma s := by
    intro n
    have hfirst : nu (firstAcceptedEvent sigma n) =
        (mu sigmaᶜ) ^ n * mu sigma := by
      simpa [nu] using measure_firstAcceptedEvent mu sigma hsigma n
    calc
      nu (pieces n) = (mu sigmaᶜ) ^ n * mu (sigma ∩ s) := by
        simpa [nu, pieces] using
          measure_firstAcceptedEvent_inter_coordinate_preimage mu sigma hsigma n s hs
      _ = ((mu sigmaᶜ) ^ n * mu sigma) * gn21AcceptedTripLaw mu sigma s := by
        unfold gn21AcceptedTripLaw
        rw [ProbabilityTheory.cond_apply hsigma mu s]
        calc
          (mu sigmaᶜ) ^ n * mu (sigma ∩ s) =
              (mu sigmaᶜ) ^ n * (1 * mu (sigma ∩ s)) := by simp
          _ = (mu sigmaᶜ) ^ n * (mu sigma * (mu sigma)⁻¹) *
              mu (sigma ∩ s) := by
            rw [ENNReal.mul_inv_cancel hmass_ne hmass_ne_top]
            simp
          _ = ((mu sigmaᶜ) ^ n * mu sigma) *
              ((mu sigma)⁻¹ * mu (sigma ∩ s)) := by ac_rfl
      _ = nu (firstAcceptedEvent sigma n) * gn21AcceptedTripLaw mu sigma s := by
        rw [hfirst]
  have hsum : ∑' n, nu (firstAcceptedEvent sigma n) = 1 := by
    simpa [nu] using tsum_measure_firstAcceptedEvent_eq_one mu sigma hsigma hmass
  change nu ((firstAcceptedTripMark sigma) ⁻¹' s) = gn21AcceptedTripLaw mu sigma s
  calc
    nu ((firstAcceptedTripMark sigma) ⁻¹' s) =
        nu (((firstAcceptedTripMark sigma) ⁻¹' s) ∩ good) :=
      measure_congr hselected_ae
    _ = nu (⋃ n, pieces n) := by rw [hpieces_union]
    _ = ∑' n, nu (pieces n) := measure_iUnion hpieces_disjoint hpieces_meas
    _ = ∑' n, nu (firstAcceptedEvent sigma n) * gn21AcceptedTripLaw mu sigma s := by
      apply tsum_congr
      exact hpieces_factor
    _ = (∑' n, nu (firstAcceptedEvent sigma n)) * gn21AcceptedTripLaw mu sigma s :=
      ENNReal.tsum_mul_right
    _ = gn21AcceptedTripLaw mu sigma s := by simp [hsum]

/-- The selected first accepted raw trip mark has exactly the source law
conditioned on acceptance. -/
theorem firstAcceptedTripMark_hasLaw
    (mu : Measure TripLength) [IsProbabilityMeasure mu]
    (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hmass : 0 < singleStateTripMass mu sigma) :
    HasLaw (firstAcceptedTripMark sigma) (gn21AcceptedTripLaw mu sigma)
      (IIDStream.measure mu) := by
  refine ⟨(measurable_firstAcceptedTripMark sigma hsigma).aemeasurable, ?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (measurable_firstAcceptedTripMark sigma hsigma) hs]
  exact measure_firstAcceptedTripMark_preimage_eq_cond mu sigma hsigma hmass s hs

/-- The actual first accepted index and continuous selected trip mark are
jointly independent of the complete future raw-mark tail.  This derives the
marked regeneration fact from the iid source stream; it is not a renewal
certificate supplied by a caller. -/
theorem indepFun_firstAcceptedIndex_firstAcceptedTripMark_postTail
    (mu : Measure TripLength) [IsProbabilityMeasure mu]
    (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hmass : 0 < singleStateTripMass mu sigma) :
    ProbabilityTheory.IndepFun
      (fun marks : Nat -> TripLength =>
        (firstAcceptedIndex sigma marks, firstAcceptedTripMark sigma marks))
      (firstAcceptedTripTail sigma)
      (IIDStream.measure mu) := by
  have hmass' : 0 < mu sigma :=
    measure_pos_of_singleStateTripMass_pos mu sigma hmass
  have hindep :=
    AppliedModelingLib.Probability.IIDStream.indepFun_firstHit_index_value_postFirstHitTail
      mu sigma hsigma hmass'
  simpa only [firstAcceptedTripTail, firstAcceptedIndex_eq_firstHit,
    firstAcceptedTripMark_eq_firstHitValue] using hindep

/-- The full continuous mark stream after the first accepted request has the
original iid source law. -/
theorem firstAcceptedTripTail_hasLaw
    (mu : Measure TripLength) [IsProbabilityMeasure mu]
    (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hmass : 0 < singleStateTripMass mu sigma) :
    HasLaw (firstAcceptedTripTail sigma) (IIDStream.measure mu)
      (IIDStream.measure mu) := by
  have hmass' : 0 < mu sigma :=
    measure_pos_of_singleStateTripMass_pos mu sigma hmass
  simpa only [firstAcceptedTripTail] using
    AppliedModelingLib.Probability.IIDStream.postFirstHitTail_hasLaw
      mu sigma hsigma hmass'

/-- The first accepted request's raw index is independent of the trip mark
selected at that index.  This is the marked-renewal fact needed to combine
the geometrically stopped request count with a conditional accepted-trip law:
the stopping index depends on which earlier marks were rejected, whereas the
value of the successful mark has the source law conditioned on acceptance. -/
theorem indepFun_firstAcceptedIndex_firstAcceptedTripMark
    (mu : Measure TripLength) [IsProbabilityMeasure mu]
    (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hmass : 0 < singleStateTripMass mu sigma) :
    ProbabilityTheory.IndepFun (firstAcceptedIndex sigma)
      (firstAcceptedTripMark sigma) (IIDStream.measure mu) := by
  classical
  let nu : Measure (Nat -> TripLength) := IIDStream.measure mu
  let good : Set (Nat -> TripLength) := {marks | ∃ n, marks n ∈ sigma}
  let acceptedLaw : Measure TripLength := gn21AcceptedTripLaw mu sigma
  letI : IsProbabilityMeasure nu := by
    dsimp [nu, IIDStream.measure]
    infer_instance
  letI : IsProbabilityMeasure acceptedLaw := by
    dsimp [acceptedLaw]
    exact gn21AcceptedTripLaw_isProbability mu sigma hmass
  apply (ProbabilityTheory.indepFun_iff_measure_inter_preimage_eq_mul).mpr
  intro indexSet markSet hindexSet hmarkSet
  let indices := {n : Nat // n ∈ indexSet}
  let indexPieces : indices -> Set (Nat -> TripLength) := fun n =>
    firstAcceptedEvent sigma n.1
  let jointPieces : indices -> Set (Nat -> TripLength) := fun n =>
    firstAcceptedEvent sigma n.1 ∩ {marks | marks n.1 ∈ markSet}
  have hgood_ae : ∀ᵐ marks ∂nu, marks ∈ good := by
    simpa [nu, good] using ae_exists_accepted mu sigma hsigma hmass
  have hindex_ae : ∀ᵐ marks ∂nu,
      (marks ∈ (firstAcceptedIndex sigma) ⁻¹' indexSet) =
        (marks ∈ ((firstAcceptedIndex sigma) ⁻¹' indexSet ∩ good)) := by
    filter_upwards [hgood_ae] with marks hmarks
    simp [hmarks]
  have hjoint_ae : ∀ᵐ marks ∂nu,
      (marks ∈ ((firstAcceptedIndex sigma) ⁻¹' indexSet ∩
        (firstAcceptedTripMark sigma) ⁻¹' markSet)) =
        (marks ∈ (((firstAcceptedIndex sigma) ⁻¹' indexSet ∩
          (firstAcceptedTripMark sigma) ⁻¹' markSet) ∩ good)) := by
    filter_upwards [hgood_ae] with marks hmarks
    simp [hmarks]
  have hindexPieces_meas : ∀ n : indices, MeasurableSet (indexPieces n) := by
    intro n
    exact measurableSet_firstAcceptedEvent sigma hsigma n.1
  have hjointPieces_meas : ∀ n : indices, MeasurableSet (jointPieces n) := by
    intro n
    exact (measurableSet_firstAcceptedEvent sigma hsigma n.1).inter
      ((measurable_pi_apply n.1) hmarkSet)
  have hindexPieces_disjoint : Pairwise (Function.onFun Disjoint indexPieces) := by
    intro n m hnm
    exact firstAcceptedEvent_pairwiseDisjoint sigma (fun h => hnm (Subtype.ext h))
  have hjointPieces_disjoint : Pairwise (Function.onFun Disjoint jointPieces) := by
    intro n m hnm
    refine Set.disjoint_left.2 ?_
    intro marks hn hm
    exact (Set.disjoint_left.1
      (hindexPieces_disjoint hnm)) hn.1 hm.1
  have hindexPieces_union :
      ⋃ n : indices, indexPieces n =
        (firstAcceptedIndex sigma) ⁻¹' indexSet ∩ good := by
    ext marks
    simp only [Set.mem_iUnion, Set.mem_inter_iff, indexPieces, good,
      Set.mem_preimage, Set.mem_setOf_eq]
    constructor
    · rintro ⟨n, hfirst⟩
      refine ⟨?_, ⟨n.1, (mem_firstAcceptedEvent_iff sigma marks n.1).mp hfirst |>.1⟩⟩
      rw [firstAcceptedIndex_eq_of_firstSuccessEvent sigma hfirst]
      exact n.2
    · rintro ⟨hindex, ⟨n, hn⟩⟩
      let h : ∃ m, marks m ∈ sigma := ⟨n, hn⟩
      let k := Nat.find h
      have hfirst : marks ∈ firstAcceptedEvent sigma k := by
        rw [mem_firstAcceptedEvent_iff]
        refine ⟨Nat.find_spec h, ?_⟩
        intro m hm
        exact Nat.find_min h hm
      have hk : k ∈ indexSet := by
        rw [← firstAcceptedIndex_eq_of_firstSuccessEvent sigma hfirst]
        exact hindex
      exact ⟨⟨k, hk⟩, hfirst⟩
  have hjointPieces_union :
      ⋃ n : indices, jointPieces n =
        ((firstAcceptedIndex sigma) ⁻¹' indexSet ∩
          (firstAcceptedTripMark sigma) ⁻¹' markSet) ∩ good := by
    ext marks
    simp only [Set.mem_iUnion, Set.mem_inter_iff, jointPieces, good,
      Set.mem_preimage, Set.mem_setOf_eq]
    constructor
    · rintro ⟨n, hfirst, hmark⟩
      have hindex := firstAcceptedIndex_eq_of_firstSuccessEvent sigma hfirst
      refine ⟨⟨?_, ?_⟩, ⟨n.1, (mem_firstAcceptedEvent_iff sigma marks n.1).mp hfirst |>.1⟩⟩
      · rw [hindex]
        exact n.2
      · change marks (firstAcceptedIndex sigma marks) ∈ markSet
        simpa [hindex] using hmark
    · rintro ⟨⟨hindex, hmark⟩, ⟨n, hn⟩⟩
      let h : ∃ m, marks m ∈ sigma := ⟨n, hn⟩
      let k := Nat.find h
      have hfirst : marks ∈ firstAcceptedEvent sigma k := by
        rw [mem_firstAcceptedEvent_iff]
        refine ⟨Nat.find_spec h, ?_⟩
        intro m hm
        exact Nat.find_min h hm
      have hk : k ∈ indexSet := by
        rw [← firstAcceptedIndex_eq_of_firstSuccessEvent sigma hfirst]
        exact hindex
      refine ⟨⟨k, hk⟩, hfirst, ?_⟩
      change marks k ∈ markSet
      change marks (firstAcceptedIndex sigma marks) ∈ markSet at hmark
      simpa [firstAcceptedIndex_eq_of_firstSuccessEvent sigma hfirst] using hmark
  have hpiece_factor (n : indices) :
      nu (jointPieces n) = nu (indexPieces n) * acceptedLaw markSet := by
    have hfirst : nu (indexPieces n) = (mu sigmaᶜ) ^ n.1 * mu sigma := by
      simpa [nu, indexPieces] using measure_firstAcceptedEvent mu sigma hsigma n.1
    calc
      nu (jointPieces n) = (mu sigmaᶜ) ^ n.1 * mu (sigma ∩ markSet) := by
        simpa [nu, jointPieces] using
          measure_firstAcceptedEvent_inter_coordinate_preimage
            mu sigma hsigma n.1 markSet hmarkSet
      _ = ((mu sigmaᶜ) ^ n.1 * mu sigma) * acceptedLaw markSet := by
        unfold acceptedLaw gn21AcceptedTripLaw
        rw [ProbabilityTheory.cond_apply hsigma mu markSet]
        have hmass' : mu sigma ≠ 0 := by
          exact ne_of_gt (measure_pos_of_singleStateTripMass_pos mu sigma hmass)
        have hmass_ne_top : mu sigma ≠ ∞ := measure_ne_top mu sigma
        calc
          (mu sigmaᶜ) ^ n.1 * mu (sigma ∩ markSet) =
              (mu sigmaᶜ) ^ n.1 * (1 * mu (sigma ∩ markSet)) := by simp
          _ = (mu sigmaᶜ) ^ n.1 * (mu sigma * (mu sigma)⁻¹) *
              mu (sigma ∩ markSet) := by
            rw [ENNReal.mul_inv_cancel hmass' hmass_ne_top]
            simp
          _ = ((mu sigmaᶜ) ^ n.1 * mu sigma) *
              ((mu sigma)⁻¹ * mu (sigma ∩ markSet)) := by ac_rfl
      _ = nu (indexPieces n) * acceptedLaw markSet := by rw [hfirst]
  have hindex_measure :
      nu ((firstAcceptedIndex sigma) ⁻¹' indexSet) =
        ∑' n : indices, nu (indexPieces n) := by
    calc
      nu ((firstAcceptedIndex sigma) ⁻¹' indexSet) =
          nu ((firstAcceptedIndex sigma) ⁻¹' indexSet ∩ good) :=
        measure_congr hindex_ae
      _ = nu (⋃ n : indices, indexPieces n) := by rw [hindexPieces_union]
      _ = ∑' n : indices, nu (indexPieces n) :=
        measure_iUnion hindexPieces_disjoint hindexPieces_meas
  calc
    nu ((firstAcceptedIndex sigma) ⁻¹' indexSet ∩
        (firstAcceptedTripMark sigma) ⁻¹' markSet) =
        nu (((firstAcceptedIndex sigma) ⁻¹' indexSet ∩
          (firstAcceptedTripMark sigma) ⁻¹' markSet) ∩ good) :=
      measure_congr hjoint_ae
    _ = nu (⋃ n : indices, jointPieces n) := by rw [hjointPieces_union]
    _ = ∑' n : indices, nu (jointPieces n) :=
      measure_iUnion hjointPieces_disjoint hjointPieces_meas
    _ = ∑' n : indices, nu (indexPieces n) * acceptedLaw markSet := by
      apply tsum_congr
      exact hpiece_factor
    _ = (∑' n : indices, nu (indexPieces n)) * acceptedLaw markSet := by
      exact ENNReal.tsum_mul_right
    _ = nu ((firstAcceptedIndex sigma) ⁻¹' indexSet) * acceptedLaw markSet := by
      rw [hindex_measure]
    _ = nu ((firstAcceptedIndex sigma) ⁻¹' indexSet) *
        nu ((firstAcceptedTripMark sigma) ⁻¹' markSet) := by
      rw [measure_firstAcceptedTripMark_preimage_eq_cond mu sigma hsigma hmass markSet hmarkSet]


/-- The first accepted raw request index is a literal observable of a GN21
raw cycle seed. -/
noncomputable def gn21RawFirstAcceptedIndex
    (state : Fin 2) (sigma : TripPolicy) : GN21RawCycleSeed -> Nat :=
  fun seed => firstAcceptedIndex sigma (fun n => gn21RawCycleMark state n seed)

/-- The first accepted raw trip mark is a literal observable of a GN21 raw
cycle seed. -/
noncomputable def gn21RawFirstAcceptedTripMark
    (state : Fin 2) (sigma : TripPolicy) : GN21RawCycleSeed -> TripLength :=
  fun seed => firstAcceptedTripMark sigma (fun n => gn21RawCycleMark state n seed)

/-- The uninspected continuous raw-mark tail after the literal first accepted
GN21 request. -/
noncomputable def gn21RawFirstAcceptedTripTail
    (state : Fin 2) (sigma : TripPolicy) : GN21RawCycleSeed -> Nat -> TripLength :=
  fun seed => firstAcceptedTripTail sigma (fun n => gn21RawCycleMark state n seed)

/-- Transport the raw IID first-accepted-mark result through the actual GN21
raw cycle-seed product measure.  This removes the conditional accepted-mark
law as a caller-supplied post-thinning input. -/
theorem gn21RawFirstAcceptedTripMark_hasLaw
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    HasLaw (gn21RawFirstAcceptedTripMark state sigma)
      (gn21AcceptedTripLaw (gn21CycleMarkLaw muI muJ state) sigma)
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  let M := gn21CycleMarkLaw muI muJ state
  have hM_prob : IsProbabilityMeasure M := by
    dsimp [M, gn21CycleMarkLaw]
    fin_cases state <;> infer_instance
  letI : IsProbabilityMeasure M := hM_prob
  have hselected : HasLaw (firstAcceptedTripMark sigma)
      (gn21AcceptedTripLaw M sigma) (IIDStream.measure M) :=
    firstAcceptedTripMark_hasLaw M sigma hsigma (by simpa [M] using hmass)
  have hraw := gn21RawCycleMarkStream_hasLaw muI muJ arrivalI arrivalJ
    switchIJ switchJI harrivalI harrivalJ hswitchIJ hswitchJI state
  change HasLaw
    (firstAcceptedTripMark sigma ∘ fun seed : GN21RawCycleSeed => seed.2 state)
    (gn21AcceptedTripLaw M sigma)
    (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)
  simpa [M, gn21RawFirstAcceptedTripMark, gn21RawCycleMark, Function.comp_def] using
    hselected.comp hraw

/-- The literal continuous mark tail after the first accepted GN21 request
has the original source iid mark-stream law. -/
theorem gn21RawFirstAcceptedTripTail_hasLaw
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    HasLaw (gn21RawFirstAcceptedTripTail state sigma)
      (IIDStream.measure (gn21CycleMarkLaw muI muJ state))
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  let M := gn21CycleMarkLaw muI muJ state
  have hM_prob : IsProbabilityMeasure M := by
    dsimp [M, gn21CycleMarkLaw]
    fin_cases state <;> infer_instance
  letI : IsProbabilityMeasure M := hM_prob
  have htail : HasLaw (firstAcceptedTripTail sigma) (IIDStream.measure M)
      (IIDStream.measure M) :=
    firstAcceptedTripTail_hasLaw M sigma hsigma (by simpa [M] using hmass)
  have hraw := gn21RawCycleMarkStream_hasLaw muI muJ arrivalI arrivalJ
    switchIJ switchJI harrivalI harrivalJ hswitchIJ hswitchJI state
  change HasLaw
    (firstAcceptedTripTail sigma ∘ fun seed : GN21RawCycleSeed => seed.2 state)
    (IIDStream.measure M)
    (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)
  simpa [M, gn21RawFirstAcceptedTripTail, gn21RawCycleMark, Function.comp_def] using
    htail.comp hraw

/-- The literal GN21 stopped index and continuous selected mark factor from
the complete uninspected continuous mark tail.  The first factor remains its
actual pushforward law, so this theorem does not hide a resampled trip mark. -/
theorem gn21RawFirstAcceptedIndexTripMarkTail_hasLaw
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    HasLaw
      (fun seed =>
        ((gn21RawFirstAcceptedIndex state sigma seed,
          gn21RawFirstAcceptedTripMark state sigma seed),
          gn21RawFirstAcceptedTripTail state sigma seed))
      ((Measure.map
        (fun marks : Nat -> TripLength =>
          (firstAcceptedIndex sigma marks, firstAcceptedTripMark sigma marks))
        (IIDStream.measure (gn21CycleMarkLaw muI muJ state))).prod
        (IIDStream.measure (gn21CycleMarkLaw muI muJ state)))
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  let M := gn21CycleMarkLaw muI muJ state
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let rawMarks : GN21RawCycleSeed -> Nat -> TripLength :=
    fun seed n => gn21RawCycleMark state n seed
  let f : (Nat -> TripLength) -> Nat × TripLength := fun marks =>
    (firstAcceptedIndex sigma marks, firstAcceptedTripMark sigma marks)
  let tail : (Nat -> TripLength) -> Nat -> TripLength := firstAcceptedTripTail sigma
  have hM_prob : IsProbabilityMeasure M := by
    dsimp [M, gn21CycleMarkLaw]
    fin_cases state <;> infer_instance
  letI : IsProbabilityMeasure M := hM_prob
  letI : IsProbabilityMeasure (IIDStream.measure M) := by
    dsimp [IIDStream.measure]
    infer_instance
  have hraw : HasLaw rawMarks (IIDStream.measure M) P := by
    simpa [rawMarks, P, M, gn21RawCycleMark] using
      (gn21RawCycleMarkStream_hasLaw muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI state)
  have hf : Measurable f := by
    exact (measurable_firstAcceptedIndex sigma hsigma).prodMk
      (measurable_firstAcceptedTripMark sigma hsigma)
  have htail : HasLaw tail (IIDStream.measure M) (IIDStream.measure M) := by
    simpa [tail] using firstAcceptedTripTail_hasLaw M sigma hsigma
      (by simpa [M] using hmass)
  have hindep : IndepFun f tail (IIDStream.measure M) := by
    simpa [f, tail] using indepFun_firstAcceptedIndex_firstAcceptedTripMark_postTail
      M sigma hsigma (by simpa [M] using hmass)
  have hpair : HasLaw (fun marks => (f marks, tail marks))
      ((Measure.map f (IIDStream.measure M)).prod (IIDStream.measure M))
      (IIDStream.measure M) := by
    refine ⟨(hf.prodMk (measurable_firstAcceptedTripTail sigma hsigma)).aemeasurable, ?_⟩
    rw [(indepFun_iff_map_prod_eq_prod_map_map hf.aemeasurable
      (measurable_firstAcceptedTripTail sigma hsigma).aemeasurable).mp hindep,
      htail.map_eq]
  change HasLaw (fun seed => (f (rawMarks seed), tail (rawMarks seed)))
    ((Measure.map f (IIDStream.measure M)).prod (IIDStream.measure M)) P
  simpa [P, M, rawMarks, f, tail, gn21RawFirstAcceptedIndex,
    gn21RawFirstAcceptedTripMark, gn21RawFirstAcceptedTripTail, gn21RawCycleMark,
    Function.comp_def] using hpair.comp hraw

/-- On the literal GN21 raw product seed, the first accepted request index is
independent of the selected conditional trip mark.  The proof transports the
IID marked-selection theorem through the actual source mark-stream map; it
does not introduce a separately sampled accepted-trip mark. -/
theorem indepFun_gn21RawFirstAcceptedIndex_firstAcceptedTripMark
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    ProbabilityTheory.IndepFun (gn21RawFirstAcceptedIndex state sigma)
      (gn21RawFirstAcceptedTripMark state sigma)
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  let M := gn21CycleMarkLaw muI muJ state
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let rawMarks : GN21RawCycleSeed -> Nat -> TripLength :=
    fun seed n => gn21RawCycleMark state n seed
  let index := firstAcceptedIndex sigma
  let mark := firstAcceptedTripMark sigma
  have hM_prob : IsProbabilityMeasure M := by
    dsimp [M, gn21CycleMarkLaw]
    fin_cases state <;> infer_instance
  letI : IsProbabilityMeasure M := hM_prob
  letI : IsProbabilityMeasure P := by
    simpa [P] using isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  letI : IsProbabilityMeasure (IIDStream.measure M) := by
    dsimp [IIDStream.measure]
    infer_instance
  have hrawMeas : Measurable rawMarks := by
    apply measurable_pi_lambda
    intro n
    exact ((measurable_pi_apply n).comp
      ((measurable_pi_apply state).comp measurable_snd))
  have hraw : HasLaw rawMarks (IIDStream.measure M) P := by
    simpa [rawMarks, P, M, gn21RawCycleMark] using
      (gn21RawCycleMarkStream_hasLaw muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI state)
  have hindex : Measurable index := by
    simpa [index] using measurable_firstAcceptedIndex sigma hsigma
  have hmark : Measurable mark := by
    simpa [mark] using measurable_firstAcceptedTripMark sigma hsigma
  have hindep : ProbabilityTheory.IndepFun index mark (IIDStream.measure M) := by
    simpa [index, mark, M] using
      (indepFun_firstAcceptedIndex_firstAcceptedTripMark M sigma hsigma
        (by simpa [M] using hmass))
  apply (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
    (hindex.comp hrawMeas).aemeasurable
    (hmark.comp hrawMeas).aemeasurable).mpr
  change P.map (fun seed => (index (rawMarks seed), mark (rawMarks seed))) =
    (P.map (fun seed => index (rawMarks seed))).prod
      (P.map (fun seed => mark (rawMarks seed)))
  calc
    P.map (fun seed => (index (rawMarks seed), mark (rawMarks seed))) =
        (P.map rawMarks).map (fun marks => (index marks, mark marks)) := by
          rw [Measure.map_map (hindex.prodMk hmark) hrawMeas]
          rfl
    _ = (IIDStream.measure M).map (fun marks => (index marks, mark marks)) := by
      rw [hraw.map_eq]
    _ = ((IIDStream.measure M).map index).prod ((IIDStream.measure M).map mark) := by
      exact (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
        hindex.aemeasurable hmark.aemeasurable).mp hindep
    _ = ((P.map rawMarks).map index).prod ((P.map rawMarks).map mark) := by
      rw [hraw.map_eq]
    _ = (P.map (fun seed => index (rawMarks seed))).prod
        (P.map (fun seed => mark (rawMarks seed))) := by
      rw [Measure.map_map hindex hrawMeas,
        Measure.map_map hmark hrawMeas]
      rfl

end AcceptedTripSelection

end

end GN21DriverSurgePricing
