import AppliedModelingLib.Foundations.Probability.PoissonSuspensionBaseArrivals

/-!
# Verified marked transport for the Poisson suspension

This module proves the remaining marked unit-window transport identity for
the stationary Poisson suspension.  Fixed reindexing maps each raw source
branch to a disjoint Palm-gap interval; those intervals tile one unit phase
strip, whose mass is exactly the Palm tagged-arrival law.

It establishes a Campbell/Palm certificate only.  PASTA and queue-state
claims require their own separate hypotheses and theorems.
-/

namespace AppliedModelingLib.Probability.PoissonProcess

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

noncomputable section

/-- The raw selected-arrival event before intersecting with the full-measure
good carrier. -/
def rawMarkedSelection (s : Set (ℤ → ℝ)) (i : ℤ) :
    Set ((ℤ → ℝ) × ℝ) :=
  {p | 0 ≤ candidatePalmArrival p.1 i - p.2 ∧
    candidatePalmArrival p.1 i - p.2 < 1 ∧ suspensionGapShift i p.1 ∈ s}

def rawMarkedTransportSource (s : Set (ℤ → ℝ)) (i : ℤ) :
    Set ((ℤ → ℝ) × ℝ) :=
  rawGoodCarrier ∩ rawMarkedSelection s i

theorem measurableSet_rawMarkedSelection
    (s : Set (ℤ → ℝ)) (hs : MeasurableSet s) (i : ℤ) :
    MeasurableSet (rawMarkedSelection s i) := by
  have hzero : MeasurableSet {p : (ℤ → ℝ) × ℝ |
      (0 : ℝ) ≤ candidatePalmArrival p.1 i - p.2} :=
    measurableSet_le measurable_const
      (((measurable_candidatePalmArrival i).comp measurable_fst).sub measurable_snd)
  have hone : MeasurableSet {p : (ℤ → ℝ) × ℝ |
      candidatePalmArrival p.1 i - p.2 < (1 : ℝ)} :=
    measurableSet_lt
      (((measurable_candidatePalmArrival i).comp measurable_fst).sub measurable_snd)
      measurable_const
  have hmark : MeasurableSet {p : (ℤ → ℝ) × ℝ |
      suspensionGapShift i p.1 ∈ s} :=
    ((measurable_suspensionGapShift i).comp measurable_fst) hs
  exact hzero.inter (hone.inter hmark)

theorem suspensionMarkedUnitSummand_eq_indicator
    (s : Set (ℤ → ℝ)) (i : ℤ) :
    suspensionMarkedUnitSummand s i =
      (rawMarkedSelection s i).indicator (fun _ => (1 : ℝ≥0∞)) := by
  classical
  funext p
  unfold suspensionMarkedUnitSummand
  rw [Set.indicator_apply]
  congr 1

/-- The \(i\)-th source branch becomes the \((-i)\)-th Palm gap interval after
the fixed reindexing.  The time selection \([0,1)\) becomes \((-1,0]\). -/
def rawMarkedTransportTarget (s : Set (ℤ → ℝ)) (i : ℤ) :
    Set ((ℤ → ℝ) × ℝ) :=
  {q | suspensionGoodGapPath q.1 ∧ q.1 ∈ s ∧
    -1 < q.2 ∧ q.2 ≤ 0 ∧
    candidatePalmArrival q.1 (-i) ≤ q.2 ∧
    q.2 < candidatePalmArrival q.1 (-i + 1)}

theorem suspensionFixedIndexFlow_zero_mem_rawMarkedTransportTarget
    (s : Set (ℤ → ℝ)) (i : ℤ) (p : (ℤ → ℝ) × ℝ)
    (hp : p ∈ rawMarkedTransportSource s i) :
    suspensionFixedIndexFlow 0 i p ∈ rawMarkedTransportTarget s i := by
  rcases p with ⟨ω, u⟩
  rcases hp with ⟨⟨hcarrier, hgood⟩, hzero, hone, hmark⟩
  simp only [rawMarkedTransportTarget, Set.mem_setOf_eq,
    suspensionFixedIndexFlow, add_zero]
  refine ⟨suspensionGoodGapPath_shift ω hgood i, hmark, ?_, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · rw [candidatePalmArrival_suspensionGapShift]
    have hzeroArrival : candidatePalmArrival ω 0 = 0 := candidatePalmArrival_zero ω
    rw [show i + -i = 0 by ring, hzeroArrival]
    linarith [hcarrier.1]
  · rw [candidatePalmArrival_suspensionGapShift]
    have honeArrival : candidatePalmArrival ω 1 = twoSidedGap 0 ω := by
      simp [candidatePalmArrival, twoSidedGap]
    rw [show i + (-i + 1) = 1 by ring, honeArrival]
    linarith [hcarrier.2]

theorem rawMarkedTransportSource_mem_of_target
    (s : Set (ℤ → ℝ)) (i : ℤ) (q : (ℤ → ℝ) × ℝ)
    (hq : q ∈ rawMarkedTransportTarget s i) :
    suspensionFixedIndexFlow 0 (-i) q ∈ rawMarkedTransportSource s i := by
  rcases q with ⟨η, v⟩
  rcases hq with ⟨hgood, hmark, hminusone, hvzero, hleft, hright⟩
  have hshiftgood : suspensionGoodGapPath (suspensionGapShift (-i) η) :=
    suspensionGoodGapPath_shift η hgood (-i)
  simp only [rawMarkedTransportSource,
    suspensionFixedIndexFlow, add_zero]
  change (suspensionGapShift (-i) η,
      v - candidatePalmArrival η (-i)) ∈ rawGoodCarrier ∧
    0 ≤ candidatePalmArrival (suspensionGapShift (-i) η) i -
      (v - candidatePalmArrival η (-i)) ∧
    candidatePalmArrival (suspensionGapShift (-i) η) i -
      (v - candidatePalmArrival η (-i)) < 1 ∧
    suspensionGapShift i (suspensionGapShift (-i) η) ∈ s
  refine ⟨?_, ?_, ?_, ?_⟩
  · constructor
    · change 0 ≤ v - candidatePalmArrival η (-i) ∧
        v - candidatePalmArrival η (-i) <
          twoSidedGap 0 (suspensionGapShift (-i) η)
      constructor
      · linarith
      · have hgap : twoSidedGap 0 (suspensionGapShift (-i) η) =
            twoSidedGap (-i) η := by
          simp [suspensionGapShift, twoSidedGap]
        rw [hgap]
        rw [candidatePalmArrival_add_one] at hright
        change v - candidatePalmArrival η (-i) < η (-i)
        change v < candidatePalmArrival η (-i) + η (-i) at hright
        linarith
    · exact hshiftgood
  · rw [candidatePalmArrival_suspensionGapShift]
    have hzeroArrival : candidatePalmArrival η 0 = 0 := candidatePalmArrival_zero η
    rw [show -i + i = 0 by ring, hzeroArrival]
    linarith
  · rw [candidatePalmArrival_suspensionGapShift]
    have hzeroArrival : candidatePalmArrival η 0 = 0 := candidatePalmArrival_zero η
    rw [show -i + i = 0 by ring, hzeroArrival]
    linarith
  · rw [suspensionGapShift_comp]
    rw [show i + -i = 0 by ring]
    have hzeroShift : suspensionGapShift 0 η = η := by
      funext j
      simp [suspensionGapShift, twoSidedGap]
    rw [hzeroShift]
    exact hmark

theorem rawMarkedTransport_fixedIndex_image_eq
    (s : Set (ℤ → ℝ)) (i : ℤ) :
    suspensionFixedIndexFlow 0 i '' rawMarkedTransportSource s i =
      rawMarkedTransportTarget s i := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact suspensionFixedIndexFlow_zero_mem_rawMarkedTransportTarget s i p hp
  · intro hq
    let p := suspensionFixedIndexFlow 0 (-i) q
    have hp : p ∈ rawMarkedTransportSource s i := by
      exact rawMarkedTransportSource_mem_of_target s i q hq
    refine ⟨p, hp, ?_⟩
    simpa [p] using suspensionFixedIndexFlow_comp_neg 0 i q

/-- The common strip tiled by the fixed-index target branches. -/
def rawMarkedTransportStrip (s : Set (ℤ → ℝ)) : Set ((ℤ → ℝ) × ℝ) :=
  {q | suspensionGoodGapPath q.1 ∧ q.1 ∈ s ∧ -1 < q.2 ∧ q.2 ≤ 0}

theorem measurableSet_rawMarkedTransportSource
    (s : Set (ℤ → ℝ)) (hs : MeasurableSet s) (i : ℤ) :
    MeasurableSet (rawMarkedTransportSource s i) := by
  exact measurableSet_rawGoodCarrier.inter
    (measurableSet_rawMarkedSelection s hs i)

theorem lintegral_suspensionMarkedUnitSummand_eq_rate_mul_source
    {rate : ℝ} (hrate : 0 < rate) (s : Set (ℤ → ℝ))
    (hs : MeasurableSet s) (i : ℤ) :
    ∫⁻ p, suspensionMarkedUnitSummand s i p ∂suspensionMeasure rate =
      ENNReal.ofReal rate *
        ((twoSidedInterarrivalMeasure rate).prod volume)
          (rawMarkedTransportSource s i) := by
  rw [suspensionMarkedUnitSummand_eq_indicator]
  change ∫⁻ p, (rawMarkedSelection s i).indicator
      (1 : ((ℤ → ℝ) × ℝ) → ℝ≥0∞) p ∂suspensionMeasure rate = _
  rw [MeasureTheory.lintegral_indicator_one
    (measurableSet_rawMarkedSelection s hs i)]
  let μ : Measure ((ℤ → ℝ) × ℝ) :=
    (twoSidedInterarrivalMeasure rate).prod (volume : Measure ℝ)
  have hrestrict : μ.restrict rawGoodCarrier = μ.restrict suspensionCarrier :=
    Measure.restrict_congr_set (rawGoodCarrier_ae_eq_suspensionCarrier hrate)
  change (ENNReal.ofReal rate • μ.restrict suspensionCarrier)
      (rawMarkedSelection s i) = _
  rw [← hrestrict]
  rw [Measure.smul_apply, smul_eq_mul]
  rw [Measure.restrict_apply (measurableSet_rawMarkedSelection s hs i)]
  have hsource : rawMarkedSelection s i ∩ rawGoodCarrier =
      rawMarkedTransportSource s i := by
    ext p
    simp [rawMarkedTransportSource, Set.inter_comm]
  rw [hsource]

theorem measurableSet_rawMarkedTransportTarget
    (s : Set (ℤ → ℝ)) (hs : MeasurableSet s) (i : ℤ) :
    MeasurableSet (rawMarkedTransportTarget s i) := by
  have hgood : MeasurableSet {q : (ℤ → ℝ) × ℝ |
      suspensionGoodGapPath q.1} :=
    measurableSet_suspensionGoodGapPath.preimage measurable_fst
  have hmark : MeasurableSet {q : (ℤ → ℝ) × ℝ | q.1 ∈ s} :=
    hs.preimage measurable_fst
  have hminusone : MeasurableSet {q : (ℤ → ℝ) × ℝ | (-1 : ℝ) < q.2} :=
    measurableSet_lt measurable_const measurable_snd
  have hzero : MeasurableSet {q : (ℤ → ℝ) × ℝ | q.2 ≤ (0 : ℝ)} :=
    measurableSet_le measurable_snd measurable_const
  have hleft : MeasurableSet {q : (ℤ → ℝ) × ℝ |
      candidatePalmArrival q.1 (-i) ≤ q.2} :=
    measurableSet_le ((measurable_candidatePalmArrival (-i)).comp measurable_fst)
      measurable_snd
  have hright : MeasurableSet {q : (ℤ → ℝ) × ℝ |
      q.2 < candidatePalmArrival q.1 (-i + 1)} :=
    measurableSet_lt measurable_snd
      ((measurable_candidatePalmArrival (-i + 1)).comp measurable_fst)
  exact hgood.inter (hmark.inter (hminusone.inter (hzero.inter (hleft.inter hright))))

theorem measurableSet_rawMarkedTransportStrip
    (s : Set (ℤ → ℝ)) (hs : MeasurableSet s) :
    MeasurableSet (rawMarkedTransportStrip s) := by
  have hgood : MeasurableSet {q : (ℤ → ℝ) × ℝ |
      suspensionGoodGapPath q.1} :=
    measurableSet_suspensionGoodGapPath.preimage measurable_fst
  have hmark : MeasurableSet {q : (ℤ → ℝ) × ℝ | q.1 ∈ s} :=
    hs.preimage measurable_fst
  have hminusone : MeasurableSet {q : (ℤ → ℝ) × ℝ | (-1 : ℝ) < q.2} :=
    measurableSet_lt measurable_const measurable_snd
  have hzero : MeasurableSet {q : (ℤ → ℝ) × ℝ | q.2 ≤ (0 : ℝ)} :=
    measurableSet_le measurable_snd measurable_const
  exact hgood.inter (hmark.inter (hminusone.inter hzero))

theorem suspensionFixedIndexFlow_zero_restrict_rawMarkedTransportSource_measurePreserving
    {rate : ℝ} (hrate : 0 < rate) (s : Set (ℤ → ℝ))
    (i : ℤ) :
    MeasurePreserving (suspensionFixedIndexFlow 0 i)
      (((twoSidedInterarrivalMeasure rate).prod volume).restrict
        (rawMarkedTransportSource s i))
      (((twoSidedInterarrivalMeasure rate).prod volume).restrict
        (rawMarkedTransportTarget s i)) := by
  have h := (suspensionFixedIndexFlow_measurePreserving hrate 0 i).restrict_image_emb
    (suspensionFixedIndexFlowEquiv 0 i).measurableEmbedding
      (rawMarkedTransportSource s i)
  rw [rawMarkedTransport_fixedIndex_image_eq] at h
  exact h

theorem measure_rawMarkedTransportSource_eq_target
    {rate : ℝ} (hrate : 0 < rate) (s : Set (ℤ → ℝ))
    (hs : MeasurableSet s) (i : ℤ) :
    ((twoSidedInterarrivalMeasure rate).prod volume)
        (rawMarkedTransportSource s i) =
      ((twoSidedInterarrivalMeasure rate).prod volume)
        (rawMarkedTransportTarget s i) := by
  let μ : Measure ((ℤ → ℝ) × ℝ) :=
    (twoSidedInterarrivalMeasure rate).prod (volume : Measure ℝ)
  let T := suspensionFixedIndexFlow 0 i
  have hmp :=
    suspensionFixedIndexFlow_zero_restrict_rawMarkedTransportSource_measurePreserving
      hrate s i
  change μ (rawMarkedTransportSource s i) = μ (rawMarkedTransportTarget s i)
  calc
    μ (rawMarkedTransportSource s i) =
        (μ.restrict (rawMarkedTransportSource s i)) Set.univ :=
      (Measure.restrict_apply_univ _).symm
    _ = (Measure.map T (μ.restrict (rawMarkedTransportSource s i))) Set.univ := by
      rw [Measure.map_apply (measurable_suspensionFixedIndexFlow 0 i)
        MeasurableSet.univ]
      simp
    _ = (μ.restrict (rawMarkedTransportTarget s i)) Set.univ := by
      rw [hmp.map_eq]
    _ = μ (rawMarkedTransportTarget s i) :=
      Measure.restrict_apply_univ _

theorem pairwiseDisjoint_rawMarkedTransportTarget (s : Set (ℤ → ℝ)) :
    Pairwise (Function.onFun Disjoint (rawMarkedTransportTarget s)) := by
  intro i j hij
  apply Set.disjoint_left.2
  intro q hqi hqj
  rcases hqi with ⟨hgood, _, _, _, hleft_i, hright_i⟩
  rcases hqj with ⟨_, _, _, _, hleft_j, hright_j⟩
  have hstrict : StrictMono (candidatePalmArrival q.1) :=
    suspensionGoodGapPath_strictMono q.1 hgood
  have hlabels : -i = -j :=
    candidatePalmArrival_interval_index_unique q.1 hstrict
      ⟨hleft_i, hright_i⟩ ⟨hleft_j, hright_j⟩
  apply hij
  linarith

theorem rawMarkedTransport_target_iUnion_eq
    (s : Set (ℤ → ℝ)) :
    ⋃ i : ℤ, rawMarkedTransportTarget s i = rawMarkedTransportStrip s := by
  ext q
  constructor
  · intro hq
    rcases Set.mem_iUnion.1 hq with ⟨i, hi⟩
    exact ⟨hi.1, hi.2.1, hi.2.2.1, hi.2.2.2.1⟩
  · rintro ⟨hgood, hmark, hminusone, hvzero⟩
    let k := suspensionCrossingIndexPastClosed q.2 (q.1, 0)
    have hinterval := suspensionCrossingIndexPastClosed_interval q.1
      (suspensionGoodGapPath_future q.1 hgood)
      (suspensionGoodGapPath_past q.1 hgood) 0 q.2
    have hinterval' : candidatePalmArrival q.1 k ≤ q.2 ∧
        q.2 < candidatePalmArrival q.1 (k + 1) := by
      simpa only [k, zero_add] using hinterval
    refine Set.mem_iUnion.2 ⟨-k, ?_⟩
    refine ⟨hgood, hmark, hminusone, hvzero, ?_, ?_⟩
    · simpa only [neg_neg] using hinterval'.1
    · have hindex : -(-k) + 1 = k + 1 := by ring
      rw [hindex]
      simpa only [neg_neg] using hinterval'.2

theorem restrict_rawMarkedTransportStrip_eq_sum_targets
    {rate : ℝ} (s : Set (ℤ → ℝ)) (hs : MeasurableSet s) :
    ((twoSidedInterarrivalMeasure rate).prod volume).restrict
      (rawMarkedTransportStrip s) =
      Measure.sum fun i : ℤ =>
        ((twoSidedInterarrivalMeasure rate).prod volume).restrict
          (rawMarkedTransportTarget s i) := by
  rw [← rawMarkedTransport_target_iUnion_eq]
  exact Measure.restrict_iUnion_ae
    (fun i j hij => (pairwiseDisjoint_rawMarkedTransportTarget s hij).aedisjoint)
    (fun i => (measurableSet_rawMarkedTransportTarget s hs i).nullMeasurableSet)

theorem tsum_measure_rawMarkedTransportTarget_eq_strip
    {rate : ℝ} (s : Set (ℤ → ℝ)) (hs : MeasurableSet s) :
    ∑' i : ℤ, ((twoSidedInterarrivalMeasure rate).prod volume)
      (rawMarkedTransportTarget s i) =
      ((twoSidedInterarrivalMeasure rate).prod volume)
        (rawMarkedTransportStrip s) := by
  let μ : Measure ((ℤ → ℝ) × ℝ) :=
    (twoSidedInterarrivalMeasure rate).prod (volume : Measure ℝ)
  change ∑' i : ℤ, μ (rawMarkedTransportTarget s i) =
    μ (rawMarkedTransportStrip s)
  calc
    ∑' i : ℤ, μ (rawMarkedTransportTarget s i) =
        (Measure.sum fun i : ℤ => μ.restrict
          (rawMarkedTransportTarget s i)) Set.univ := by
          symm
          rw [Measure.sum_apply
            (fun i : ℤ => μ.restrict (rawMarkedTransportTarget s i))
            MeasurableSet.univ]
          simp only [Measure.restrict_apply_univ]
    _ = (μ.restrict (rawMarkedTransportStrip s)) Set.univ := by
      rw [restrict_rawMarkedTransportStrip_eq_sum_targets s hs]
    _ = μ (rawMarkedTransportStrip s) := Measure.restrict_apply_univ _

/-- The common raw target strip has exactly the tagged Palm-gap mass of its
mark.  Its phase fibre is the unit interval \((-1, 0]\); the good-path factor
can be removed by the full-measure nonexplosion/positivity carrier. -/
theorem measure_rawMarkedTransportStrip_eq_twoSidedInterarrivalMeasure
    {rate : ℝ} (hrate : 0 < rate) (s : Set (ℤ → ℝ))
    (hs : MeasurableSet s) :
    ((twoSidedInterarrivalMeasure rate).prod volume)
      (rawMarkedTransportStrip s) =
      twoSidedInterarrivalMeasure rate s := by
  classical
  let G : Set (ℤ → ℝ) := {ω | suspensionGoodGapPath ω}
  have hG : MeasurableSet G := measurableSet_suspensionGoodGapPath
  have hGs : MeasurableSet (G ∩ s) := hG.inter hs
  have hstrip : rawMarkedTransportStrip s =
      (G ∩ s) ×ˢ Set.Ioc (-1 : ℝ) 0 := by
    ext q
    rcases q with ⟨ω, u⟩
    simp only [rawMarkedTransportStrip, Set.mem_setOf_eq, Set.mem_prod,
      Set.mem_inter_iff, Set.mem_Ioc]
    simp [G, and_assoc]
  have hphase : volume (Set.Ioc (-1 : ℝ) 0) = 1 := by
    norm_num [Real.volume_Ioc]
  rw [hstrip, Measure.prod_prod, hphase, mul_one]
  apply MeasureTheory.measure_congr
  filter_upwards [ae_suspensionGoodGapPath hrate] with ω hω
  apply propext
  change (suspensionGoodGapPath ω ∧ ω ∈ s) ↔ ω ∈ s
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨hω, h⟩

/-- The preceding strip identity in the literal \(Ptag\) notation used by the
Campbell certificate. -/
theorem measure_rawMarkedTransportStrip_eq_candidateTaggedArrivalAtZero
    {rate : ℝ} (hrate : 0 < rate) (s : Set (ℤ → ℝ))
    (hs : MeasurableSet s) :
    ((twoSidedInterarrivalMeasure rate).prod volume)
      (rawMarkedTransportStrip s) =
      (candidateTaggedArrivalAtZero rate hrate).Ptag s := by
  simpa [candidateTaggedArrivalAtZero] using
    (measure_rawMarkedTransportStrip_eq_twoSidedInterarrivalMeasure hrate s hs)

/-- The fixed-index branch maps transport the full marked unit-window
Campbell sum to the unit phase strip, proving the raw transport premise used
by the good-suspension Campbell certificate. -/
theorem hasSuspensionMarkedUnitTransport
    {rate : ℝ} (hrate : 0 < rate) :
    HasSuspensionMarkedUnitTransport rate := by
  intro s hs
  calc
    ∑' i : ℤ, ∫⁻ p, suspensionMarkedUnitSummand s i p
        ∂suspensionMeasure rate =
      ∑' i : ℤ, ENNReal.ofReal rate *
        ((twoSidedInterarrivalMeasure rate).prod volume)
          (rawMarkedTransportSource s i) := by
          apply tsum_congr
          intro i
          exact lintegral_suspensionMarkedUnitSummand_eq_rate_mul_source
            hrate s hs i
    _ = ENNReal.ofReal rate * ∑' i : ℤ,
        ((twoSidedInterarrivalMeasure rate).prod volume)
          (rawMarkedTransportSource s i) := ENNReal.tsum_mul_left
    _ = ENNReal.ofReal rate * ∑' i : ℤ,
        ((twoSidedInterarrivalMeasure rate).prod volume)
          (rawMarkedTransportTarget s i) := by
          congr 1
          apply tsum_congr
          intro i
          rw [measure_rawMarkedTransportSource_eq_target hrate s hs i]
    _ = ENNReal.ofReal rate *
        ((twoSidedInterarrivalMeasure rate).prod volume)
          (rawMarkedTransportStrip s) := by
          rw [tsum_measure_rawMarkedTransportTarget_eq_strip s hs]
    _ = ENNReal.ofReal rate * twoSidedInterarrivalMeasure rate s := by
          rw [measure_rawMarkedTransportStrip_eq_twoSidedInterarrivalMeasure hrate s hs]

/-- The fully verified stationary Campbell/Palm certificate for the Poisson
suspension.  It certifies marked unit-window Campbell transport, not PASTA or
any queue-state equality. -/
noncomputable def poissonSuspensionCampbellCertificate
    {rate : ℝ} (hrate : 0 < rate) :
    Palm.CampbellPalmTaggedArrivalCertificate
      (goodSuspensionShiftInvariantLaw hrate)
      (candidateTaggedArrivalAtZero rate hrate) :=
  goodSuspensionCampbellCertificate_of_transport hrate
    (hasSuspensionMarkedUnitTransport hrate)

end

end AppliedModelingLib.Probability.PoissonProcess
