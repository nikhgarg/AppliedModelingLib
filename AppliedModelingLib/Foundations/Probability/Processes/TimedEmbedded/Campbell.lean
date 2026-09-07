import AppliedModelingLib.Foundations.Probability.Processes.Palm.SelectedMarkedTransport

namespace AppliedModelingLib.Probability.Queueing

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

noncomputable section

open PoissonProcess

variable {α : Type*} [MeasurableSpace α]

/-- The raw fixed-index summand for a timed embedded product. -/
noncomputable def timedEmbeddedRawSummand
    (s : Set ((ℤ → ℝ) × (ℤ → α))) (i : ℤ)
    (z : ((ℤ → ℝ) × ℝ) × (ℤ → α)) : ℝ≥0∞ := by
  classical
  exact if 0 ≤ candidatePalmArrival z.1.1 i - z.1.2 ∧
      candidatePalmArrival z.1.1 i - z.1.2 < 1 ∧
      (suspensionGapShift i z.1.1, intPathShift i z.2) ∈ s then 1 else 0

theorem measurable_timedEmbeddedRawSummand
    (s : Set ((ℤ → ℝ) × (ℤ → α))) (hs : MeasurableSet s) (i : ℤ) :
    Measurable (timedEmbeddedRawSummand (α := α) s i) := by
  classical
  have hleft : MeasurableSet {z : ((ℤ → ℝ) × ℝ) × (ℤ → α) |
      (0 : ℝ) ≤ candidatePalmArrival z.1.1 i - z.1.2} :=
    measurableSet_le measurable_const
      (((measurable_candidatePalmArrival i).comp
        (measurable_fst.comp measurable_fst)).sub
        (measurable_snd.comp measurable_fst))
  have hright : MeasurableSet {z : ((ℤ → ℝ) × ℝ) × (ℤ → α) |
      candidatePalmArrival z.1.1 i - z.1.2 < (1 : ℝ)} :=
    measurableSet_lt
      (((measurable_candidatePalmArrival i).comp
        (measurable_fst.comp measurable_fst)).sub
        (measurable_snd.comp measurable_fst)) measurable_const
  have hmark : MeasurableSet {z : ((ℤ → ℝ) × ℝ) × (ℤ → α) |
      (suspensionGapShift i z.1.1, intPathShift i z.2) ∈ s} :=
    (((measurable_suspensionGapShift i).comp
      (measurable_fst.comp measurable_fst)).prodMk
      ((measurable_intPathShift (α := α) i).comp measurable_snd)) hs
  change Measurable (fun z : ((ℤ → ℝ) × ℝ) × (ℤ → α) => if
      0 ≤ candidatePalmArrival z.1.1 i - z.1.2 ∧
        candidatePalmArrival z.1.1 i - z.1.2 < 1 ∧
        (suspensionGapShift i z.1.1, intPathShift i z.2) ∈ s
      then (1 : ℝ≥0∞) else 0)
  exact Measurable.ite (hleft.inter (hright.inter hmark))
    measurable_const measurable_const

/-- The gap section of a full tagged event at a fixed embedded path. -/
def timedEmbeddedGapSection
    (s : Set ((ℤ → ℝ) × (ℤ → α))) (x : ℤ → α) : Set (ℤ → ℝ) :=
  (fun g => (g, x)) ⁻¹' s

theorem measurableSet_timedEmbeddedGapSection
    (s : Set ((ℤ → ℝ) × (ℤ → α))) (hs : MeasurableSet s) (x : ℤ → α) :
    MeasurableSet (timedEmbeddedGapSection s x) := by
  exact measurable_prodMk_right hs

omit [MeasurableSpace α] in
theorem timedEmbeddedRawSummand_eq_suspensionSummand_section
    (s : Set ((ℤ → ℝ) × (ℤ → α))) (i : ℤ)
    (z : ((ℤ → ℝ) × ℝ) × (ℤ → α)) :
    timedEmbeddedRawSummand s i z =
      suspensionMarkedUnitSummand
        (timedEmbeddedGapSection s (intPathShift i z.2)) i z.1 := by
  unfold timedEmbeddedRawSummand timedEmbeddedGapSection suspensionMarkedUnitSummand
  rfl

/-- The same raw summand before the event-index reindexing of its path factor. -/
noncomputable def timedEmbeddedRawSectionSummand
    (s : Set ((ℤ → ℝ) × (ℤ → α))) (i : ℤ)
    (z : ((ℤ → ℝ) × ℝ) × (ℤ → α)) : ℝ≥0∞ :=
  suspensionMarkedUnitSummand (timedEmbeddedGapSection s z.2) i z.1

theorem measurable_timedEmbeddedRawSectionSummand
    (s : Set ((ℤ → ℝ) × (ℤ → α))) (hs : MeasurableSet s) (i : ℤ) :
    Measurable (timedEmbeddedRawSectionSummand (α := α) s i) := by
  classical
  have hleft : MeasurableSet {z : ((ℤ → ℝ) × ℝ) × (ℤ → α) |
      (0 : ℝ) ≤ candidatePalmArrival z.1.1 i - z.1.2} :=
    measurableSet_le measurable_const
      (((measurable_candidatePalmArrival i).comp
        (measurable_fst.comp measurable_fst)).sub
        (measurable_snd.comp measurable_fst))
  have hright : MeasurableSet {z : ((ℤ → ℝ) × ℝ) × (ℤ → α) |
      candidatePalmArrival z.1.1 i - z.1.2 < (1 : ℝ)} :=
    measurableSet_lt
      (((measurable_candidatePalmArrival i).comp
        (measurable_fst.comp measurable_fst)).sub
        (measurable_snd.comp measurable_fst)) measurable_const
  have hmark : MeasurableSet {z : ((ℤ → ℝ) × ℝ) × (ℤ → α) |
      (suspensionGapShift i z.1.1, z.2) ∈ s} :=
    (((measurable_suspensionGapShift i).comp
      (measurable_fst.comp measurable_fst)).prodMk measurable_snd) hs
  change Measurable (fun z : ((ℤ → ℝ) × ℝ) × (ℤ → α) => if
      0 ≤ candidatePalmArrival z.1.1 i - z.1.2 ∧
        candidatePalmArrival z.1.1 i - z.1.2 < 1 ∧
        (suspensionGapShift i z.1.1, z.2) ∈ s
      then (1 : ℝ≥0∞) else 0)
  exact Measurable.ite (hleft.inter (hright.inter hmark))
    measurable_const measurable_const

omit [MeasurableSpace α] in
theorem timedEmbeddedRawSummand_eq_sectionSummand_shift
    (s : Set ((ℤ → ℝ) × (ℤ → α))) (i : ℤ)
    (z : ((ℤ → ℝ) × ℝ) × (ℤ → α)) :
    timedEmbeddedRawSummand s i z =
      timedEmbeddedRawSectionSummand s i (z.1, intPathShift i z.2) := by
  unfold timedEmbeddedRawSummand timedEmbeddedRawSectionSummand
    timedEmbeddedGapSection suspensionMarkedUnitSummand
  rfl

theorem measurable_timedEmbeddedRawSectionIntegral
    {rate : ℝ} (hrate : 0 < rate)
    (s : Set ((ℤ → ℝ) × (ℤ → α))) (hs : MeasurableSet s) (i : ℤ) :
    Measurable (fun x : ℤ → α => ∫⁻ p,
      timedEmbeddedRawSectionSummand s i (p, x) ∂suspensionMeasure rate) := by
  letI : IsProbabilityMeasure (suspensionMeasure rate) :=
    isProbabilityMeasure_suspensionMeasure hrate
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure rate) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure hrate
  let f : ((ℤ → ℝ) × ℝ) → (ℤ → α) → ℝ≥0∞ := fun p x =>
    timedEmbeddedRawSectionSummand s i (p, x)
  have hf : Measurable (Function.uncurry f) := by
    simpa only [f, Function.uncurry] using
      (measurable_timedEmbeddedRawSectionSummand s hs i)
  exact hf.lintegral_prod_left

theorem lintegral_timedEmbeddedRawSummand_eq_section
    {rate : ℝ} (hrate : 0 < rate)
    (P : Measure (ℤ → α)) [IsProbabilityMeasure P]
    (hpath : ∀ k : ℤ, MeasurePreserving (intPathShift (α := α) k) P P)
    (s : Set ((ℤ → ℝ) × (ℤ → α))) (hs : MeasurableSet s) (i : ℤ) :
    ∫⁻ z, timedEmbeddedRawSummand s i z ∂(suspensionMeasure rate).prod P =
      ∫⁻ x, ∫⁻ p, timedEmbeddedRawSectionSummand s i (p, x)
        ∂suspensionMeasure rate ∂P := by
  letI : IsProbabilityMeasure (suspensionMeasure rate) :=
    isProbabilityMeasure_suspensionMeasure hrate
  rw [MeasureTheory.lintegral_prod_symm'
    (timedEmbeddedRawSummand (α := α) s i)
    (measurable_timedEmbeddedRawSummand s hs i)]
  calc
    (∫⁻ x, ∫⁻ p, timedEmbeddedRawSummand s i (p, x)
        ∂suspensionMeasure rate ∂P) =
      ∫⁻ x, ∫⁻ p, timedEmbeddedRawSectionSummand s i
        (p, intPathShift i x) ∂suspensionMeasure rate ∂P := by
          apply lintegral_congr
          intro x
          apply lintegral_congr
          intro p
          exact timedEmbeddedRawSummand_eq_sectionSummand_shift s i (p, x)
    _ = ∫⁻ x, (fun y : ℤ → α => ∫⁻ p,
        timedEmbeddedRawSectionSummand s i (p, y)
          ∂suspensionMeasure rate) (intPathShift i x) ∂P := rfl
    _ = ∫⁻ x, ∫⁻ p, timedEmbeddedRawSectionSummand s i (p, x)
        ∂suspensionMeasure rate ∂P :=
      (hpath i).lintegral_comp
        (measurable_timedEmbeddedRawSectionIntegral hrate s hs i)

/-- Independent integer-shift-invariant path marks lift the Poisson raw
Campbell transport to a full tagged gap/path event. -/
theorem timedEmbedded_rawProductCampbell_transport
    {rate : ℝ} (hrate : 0 < rate)
    (P : Measure (ℤ → α)) [IsProbabilityMeasure P]
    (hpath : ∀ k : ℤ, MeasurePreserving (intPathShift (α := α) k) P P)
    (s : Set ((ℤ → ℝ) × (ℤ → α))) (hs : MeasurableSet s) :
    ∑' i : ℤ, ∫⁻ z, timedEmbeddedRawSummand s i z
      ∂(suspensionMeasure rate).prod P =
      ENNReal.ofReal rate * ((twoSidedInterarrivalMeasure rate).prod P) s := by
  letI : IsProbabilityMeasure (suspensionMeasure rate) :=
    isProbabilityMeasure_suspensionMeasure hrate
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure rate) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure hrate
  calc
    ∑' i : ℤ, ∫⁻ z, timedEmbeddedRawSummand s i z
        ∂(suspensionMeasure rate).prod P =
      ∑' i : ℤ, ∫⁻ x, ∫⁻ p, timedEmbeddedRawSectionSummand s i (p, x)
        ∂suspensionMeasure rate ∂P := by
          apply tsum_congr
          intro i
          exact lintegral_timedEmbeddedRawSummand_eq_section hrate P hpath s hs i
    _ = ∫⁻ x, ∑' i : ℤ, ∫⁻ p, timedEmbeddedRawSectionSummand s i (p, x)
        ∂suspensionMeasure rate ∂P := by
          symm
          exact MeasureTheory.lintegral_tsum fun i =>
            (measurable_timedEmbeddedRawSectionIntegral hrate s hs i).aemeasurable
    _ = ∫⁻ x, ENNReal.ofReal rate *
        twoSidedInterarrivalMeasure rate (timedEmbeddedGapSection s x) ∂P := by
          apply lintegral_congr
          intro x
          exact hasSuspensionMarkedUnitTransport hrate
            (timedEmbeddedGapSection s x)
            (measurableSet_timedEmbeddedGapSection s hs x)
    _ = ENNReal.ofReal rate * ((twoSidedInterarrivalMeasure rate).prod P) s := by
          rw [lintegral_const_mul (ENNReal.ofReal rate)]
          · rw [Measure.prod_apply_symm hs]
            rfl
          · simpa only [timedEmbeddedGapSection] using
              (measurable_measure_prodMk_right hs)

/-- On the good suspension carrier, the full timed embedded Campbell count
is the finite sum of the raw fixed-index summands. -/
theorem timedEmbeddedUnitWindowCount_eq_sum_raw
    (s : Set ((ℤ → ℝ) × (ℤ → α))) (z : GoodSuspensionState × (ℤ → α)) :
    Palm.unitWindowCampbellCount timedEmbeddedArrivalIndices timedEmbeddedRecenterAt s z =
      (by
        classical
        exact ∑ i ∈ suspensionBaseArrivalIndices 0 1 z.1,
          if 0 ≤ suspensionBaseArrival z.1 i ∧
              suspensionBaseArrival z.1 i < 1 ∧
              (suspensionBaseRecenter z.1 i, intPathShift i z.2) ∈ s
            then 1 else 0) := by
  classical
  change ((suspensionBaseArrivalIndices 0 1 z.1).filter fun i =>
    (suspensionBaseRecenter z.1 i, intPathShift i z.2) ∈ s).card = _
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro i hi
  have hinterval : 0 ≤ suspensionBaseArrival z.1 i ∧
      suspensionBaseArrival z.1 i < 1 :=
    (mem_suspensionBaseArrivalIndices_iff 0 1 z.1 i).mp hi
  by_cases hmark : (suspensionBaseRecenter z.1 i, intPathShift i z.2) ∈ s
  · simp [hinterval, hmark]
  · simp [hinterval, hmark]

theorem timedEmbeddedUnitWindowCount_coe_eq_tsum_raw
    (s : Set ((ℤ → ℝ) × (ℤ → α))) (z : GoodSuspensionState × (ℤ → α)) :
    (Palm.unitWindowCampbellCount
      timedEmbeddedArrivalIndices timedEmbeddedRecenterAt s z : ℝ≥0∞) =
      ∑' i : ℤ, timedEmbeddedRawSummand s i (z.1.1, z.2) := by
  classical
  rw [timedEmbeddedUnitWindowCount_eq_sum_raw]
  rw [tsum_eq_sum (s := suspensionBaseArrivalIndices 0 1 z.1)]
  · simp only [timedEmbeddedRawSummand, suspensionBaseArrival,
      suspensionBaseRecenter]
    norm_cast
  · intro i hi
    have hnot : ¬ (0 ≤ suspensionBaseArrival z.1 i ∧
        suspensionBaseArrival z.1 i < 1) := by
      intro h
      exact hi ((mem_suspensionBaseArrivalIndices_iff 0 1 z.1 i).mpr h)
    change timedEmbeddedRawSummand s i (z.1.1, z.2) = 0
    unfold timedEmbeddedRawSummand
    have hnot' : ¬ (0 ≤ candidatePalmArrival z.1.1.1 i - z.1.1.2 ∧
        candidatePalmArrival z.1.1.1 i - z.1.1.2 < 1 ∧
        (suspensionGapShift i z.1.1.1, intPathShift i z.2) ∈ s) := by
      rintro ⟨hzero, hone, _⟩
      exact hnot ⟨hzero, hone⟩
    rw [if_neg hnot']

theorem map_goodSuspension_prod_path
    {rate : ℝ} (hrate : 0 < rate) (P : Measure (ℤ → α))
    [IsProbabilityMeasure P] :
    Measure.map (Prod.map (Subtype.val : GoodSuspensionState → ((ℤ → ℝ) × ℝ)) id)
      ((goodSuspensionMeasure rate).prod P) =
      (suspensionMeasure rate).prod P := by
  letI : IsProbabilityMeasure (goodSuspensionMeasure rate) :=
    isProbabilityMeasure_goodSuspensionMeasure hrate
  letI : SFinite (goodSuspensionMeasure rate) := by infer_instance
  letI : SFinite P := by infer_instance
  calc
    Measure.map (Prod.map (Subtype.val : GoodSuspensionState → ((ℤ → ℝ) × ℝ)) id)
        ((goodSuspensionMeasure rate).prod P) =
      (Measure.map (Subtype.val : GoodSuspensionState → ((ℤ → ℝ) × ℝ))
        (goodSuspensionMeasure rate)).prod (Measure.map id P) := by
          symm
          exact Measure.map_prod_map (goodSuspensionMeasure rate) P
            measurable_subtype_coe measurable_id
    _ = (suspensionMeasure rate).prod P := by
      rw [map_goodSuspensionMeasure_subtype_val hrate, Measure.map_id]

/-- The all-event Campbell identity for an independent, shift-invariant
embedded path factor, still expressed directly over the good suspension
product. -/
theorem timedEmbedded_goodProductCampbell_transport
    {rate : ℝ} (hrate : 0 < rate)
    (P : Measure (ℤ → α)) [IsProbabilityMeasure P]
    (hpath : ∀ k : ℤ, MeasurePreserving (intPathShift (α := α) k) P P)
    (s : Set ((ℤ → ℝ) × (ℤ → α))) (hs : MeasurableSet s) :
    ∫⁻ z, (Palm.unitWindowCampbellCount
      timedEmbeddedArrivalIndices timedEmbeddedRecenterAt s z : ℝ≥0∞)
      ∂(goodSuspensionMeasure rate).prod P =
      ENNReal.ofReal rate * ((twoSidedInterarrivalMeasure rate).prod P) s := by
  letI : IsProbabilityMeasure (goodSuspensionMeasure rate) :=
    isProbabilityMeasure_goodSuspensionMeasure hrate
  letI : IsProbabilityMeasure (suspensionMeasure rate) :=
    isProbabilityMeasure_suspensionMeasure hrate
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure rate) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure hrate
  let lift : (GoodSuspensionState × (ℤ → α)) →
      ((ℤ → ℝ) × ℝ) × (ℤ → α) :=
    Prod.map (Subtype.val : GoodSuspensionState → ((ℤ → ℝ) × ℝ)) id
  have hlift : Measurable lift := measurable_subtype_coe.prodMap measurable_id
  have hmp : MeasurePreserving lift
      ((goodSuspensionMeasure rate).prod P)
      ((suspensionMeasure rate).prod P) :=
    ⟨hlift, map_goodSuspension_prod_path hrate P⟩
  calc
    ∫⁻ z, (Palm.unitWindowCampbellCount
        timedEmbeddedArrivalIndices timedEmbeddedRecenterAt s z : ℝ≥0∞)
        ∂(goodSuspensionMeasure rate).prod P =
      ∫⁻ z, ∑' i : ℤ, timedEmbeddedRawSummand s i (lift z)
        ∂(goodSuspensionMeasure rate).prod P := by
          apply lintegral_congr
          intro z
          exact timedEmbeddedUnitWindowCount_coe_eq_tsum_raw s z
    _ = ∑' i : ℤ, ∫⁻ z, timedEmbeddedRawSummand s i (lift z)
        ∂(goodSuspensionMeasure rate).prod P := by
          exact MeasureTheory.lintegral_tsum fun i =>
            ((measurable_timedEmbeddedRawSummand s hs i).comp hlift).aemeasurable
    _ = ∑' i : ℤ, ∫⁻ z, timedEmbeddedRawSummand s i z
        ∂(suspensionMeasure rate).prod P := by
          apply tsum_congr
          intro i
          exact hmp.lintegral_comp (measurable_timedEmbeddedRawSummand s hs i)
    _ = ENNReal.ofReal rate * ((twoSidedInterarrivalMeasure rate).prod P) s :=
      timedEmbedded_rawProductCampbell_transport hrate P hpath s hs

/-- The preceding product transport in exactly the stationary-base and
tagged-arrival notation accepted by the timed embedded Campbell constructor. -/
theorem timedEmbedded_allEventCampbell_transport
    {rate : ℝ} (hrate : 0 < rate)
    (P : Measure (ℤ → α)) [IsProbabilityMeasure P]
    (hpath : ∀ k : ℤ, MeasurePreserving (intPathShift (α := α) k) P P)
    (s : Set ((ℤ → ℝ) × (ℤ → α))) (hs : MeasurableSet s) :
    ∫⁻ z, (Palm.unitWindowCampbellCount
      timedEmbeddedArrivalIndices timedEmbeddedRecenterAt s z : ℝ≥0∞) ∂
        (timedEmbeddedSuspensionShiftInvariantLaw_of_intPathShift
          hrate P hpath).Pbase =
      ENNReal.ofReal rate *
        (timedEmbeddedTaggedArrivalAtZero rate hrate P).Ptag s := by
  simpa only [timedEmbeddedSuspensionShiftInvariantLaw_of_intPathShift,
    timedEmbeddedSuspensionProductMeasure, timedEmbeddedTaggedArrivalAtZero,
    TaggedArrivalAtZero.Ptag, candidateTaggedArrivalAtZero] using
    (timedEmbedded_goodProductCampbell_transport hrate P hpath s hs)

/-- A genuine all-event Campbell/Palm certificate for a Poisson-suspended,
independent, integer-shift-invariant embedded path. -/
noncomputable def timedEmbeddedCampbellCertificate_of_independentPath
    {rate : ℝ} (hrate : 0 < rate)
    (P : Measure (ℤ → α)) [IsProbabilityMeasure P]
    (hpath : ∀ k : ℤ, MeasurePreserving (intPathShift (α := α) k) P P) :
    Palm.CampbellPalmTaggedArrivalCertificate
      (timedEmbeddedSuspensionShiftInvariantLaw_of_intPathShift hrate P hpath)
      (timedEmbeddedTaggedArrivalAtZero rate hrate P) :=
  timedEmbeddedCampbellCertificate_of_transport hrate P hpath P
    (fun s hs => timedEmbedded_allEventCampbell_transport hrate P hpath s hs)

theorem cond_prod_snd_eq_prod_cond
    {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    (G : Measure β) [IsProbabilityMeasure G]
    (P : Measure γ) [IsProbabilityMeasure P]
    (A : Set γ) :
    (G.prod P)[| Set.univ ×ˢ A] = G.prod (P[| A]) := by
  simp only [ProbabilityTheory.cond]
  rw [← Measure.prod_restrict, Measure.restrict_univ, Measure.prod_smul_right]
  simp [Measure.prod_prod, measure_univ]

variable {α : Type*} [MeasurableSpace α]

/-- A Boolean mark read from the coordinate at the tagged embedded origin. -/
def timedEmbeddedTaggedPathZeroMark (m : α → Bool) :
    ((ℤ → ℝ) × (ℤ → α)) → Bool :=
  fun z => m (z.2 0)

/-- The corresponding true-mark slice of an embedded path law. -/
def timedEmbeddedPathZeroTrueSet (m : α → Bool) : Set (ℤ → α) :=
  {x | m (x 0) = true}

theorem measurable_timedEmbeddedTaggedPathZeroMark
    (m : α → Bool) (hm : Measurable m) :
    Measurable (timedEmbeddedTaggedPathZeroMark m) :=
  hm.comp ((measurable_pi_apply 0).comp measurable_snd)

theorem measurableSet_timedEmbeddedPathZeroTrueSet
    (m : α → Bool) (hm : Measurable m) :
    MeasurableSet (timedEmbeddedPathZeroTrueSet m) := by
  exact (measurableSet_singleton true).preimage
    (hm.comp (measurable_pi_apply 0))

omit [MeasurableSpace α] in
theorem timedEmbeddedTaggedPathZeroMark_true_preimage
    (m : α → Bool) :
    (timedEmbeddedTaggedPathZeroMark m) ⁻¹' ({true} : Set Bool) =
      Set.univ ×ˢ timedEmbeddedPathZeroTrueSet m := by
  ext z
  simp [timedEmbeddedTaggedPathZeroMark, timedEmbeddedPathZeroTrueSet]

theorem measure_timedEmbeddedTaggedPathZeroMark_true
    {rate : ℝ} (hrate : 0 < rate)
    (P : Measure (ℤ → α)) [IsProbabilityMeasure P]
    (m : α → Bool) :
    (timedEmbeddedTaggedArrivalAtZero rate hrate P).Ptag
      ((timedEmbeddedTaggedPathZeroMark m) ⁻¹' ({true} : Set Bool)) =
      P (timedEmbeddedPathZeroTrueSet m) := by
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure rate) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure hrate
  change ((twoSidedInterarrivalMeasure rate).prod P)
      ((timedEmbeddedTaggedPathZeroMark m) ⁻¹' ({true} : Set Bool)) = _
  rw [timedEmbeddedTaggedPathZeroMark_true_preimage, Measure.prod_prod,
    measure_univ, one_mul]

/-- The full tagged gap/path law after conditioning only its embedded path
factor on a true coordinate-zero mark. -/
noncomputable def timedEmbeddedTaggedArrivalAtZero_conditionedOnPathZeroTrue
    {rate : ℝ} (hrate : 0 < rate)
    (P : Measure (ℤ → α)) [IsProbabilityMeasure P]
    (m : α → Bool)
    (htrue : P (timedEmbeddedPathZeroTrueSet m) ≠ 0) :
    TaggedArrivalAtZero ((ℤ → ℝ) × (ℤ → α)) := by
  letI : IsProbabilityMeasure (P[| timedEmbeddedPathZeroTrueSet m]) :=
    ProbabilityTheory.cond_isProbabilityMeasure htrue
  exact timedEmbeddedTaggedArrivalAtZero rate hrate
    (P[| timedEmbeddedPathZeroTrueSet m])

/-- Conditioning the full tagged product on a true zero-coordinate mark is
exactly the product with its path factor conditioned on that mark. -/
theorem timedEmbeddedTaggedArrivalAtZero_conditionOnPathZeroTrue_Ptag
    {rate : ℝ} (hrate : 0 < rate)
    (P : Measure (ℤ → α)) [IsProbabilityMeasure P]
    (m : α → Bool) (htrue : P (timedEmbeddedPathZeroTrueSet m) ≠ 0)
    (hfull : (timedEmbeddedTaggedArrivalAtZero rate hrate P).Ptag
      ((timedEmbeddedTaggedPathZeroMark m) ⁻¹' ({true} : Set Bool)) ≠ 0) :
    ((timedEmbeddedTaggedArrivalAtZero rate hrate P).conditionOn
      ((timedEmbeddedTaggedPathZeroMark m) ⁻¹' ({true} : Set Bool)) hfull).Ptag =
      (timedEmbeddedTaggedArrivalAtZero_conditionedOnPathZeroTrue
        hrate P m htrue).Ptag := by
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure rate) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure hrate
  letI : IsProbabilityMeasure (P[| timedEmbeddedPathZeroTrueSet m]) :=
    ProbabilityTheory.cond_isProbabilityMeasure htrue
  rw [TaggedArrivalAtZero.conditionOn_Ptag]
  change ((twoSidedInterarrivalMeasure rate).prod P)[|
      (timedEmbeddedTaggedPathZeroMark m) ⁻¹' ({true} : Set Bool)] =
    (twoSidedInterarrivalMeasure rate).prod
      (P[| timedEmbeddedPathZeroTrueSet m])
  rw [timedEmbeddedTaggedPathZeroMark_true_preimage]
  exact cond_prod_snd_eq_prod_cond (twoSidedInterarrivalMeasure rate) P
    (timedEmbeddedPathZeroTrueSet m)

/-- Under the concrete tagged law obtained by conditioning only the embedded
path factor at the tag, the first post-tag interarrival and every measurable
statistic of that same conditioned path have the displayed product law.

The first component is the actual Palm-gap coordinate `twoSidedGap 0`, not a
separately adjoined clock.  The result is one-gap/one-path-statistic only; it
does not establish a thinned Poisson process or an infinite iid mark tail. -/
theorem timedEmbeddedTaggedArrivalAtZero_conditionedOnPathZeroTrue_firstGap_pathStatistic_hasLaw
    {β : Type*} [MeasurableSpace β]
    {rate : ℝ} (hrate : 0 < rate)
    (P : Measure (ℤ → α)) [IsProbabilityMeasure P]
    (m : α → Bool)
    (htrue : P (timedEmbeddedPathZeroTrueSet m) ≠ 0)
    (stat : (ℤ → α) → β) (hstat : Measurable stat) :
    HasLaw
      (fun z : (ℤ → ℝ) × (ℤ → α) => (twoSidedGap 0 z.1, stat z.2))
      ((ProbabilityTheory.expMeasure rate).prod
        ((P[| timedEmbeddedPathZeroTrueSet m]).map stat))
      (timedEmbeddedTaggedArrivalAtZero_conditionedOnPathZeroTrue
        hrate P m htrue).Ptag := by
  let G : Measure (ℤ → ℝ) := twoSidedInterarrivalMeasure rate
  let A : Set (ℤ → α) := timedEmbeddedPathZeroTrueSet m
  let Q : Measure (ℤ → α) := P[| A]
  letI : IsProbabilityMeasure G := isProbabilityMeasure_twoSidedInterarrivalMeasure hrate
  letI : IsProbabilityMeasure Q := by
    dsimp [Q, A]
    exact ProbabilityTheory.cond_isProbabilityMeasure htrue
  refine ⟨((measurable_twoSidedGap 0).comp measurable_fst |>.prodMk
    (hstat.comp measurable_snd)).aemeasurable, ?_⟩
  change Measure.map (fun z : (ℤ → ℝ) × (ℤ → α) =>
      (twoSidedGap 0 z.1, stat z.2)) (G.prod Q) =
    (ProbabilityTheory.expMeasure rate).prod (Q.map stat)
  calc
    Measure.map (fun z : (ℤ → ℝ) × (ℤ → α) =>
        (twoSidedGap 0 z.1, stat z.2)) (G.prod Q) =
      (G.map (twoSidedGap 0)).prod (Q.map stat) := by
        simpa [Prod.map] using
          (Measure.map_prod_map G Q (measurable_twoSidedGap 0) hstat).symm
    _ = (ProbabilityTheory.expMeasure rate).prod (Q.map stat) := by
      rw [(twoSidedGap_hasLaw hrate 0).map_eq]

/-- The full post-tag future-gap path has its canonical iid exponential law
and is independent of every measurable statistic of the *same* conditioned
embedded path factor.  The source remains the concrete conditioned tagged
law: this is not a separately constructed clock/path product.

It gives the all-event Palm gap path only.  It neither thins that path by
marks nor proves an infinite iid mark tail. -/
theorem timedEmbeddedTaggedArrivalAtZero_conditionedOnPathZeroTrue_futureGapPath_pathStatistic_hasLaw
    {β : Type*} [MeasurableSpace β]
    {rate : ℝ} (hrate : 0 < rate)
    (P : Measure (ℤ → α)) [IsProbabilityMeasure P]
    (m : α → Bool)
    (htrue : P (timedEmbeddedPathZeroTrueSet m) ≠ 0)
    (stat : (ℤ → α) → β) (hstat : Measurable stat) :
    HasLaw
      (fun z : (ℤ → ℝ) × (ℤ → α) =>
        (candidateFutureGapPath z.1, stat z.2))
      ((exponentialInterarrivalMeasure rate).prod
        ((P[| timedEmbeddedPathZeroTrueSet m]).map stat))
      (timedEmbeddedTaggedArrivalAtZero_conditionedOnPathZeroTrue
        hrate P m htrue).Ptag := by
  let G : Measure (ℤ → ℝ) := twoSidedInterarrivalMeasure rate
  let A : Set (ℤ → α) := timedEmbeddedPathZeroTrueSet m
  let Q : Measure (ℤ → α) := P[| A]
  letI : IsProbabilityMeasure G := isProbabilityMeasure_twoSidedInterarrivalMeasure hrate
  letI : IsProbabilityMeasure Q := by
    dsimp [Q, A]
    exact ProbabilityTheory.cond_isProbabilityMeasure htrue
  have hfuture : Measurable candidateFutureGapPath :=
    measurable_pi_iff.2 fun n => measurable_twoSidedGap (Int.ofNat n)
  refine ⟨((hfuture.comp measurable_fst).prodMk
    (hstat.comp measurable_snd)).aemeasurable, ?_⟩
  change Measure.map (fun z : (ℤ → ℝ) × (ℤ → α) =>
      (candidateFutureGapPath z.1, stat z.2)) (G.prod Q) =
    (exponentialInterarrivalMeasure rate).prod (Q.map stat)
  calc
    Measure.map (fun z : (ℤ → ℝ) × (ℤ → α) =>
        (candidateFutureGapPath z.1, stat z.2)) (G.prod Q) =
      (G.map candidateFutureGapPath).prod (Q.map stat) := by
        simpa [Prod.map] using
          (Measure.map_prod_map G Q hfuture hstat).symm
    _ = (exponentialInterarrivalMeasure rate).prod (Q.map stat) := by
      rw [(candidateFutureGapPath_hasLaw hrate).map_eq]

/-- The unnormalized true-mark slice of the full tagged gap/path product is
the path true probability times the tagged product with the path factor
conditioned on that mark. -/
theorem timedEmbeddedTaggedArrivalAtZero_trueSlice_factorization
    {rate : ℝ} (hrate : 0 < rate)
    (P : Measure (ℤ → α)) [IsProbabilityMeasure P]
    (m : α → Bool) (hm : Measurable m)
    (htrue : P (timedEmbeddedPathZeroTrueSet m) ≠ 0)
    (s : Set ((ℤ → ℝ) × (ℤ → α))) :
    (timedEmbeddedTaggedArrivalAtZero rate hrate P).Ptag
      ((timedEmbeddedTaggedPathZeroMark m) ⁻¹' ({true} : Set Bool) ∩ s) =
      P (timedEmbeddedPathZeroTrueSet m) *
        (timedEmbeddedTaggedArrivalAtZero_conditionedOnPathZeroTrue
          hrate P m htrue).Ptag s := by
  let U : Set ((ℤ → ℝ) × (ℤ → α)) :=
    (timedEmbeddedTaggedPathZeroMark m) ⁻¹' ({true} : Set Bool)
  have hU : MeasurableSet U :=
    (measurableSet_singleton true).preimage
      (measurable_timedEmbeddedTaggedPathZeroMark m hm)
  have hfull : (timedEmbeddedTaggedArrivalAtZero rate hrate P).Ptag U ≠ 0 := by
    simpa only [U] using
      (measure_timedEmbeddedTaggedPathZeroMark_true hrate P m).trans_ne htrue
  have hmassU : (timedEmbeddedTaggedArrivalAtZero rate hrate P).Ptag U =
      P (timedEmbeddedPathZeroTrueSet m) := by
    simpa only [U] using
      (measure_timedEmbeddedTaggedPathZeroMark_true hrate P m)
  calc
    (timedEmbeddedTaggedArrivalAtZero rate hrate P).Ptag (U ∩ s) =
      (timedEmbeddedTaggedArrivalAtZero rate hrate P).Ptag U *
        ((timedEmbeddedTaggedArrivalAtZero rate hrate P).conditionOn U hfull).Ptag s :=
      Palm.tagged_conditionOn_slice_factorization
        (timedEmbeddedTaggedArrivalAtZero rate hrate P) U s hU hfull
    _ = P (timedEmbeddedPathZeroTrueSet m) *
        (timedEmbeddedTaggedArrivalAtZero_conditionedOnPathZeroTrue
          hrate P m htrue).Ptag s := by
      rw [hmassU,
        timedEmbeddedTaggedArrivalAtZero_conditionOnPathZeroTrue_Ptag
          hrate P m htrue hfull]

/-- The preceding factorization with a real-valued notation for the positive
true-mark probability. -/
theorem timedEmbeddedTaggedArrivalAtZero_trueSlice_factorization_ofReal
    {rate : ℝ} (hrate : 0 < rate)
    (P : Measure (ℤ → α)) [IsProbabilityMeasure P]
    (m : α → Bool) (hm : Measurable m)
    (p : ℝ)
    (hmass : P (timedEmbeddedPathZeroTrueSet m) = ENNReal.ofReal p)
    (htrue : P (timedEmbeddedPathZeroTrueSet m) ≠ 0)
    (s : Set ((ℤ → ℝ) × (ℤ → α))) :
    (timedEmbeddedTaggedArrivalAtZero rate hrate P).Ptag
      ((timedEmbeddedTaggedPathZeroMark m) ⁻¹' ({true} : Set Bool) ∩ s) =
      ENNReal.ofReal p *
        (timedEmbeddedTaggedArrivalAtZero_conditionedOnPathZeroTrue
          hrate P m htrue).Ptag s := by
  rw [timedEmbeddedTaggedArrivalAtZero_trueSlice_factorization
    hrate P m hm htrue s, hmass]

/-- A convenient positive-real-mass version of the true-slice factorization. -/
theorem timedEmbeddedTaggedArrivalAtZero_trueSlice_factorization_ofReal_of_pos
    {rate : ℝ} (hrate : 0 < rate)
    (P : Measure (ℤ → α)) [IsProbabilityMeasure P]
    (m : α → Bool) (hm : Measurable m)
    (p : ℝ) (hp : 0 < p)
    (hmass : P (timedEmbeddedPathZeroTrueSet m) = ENNReal.ofReal p)
    (s : Set ((ℤ → ℝ) × (ℤ → α))) :
    (timedEmbeddedTaggedArrivalAtZero rate hrate P).Ptag
      ((timedEmbeddedTaggedPathZeroMark m) ⁻¹' ({true} : Set Bool) ∩ s) =
      ENNReal.ofReal p *
        (timedEmbeddedTaggedArrivalAtZero_conditionedOnPathZeroTrue
          hrate P m (by rw [hmass]; exact ENNReal.ofReal_ne_zero_iff.mpr hp)).Ptag s := by
  let htrue : P (timedEmbeddedPathZeroTrueSet m) ≠ 0 := by
    rw [hmass]
    exact ENNReal.ofReal_ne_zero_iff.mpr hp
  exact timedEmbeddedTaggedArrivalAtZero_trueSlice_factorization_ofReal
    hrate P m hm p hmass htrue s



end

end AppliedModelingLib.Probability.Queueing
