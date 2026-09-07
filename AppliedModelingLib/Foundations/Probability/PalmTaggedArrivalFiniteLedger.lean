import AppliedModelingLib.Foundations.Probability.PoissonSuspensionFlow

/-!
# Finite interval ledgers for a Palm-tagged Poisson arrival path

This module works directly with a raw two-sided tagged gap path.  It gives a
finite, boundary-explicit enumeration of the tagged arrival epochs in any
half-open real interval.  It does not construct an untagged stationary law,
queue execution, service discipline, response time, or tail bound.
-/

namespace AppliedModelingLib.Probability.PoissonProcess

open MeasureTheory Filter

noncomputable section

/-- The finite candidate ledger for Palm-tagged arrivals in `[a, b)`.  The
two crossing labels provide finite integer bounds; the literal filter fixes
the interval endpoint convention even when a crossing label lies outside the
requested half-open interval. -/
def palmTaggedArrivalIndices (a b : ℝ) (g : ℤ → ℝ) : Finset ℤ :=
  (Finset.Icc
    (suspensionCrossingIndexPastClosed a (g, 0))
    (suspensionCrossingIndexPastClosed b (g, 0))).filter
      (fun i => a ≤ candidatePalmArrival g i ∧ candidatePalmArrival g i < b)

/-- The finite candidate ledger for a right-closed physical interval `(a, b]`.
This is useful when a renewal-count convention includes the endpoint at `b`
but excludes the distinguished arrival at `a`. -/
def palmTaggedArrivalIndicesRightClosed (a b : ℝ) (g : ℤ → ℝ) : Finset ℤ :=
  (Finset.Icc
    (suspensionCrossingIndexPastClosed a (g, 0))
    (suspensionCrossingIndexPastClosed b (g, 0))).filter
      (fun i => a < candidatePalmArrival g i ∧ candidatePalmArrival g i ≤ b)

/-- A crossing index for a good tagged gap path identifies the candidate
arrival interval containing the requested physical time. -/
theorem palmTaggedArrival_crossing_interval
    (g : ℤ → ℝ) (hgood : suspensionGoodGapPath g) (t : ℝ) :
    let k := suspensionCrossingIndexPastClosed t (g, 0)
    candidatePalmArrival g k ≤ t ∧ t < candidatePalmArrival g (k + 1) := by
  dsimp
  simpa using
    (suspensionCrossingIndexPastClosed_interval g
      (suspensionGoodGapPath_future g hgood)
      (suspensionGoodGapPath_past g hgood) 0 t)

/-- Exact membership specification for the finite tagged ledger.  The good
path hypothesis supplies strict ordering and two-sided nonexplosion used to
prove that every arrival in `[a, b)` lies between the two finite crossing
labels. -/
theorem mem_palmTaggedArrivalIndices_iff
    (a b : ℝ) (g : ℤ → ℝ) (hgood : suspensionGoodGapPath g) (i : ℤ) :
    i ∈ palmTaggedArrivalIndices a b g ↔
      a ≤ candidatePalmArrival g i ∧ candidatePalmArrival g i < b := by
  constructor
  · intro hi
    exact (Finset.mem_filter.mp hi).2
  · intro hi
    have ha := palmTaggedArrival_crossing_interval g hgood a
    have hb := palmTaggedArrival_crossing_interval g hgood b
    have hlow : suspensionCrossingIndexPastClosed a (g, 0) ≤ i := by
      by_contra hnot
      have hiless : i < suspensionCrossingIndexPastClosed a (g, 0) :=
        lt_of_not_ge hnot
      have harrival := (suspensionGoodGapPath_strictMono g hgood) hiless
      linarith [ha.1]
    have hupp : i ≤ suspensionCrossingIndexPastClosed b (g, 0) := by
      by_contra hnot
      have hiless : suspensionCrossingIndexPastClosed b (g, 0) < i :=
        lt_of_not_ge hnot
      have hnext : suspensionCrossingIndexPastClosed b (g, 0) + 1 ≤ i := by
        omega
      have harrival := (suspensionGoodGapPath_strictMono g hgood).monotone hnext
      linarith [hb.2]
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hlow, hupp⟩, hi⟩

/-- Exact membership specification for the right-closed finite tagged ledger.
The same crossing bounds suffice because the strict lower endpoint and weak
upper endpoint are recorded explicitly by the filter. -/
theorem mem_palmTaggedArrivalIndicesRightClosed_iff
    (a b : ℝ) (g : ℤ → ℝ) (hgood : suspensionGoodGapPath g) (i : ℤ) :
    i ∈ palmTaggedArrivalIndicesRightClosed a b g ↔
      a < candidatePalmArrival g i ∧ candidatePalmArrival g i ≤ b := by
  constructor
  · intro hi
    exact (Finset.mem_filter.mp hi).2
  · intro hi
    have ha := palmTaggedArrival_crossing_interval g hgood a
    have hb := palmTaggedArrival_crossing_interval g hgood b
    have hlow : suspensionCrossingIndexPastClosed a (g, 0) ≤ i := by
      by_contra hnot
      have hiless : i < suspensionCrossingIndexPastClosed a (g, 0) :=
        lt_of_not_ge hnot
      have harrival := (suspensionGoodGapPath_strictMono g hgood) hiless
      linarith [ha.1]
    have hupp : i ≤ suspensionCrossingIndexPastClosed b (g, 0) := by
      by_contra hnot
      have hiless : suspensionCrossingIndexPastClosed b (g, 0) < i :=
        lt_of_not_ge hnot
      have hnext : suspensionCrossingIndexPastClosed b (g, 0) + 1 ≤ i := by
        omega
      have harrival := (suspensionGoodGapPath_strictMono g hgood).monotone hnext
      linarith [hb.2]
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hlow, hupp⟩, hi⟩

/-- Membership of a fixed index in a right-closed Palm-tagged finite ledger
is a Borel event of the underlying two-sided gap path. -/
theorem measurableSet_mem_palmTaggedArrivalIndicesRightClosed
    (a b : ℝ) (k : ℤ) :
    MeasurableSet {g : ℤ → ℝ | k ∈ palmTaggedArrivalIndicesRightClosed a b g} := by
  change MeasurableSet {g : ℤ → ℝ |
    k ∈ (Finset.Icc
      (suspensionCrossingIndexPastClosed a (g, 0))
      (suspensionCrossingIndexPastClosed b (g, 0))).filter
        (fun m => a < candidatePalmArrival g m ∧ candidatePalmArrival g m ≤ b)}
  simp only [Finset.mem_filter, Finset.mem_Icc, Set.setOf_and]
  have hcrossLeft : Measurable (fun g : ℤ → ℝ =>
      suspensionCrossingIndexPastClosed a (g, 0)) := by
    exact (measurable_suspensionCrossingIndexPastClosed a).comp
      (measurable_id.prodMk measurable_const)
  have hcrossRight : Measurable (fun g : ℤ → ℝ =>
      suspensionCrossingIndexPastClosed b (g, 0)) := by
    exact (measurable_suspensionCrossingIndexPastClosed b).comp
      (measurable_id.prodMk measurable_const)
  have harrival : Measurable (fun g : ℤ → ℝ => candidatePalmArrival g k) :=
    measurable_candidatePalmArrival k
  exact ((measurableSet_le hcrossLeft measurable_const).inter
    (measurableSet_le measurable_const hcrossRight)).inter
      ((measurableSet_lt measurable_const harrival).inter
        (measurableSet_le harrival measurable_const))

/-- Adjacent right-closed Palm arrival windows partition their union exactly.
The shared endpoint belongs to the earlier window, so no boundary arrival is
lost or duplicated. -/
theorem palmTaggedArrivalIndicesRightClosed_union
    (a c b : ℝ) (g : ℤ → ℝ) (hgood : suspensionGoodGapPath g)
    (hac : a ≤ c) (hcb : c ≤ b) :
    palmTaggedArrivalIndicesRightClosed a b g =
      palmTaggedArrivalIndicesRightClosed a c g ∪
        palmTaggedArrivalIndicesRightClosed c b g := by
  ext k
  rw [Finset.mem_union,
    mem_palmTaggedArrivalIndicesRightClosed_iff a b g hgood k,
    mem_palmTaggedArrivalIndicesRightClosed_iff a c g hgood k,
    mem_palmTaggedArrivalIndicesRightClosed_iff c b g hgood k]
  constructor
  · rintro ⟨hlower, hupper⟩
    by_cases hsplit : candidatePalmArrival g k ≤ c
    · exact Or.inl ⟨hlower, hsplit⟩
    · exact Or.inr ⟨lt_of_not_ge hsplit, hupper⟩
  · rintro (hleft | hright)
    · exact ⟨hleft.1, hleft.2.trans hcb⟩
    · exact ⟨lt_of_le_of_lt hac hright.1, hright.2⟩

/-- The distinguished Palm index has physical arrival time zero, pointwise. -/
theorem palmTaggedArrival_zero (g : ℤ → ℝ) : candidatePalmArrival g 0 = 0 :=
  candidatePalmArrival_zero g

/-- The full-measure carrier for a raw tagged Poisson gap path.  Including
the zero-tag fact here makes the finite-ledger input self-contained without
claiming any stationary or queueing property. -/
def palmTaggedArrivalGoodCarrier (g : ℤ → ℝ) : Prop :=
  suspensionGoodGapPath g ∧ candidatePalmArrival g 0 = 0

/-- Every path in the tagged good carrier has its distinguished arrival at
time zero. -/
theorem palmTaggedArrivalGoodCarrier_tag_at_zero
    (g : ℤ → ℝ) (hgood : palmTaggedArrivalGoodCarrier g) :
    candidatePalmArrival g 0 = 0 :=
  hgood.2

/-- Iid exponential Palm gaps lie in the tagged finite-ledger carrier almost
surely. -/
theorem ae_palmTaggedArrivalGoodCarrier
    {rate : ℝ} (hrate : 0 < rate) :
    ∀ᵐ g ∂twoSidedInterarrivalMeasure rate, palmTaggedArrivalGoodCarrier g := by
  filter_upwards [ae_suspensionGoodGapPath hrate] with g hgood
  exact ⟨hgood, palmTaggedArrival_zero g⟩

end

end AppliedModelingLib.Probability.PoissonProcess
