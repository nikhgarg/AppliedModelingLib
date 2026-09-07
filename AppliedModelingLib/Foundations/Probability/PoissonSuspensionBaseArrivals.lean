import AppliedModelingLib.Foundations.Probability.PoissonSuspensionStationaryBase
import AppliedModelingLib.Foundations.Probability.PalmCampbell

/-!
# Stationary arrivals carried by the Poisson suspension

This module equips the literal good-state Poisson suspension with its
untagged ordered arrival process, exact finite window enumerators, and the
recentring map to the iid Palm-gap path. It proves every structural field of
the Campbell/Palm certificate. The remaining field is deliberately an
explicit marked unit-window mass-transport equality.
-/

namespace AppliedModelingLib.Probability.PoissonProcess

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

/-- The untagged arrival epochs in the stationary suspension state. -/
def suspensionBaseArrival (p : GoodSuspensionState) (i : ℤ) : ℝ :=
  candidatePalmArrival p.1.1 i - p.1.2

theorem measurable_suspensionBaseArrival (i : ℤ) :
    Measurable (fun p : GoodSuspensionState => suspensionBaseArrival p i) := by
  exact ((measurable_candidatePalmArrival i).comp
    (measurable_fst.comp measurable_subtype_coe)).sub
      (measurable_snd.comp measurable_subtype_coe)

theorem suspensionBaseArrival_strictMono (p : GoodSuspensionState) :
    StrictMono (suspensionBaseArrival p) := by
  intro i j hij
  exact sub_lt_sub_right
    (suspensionGoodGapPath_strictMono p.1.1 p.2.2 hij) _

/-- Every positive stationary suspension label lies strictly after the
deterministic origin. -/
theorem zero_lt_suspensionBaseArrival_ofNat_succ
    (p : GoodSuspensionState) (n : ℕ) :
    0 < suspensionBaseArrival p (Int.ofNat (n + 1)) := by
  have hphase : p.1.2 < twoSidedGap 0 p.1.1 := p.2.1.2
  have hfirst : candidatePalmArrival p.1.1 (Int.ofNat 1) =
      twoSidedGap 0 p.1.1 := by
    rw [show (Int.ofNat 1 : ℤ) = 0 + 1 by norm_num,
      candidatePalmArrival_add_one, candidatePalmArrival_zero]
    simp [twoSidedGap]
  have hindex : (Int.ofNat 1 : ℤ) ≤ Int.ofNat (n + 1) := by
    exact Int.ofNat_le.mpr (Nat.succ_le_succ (Nat.zero_le n))
  have hfuture : twoSidedGap 0 p.1.1 ≤
      candidatePalmArrival p.1.1 (Int.ofNat (n + 1)) := by
    rw [← hfirst]
    exact (suspensionGoodGapPath_strictMono p.1.1 p.2.2).monotone hindex
  exact sub_pos.mpr (lt_of_lt_of_le hphase hfuture)

/-- The positive stationary-base label `n + 1` is the `n`th canonical future
renewal epoch, shifted to physical time. -/
theorem suspensionBaseArrival_ofNat_succ_eq_arrivalTime_sub
    (p : GoodSuspensionState) (n : ℕ) :
    suspensionBaseArrival p (Int.ofNat (n + 1)) =
      arrivalTime n (suspensionFuturePath p.1.1) - p.1.2 := by
  rw [suspensionBaseArrival, candidatePalmArrival_ofNat,
    candidateFutureEpoch_succ_eq_arrivalTime_suspension]

/-- The positive labelled arrivals of a good stationary suspension do not
accumulate in finite time.  This is the stationary-base form of renewal
nonexplosion and is shared by queueing stopped-cycle arguments. -/
theorem tendsto_suspensionBaseArrival_ofNat_succ_atTop
    (p : GoodSuspensionState) :
    Filter.Tendsto (fun n : ℕ => suspensionBaseArrival p (Int.ofNat (n + 1)))
      Filter.atTop Filter.atTop := by
  have hfuture : Filter.Tendsto (fun n : ℕ => arrivalTime n (suspensionFuturePath p.1.1))
      Filter.atTop Filter.atTop :=
    suspensionGoodGapPath_future p.1.1 p.2.2
  rw [Filter.tendsto_atTop]
  intro bound
  filter_upwards [Filter.tendsto_atTop.1 hfuture (bound + p.1.2)] with n hn
  change bound ≤ candidatePalmArrival p.1.1 (Int.ofNat (n + 1)) - p.1.2
  rw [candidatePalmArrival_ofNat,
    candidateFutureEpoch_succ_eq_arrivalTime_suspension]
  linarith

/-- A positive stationary arrival strictly before a deterministic clock lies
in the corresponding finite forward-renewal prefix.  This converts a
physical-time bound into the index bound needed by finite-prefix arguments. -/
theorem lt_canonicalRenewalCount_of_suspensionBaseArrival_ofNat_succ_lt
    (p : GoodSuspensionState) (n : ℕ) (t : ℝ)
    (hbefore : suspensionBaseArrival p (Int.ofNat (n + 1)) < t) :
    n < canonicalRenewalCount (p.1.2 + t) (suspensionFuturePath p.1.1) := by
  have htime : arrivalTime n (suspensionFuturePath p.1.1) ≤ p.1.2 + t := by
    rw [← candidateFutureEpoch_succ_eq_arrivalTime_suspension]
    change candidatePalmArrival p.1.1 (Int.ofNat (n + 1)) ≤ p.1.2 + t
    change candidatePalmArrival p.1.1 (Int.ofNat (n + 1)) - p.1.2 < t at hbefore
    linarith
  have hmono : Monotone (fun k : ℕ => arrivalTime k (suspensionFuturePath p.1.1)) := by
    apply (arrivalTime_strictMono_of_positive _ ?_).monotone
    intro k
    simpa [interarrival, suspensionFuturePath, twoSidedGap] using
      p.2.2.1 (Int.ofNat k)
  exact (lt_canonicalRenewalCount_iff_arrivalTime_le_of_tendsto
    (suspensionFuturePath p.1.1) (suspensionGoodGapPath_future p.1.1 p.2.2)
    hmono (p.1.2 + t) n).mpr htime

/-- Any labelled stationary arrival strictly before the deterministic origin
has a nonpositive two-sided index. -/
theorem le_zero_of_suspensionBaseArrival_lt_zero
    (p : GoodSuspensionState) (m : ℤ)
    (hm : suspensionBaseArrival p m < 0) : m ≤ 0 := by
  cases m with
  | ofNat n =>
      cases n with
      | zero => exact le_rfl
      | succ n =>
          exact False.elim ((not_lt_of_ge
            (zero_lt_suspensionBaseArrival_ofNat_succ p n).le) hm)
  | negSucc n =>
      change -(Int.ofNat (n + 1)) ≤ 0
      exact neg_nonpos.mpr (Int.natCast_nonneg _)

/-- The iid-gap candidate path obtained by choosing base arrival `i` as tag. -/
def suspensionBaseRecenter (p : GoodSuspensionState) (i : ℤ) : ℤ → ℝ :=
  suspensionGapShift i p.1.1

theorem measurable_suspensionBaseRecenter (i : ℤ) :
    Measurable (fun p : GoodSuspensionState => suspensionBaseRecenter p i) := by
  exact (measurable_suspensionGapShift i).comp
    (measurable_fst.comp measurable_subtype_coe)

theorem suspensionBaseRecenter_arrivals
    (p : GoodSuspensionState) (i j : ℤ) :
    candidatePalmArrival (suspensionBaseRecenter p i) j =
      suspensionBaseArrival p (i + j) - suspensionBaseArrival p i := by
  change candidatePalmArrival (suspensionGapShift i p.1.1) j =
    suspensionBaseArrival p (i + j) - suspensionBaseArrival p i
  rw [candidatePalmArrival_suspensionGapShift]
  simp only [suspensionBaseArrival]
  ring

/-- The recenter map has the candidate iid Palm-gap path as its tagged target
type; the displayed equality is the corresponding arrival-path field. Its law
under a *selected* base arrival is the remaining Campbell identity. -/
theorem suspensionBaseRecenter_candidateTagged_arrivals
    {rate : ℝ} (hrate : 0 < rate) (p : GoodSuspensionState) (i j : ℤ) :
    (candidateTaggedArrivalAtZero rate hrate).arrivals
        (suspensionBaseRecenter p i) j =
      suspensionBaseArrival p (i + j) - suspensionBaseArrival p i := by
  exact suspensionBaseRecenter_arrivals p i j

/-- A finite candidate set containing exactly all indices with stationary-base
arrival epoch in `[a,b)`. Filtering makes the endpoint convention literal;
the two crossing labels make the containing interval finite. -/
def suspensionBaseArrivalIndices (a b : ℝ) (p : GoodSuspensionState) : Finset ℤ :=
  (Finset.Icc (suspensionCrossingIndexPastClosed a p.1)
    (suspensionCrossingIndexPastClosed b p.1)).filter
      (fun i => a ≤ suspensionBaseArrival p i ∧ suspensionBaseArrival p i < b)

/-- A finite candidate set containing exactly the stationary-base arrivals in
the right-closed interval `(a, b]`.  This endpoint convention is used by
canonical forward renewal counts. -/
def suspensionBaseArrivalIndicesRightClosed
    (a b : ℝ) (p : GoodSuspensionState) : Finset ℤ :=
  (Finset.Icc (suspensionCrossingIndexPastClosed a p.1)
    (suspensionCrossingIndexPastClosed b p.1)).filter
      (fun i => a < suspensionBaseArrival p i ∧ suspensionBaseArrival p i ≤ b)

theorem suspensionBaseArrival_crossing_interval
    (p : GoodSuspensionState) (t : ℝ) :
    let k := suspensionCrossingIndexPastClosed t p.1
    suspensionBaseArrival p k ≤ t ∧ t < suspensionBaseArrival p (k + 1) := by
  dsimp
  have h := suspensionCrossingIndexPastClosed_interval p.1.1
    (suspensionGoodGapPath_future p.1.1 p.2.2)
    (suspensionGoodGapPath_past p.1.1 p.2.2) p.1.2 t
  dsimp at h
  change candidatePalmArrival p.1.1 (suspensionCrossingIndexPastClosed t p.1) - p.1.2 ≤ t ∧
    t < candidatePalmArrival p.1.1 (suspensionCrossingIndexPastClosed t p.1 + 1) - p.1.2
  constructor <;> linarith [h.1, h.2]

theorem mem_suspensionBaseArrivalIndices_iff
    (a b : ℝ) (p : GoodSuspensionState) (i : ℤ) :
    i ∈ suspensionBaseArrivalIndices a b p ↔
      a ≤ suspensionBaseArrival p i ∧ suspensionBaseArrival p i < b := by
  constructor
  · intro hi
    exact (Finset.mem_filter.mp hi).2
  · intro hi
    have ha := suspensionBaseArrival_crossing_interval p a
    have hb := suspensionBaseArrival_crossing_interval p b
    have hlow : suspensionCrossingIndexPastClosed a p.1 ≤ i := by
      by_contra hnot
      have hiless : i < suspensionCrossingIndexPastClosed a p.1 := lt_of_not_ge hnot
      have harrival := suspensionBaseArrival_strictMono p hiless
      linarith [ha.1]
    have hupp : i ≤ suspensionCrossingIndexPastClosed b p.1 := by
      by_contra hnot
      have hiless : suspensionCrossingIndexPastClosed b p.1 < i := lt_of_not_ge hnot
      have hnext : suspensionCrossingIndexPastClosed b p.1 + 1 ≤ i := by omega
      have harrival := (suspensionBaseArrival_strictMono p).monotone hnext
      linarith [hb.2]
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hlow, hupp⟩, hi⟩

/-- Exact membership characterization of the right-closed stationary arrival
ledger. -/
theorem mem_suspensionBaseArrivalIndicesRightClosed_iff
    (a b : ℝ) (p : GoodSuspensionState) (i : ℤ) :
    i ∈ suspensionBaseArrivalIndicesRightClosed a b p ↔
      a < suspensionBaseArrival p i ∧ suspensionBaseArrival p i ≤ b := by
  constructor
  · intro hi
    exact (Finset.mem_filter.mp hi).2
  · intro hi
    have ha := suspensionBaseArrival_crossing_interval p a
    have hb := suspensionBaseArrival_crossing_interval p b
    have hlow : suspensionCrossingIndexPastClosed a p.1 ≤ i := by
      by_contra hnot
      have hiless : i < suspensionCrossingIndexPastClosed a p.1 := lt_of_not_ge hnot
      have harrival := suspensionBaseArrival_strictMono p hiless
      linarith [ha.1]
    have hupp : i ≤ suspensionCrossingIndexPastClosed b p.1 := by
      by_contra hnot
      have hiless : suspensionCrossingIndexPastClosed b p.1 < i := lt_of_not_ge hnot
      have hnext : suspensionCrossingIndexPastClosed b p.1 + 1 ≤ i := by omega
      have harrival := (suspensionBaseArrival_strictMono p).monotone hnext
      linarith [hb.2]
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hlow, hupp⟩, hi⟩

/-- Membership of one fixed index in a right-closed stationary-base finite
ledger is Borel in the suspension state. -/
theorem measurableSet_mem_suspensionBaseArrivalIndicesRightClosed
    (a b : ℝ) (i : ℤ) :
    MeasurableSet {p : GoodSuspensionState |
      i ∈ suspensionBaseArrivalIndicesRightClosed a b p} := by
  apply measurableSet_setOf.mpr
  simpa only [mem_suspensionBaseArrivalIndicesRightClosed_iff] using
    ((measurable_const.lt (measurable_suspensionBaseArrival i)).and
      ((measurable_suspensionBaseArrival i).le' measurable_const))

/-- Adjacent right-closed stationary arrival windows partition their union
exactly.  The shared endpoint is assigned to the earlier window. -/
theorem suspensionBaseArrivalIndicesRightClosed_union
    (a c b : ℝ) (p : GoodSuspensionState)
    (hac : a ≤ c) (hcb : c ≤ b) :
    suspensionBaseArrivalIndicesRightClosed a b p =
      suspensionBaseArrivalIndicesRightClosed a c p ∪
        suspensionBaseArrivalIndicesRightClosed c b p := by
  ext k
  rw [Finset.mem_union,
    mem_suspensionBaseArrivalIndicesRightClosed_iff a b p k,
    mem_suspensionBaseArrivalIndicesRightClosed_iff a c p k,
    mem_suspensionBaseArrivalIndicesRightClosed_iff c b p k]
  constructor
  · rintro ⟨hlower, hupper⟩
    by_cases hsplit : suspensionBaseArrival p k ≤ c
    · exact Or.inl ⟨hlower, hsplit⟩
    · exact Or.inr ⟨lt_of_not_ge hsplit, hupper⟩
  · rintro (hleft | hright)
    · exact ⟨hleft.1, hleft.2.trans hcb⟩
    · exact ⟨lt_of_le_of_lt hac hright.1, hright.2⟩

/-- Adjacent right-closed arrival windows are disjoint: the shared clock
endpoint belongs only to the earlier window. -/
theorem disjoint_suspensionBaseArrivalIndicesRightClosed_adjacent
    (a c b : ℝ) (p : GoodSuspensionState) :
    Disjoint (suspensionBaseArrivalIndicesRightClosed a c p)
      (suspensionBaseArrivalIndicesRightClosed c b p) := by
  rw [Finset.disjoint_left]
  intro k hleft hright
  have hleft' :=
    (mem_suspensionBaseArrivalIndicesRightClosed_iff a c p k).mp hleft
  have hright' :=
    (mem_suspensionBaseArrivalIndicesRightClosed_iff c b p k).mp hright
  linarith

/-- The cardinality of a right-closed stationary arrival window is additive
across an intermediate deterministic clock. -/
theorem card_suspensionBaseArrivalIndicesRightClosed_add
    (a c b : ℝ) (p : GoodSuspensionState)
    (hac : a ≤ c) (hcb : c ≤ b) :
    (suspensionBaseArrivalIndicesRightClosed a b p).card =
      (suspensionBaseArrivalIndicesRightClosed a c p).card +
        (suspensionBaseArrivalIndicesRightClosed c b p).card := by
  rw [suspensionBaseArrivalIndicesRightClosed_union a c b p hac hcb]
  exact Finset.card_union_of_disjoint
    (disjoint_suspensionBaseArrivalIndicesRightClosed_adjacent a c b p)

/-- A finite deterministic grid partitions a right-closed stationary arrival
window.  This is the pathwise telescoping identity behind finite-grid Poisson
compensation: the count through the terminal clock is the sum of the counts
in its consecutive right-closed subintervals. -/
theorem card_suspensionBaseArrivalIndicesRightClosed_grid
    (a h : ℝ) (p : GoodSuspensionState) (hh : 0 ≤ h) (N : ℕ) :
    (suspensionBaseArrivalIndicesRightClosed a (a + (N : ℝ) * h) p).card =
      ∑ r ∈ Finset.range N,
        (suspensionBaseArrivalIndicesRightClosed
          (a + (r : ℝ) * h) (a + ((r + 1 : ℕ) : ℝ) * h) p).card := by
  induction N with
  | zero =>
      have hempty : suspensionBaseArrivalIndicesRightClosed a a p = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro k hk
        have hmem :=
          (mem_suspensionBaseArrivalIndicesRightClosed_iff a a p k).mp hk
        linarith
      simp [hempty]
  | succ N ih =>
      let c : ℝ := a + (N : ℝ) * h
      let b : ℝ := a + ((N + 1 : ℕ) : ℝ) * h
      have hac : a ≤ c := by
        dsimp [c]
        have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
        exact le_add_of_nonneg_right (mul_nonneg hN hh)
      have hcb : c ≤ b := by
        dsimp [c, b]
        norm_num [Nat.cast_add, Nat.cast_one]
        linarith
      have hcard := card_suspensionBaseArrivalIndicesRightClosed_add a c b p hac hcb
      rw [Finset.sum_range_succ]
      calc
        (suspensionBaseArrivalIndicesRightClosed
            a (a + ((N + 1 : ℕ) : ℝ) * h) p).card =
            (suspensionBaseArrivalIndicesRightClosed a c p).card +
              (suspensionBaseArrivalIndicesRightClosed c b p).card := by
                simpa [b] using hcard
        _ = (∑ r ∈ Finset.range N,
            (suspensionBaseArrivalIndicesRightClosed
              (a + (r : ℝ) * h) (a + ((r + 1 : ℕ) : ℝ) * h) p).card) +
              (suspensionBaseArrivalIndicesRightClosed
                (a + (N : ℝ) * h) (a + ((N + 1 : ℕ) : ℝ) * h) p).card := by
                  rw [ih]

/-- The canonical forward-renewal count, started at the suspension phase and
observed through physical time `t`. -/
noncomputable def suspensionBaseFutureCount (p : GoodSuspensionState) (t : ℝ) : ℕ :=
  canonicalRenewalCount (p.1.2 + t) (suspensionFuturePath p.1.1)

/-- On the nonnegative physical half-line, right-closed stationary arrival
labels are exactly the positive canonical future-renewal labels. -/
theorem suspensionBaseArrivalIndicesRightClosed_zero_eq_futureCanonicalIndices
    (p : GoodSuspensionState) (t : ℝ) (ht : 0 ≤ t) :
    suspensionBaseArrivalIndicesRightClosed 0 t p =
      (Finset.range (suspensionBaseFutureCount p t)).image
        (fun n => Int.ofNat (n + 1)) := by
  classical
  have hfuture : Filter.Tendsto
      (fun n : ℕ => arrivalTime n (suspensionFuturePath p.1.1))
      Filter.atTop Filter.atTop :=
    suspensionGoodGapPath_future p.1.1 p.2.2
  have hmono : Monotone
      (fun n : ℕ => arrivalTime n (suspensionFuturePath p.1.1)) := by
    apply (arrivalTime_strictMono_of_positive _ ?_).monotone
    intro n
    simpa [interarrival, suspensionFuturePath, twoSidedGap] using
      p.2.2.1 (Int.ofNat n)
  have hbasezero : suspensionBaseArrival p 0 ≤ 0 := by
    change candidatePalmArrival p.1.1 0 - p.1.2 ≤ 0
    rw [candidatePalmArrival_zero]
    linarith [p.2.1.1]
  ext k
  cases k with
  | ofNat n =>
      cases n with
      | zero =>
          constructor
          · intro hk
            have hmem :=
              (mem_suspensionBaseArrivalIndicesRightClosed_iff 0 t p 0).mp hk
            linarith
          · intro hk
            rcases Finset.mem_image.mp hk with ⟨m, hm, hzero⟩
            have hpositive : (0 : ℤ) < Int.ofNat (m + 1) := by
              change (0 : ℤ) < ((m + 1 : ℕ) : ℤ)
              exact_mod_cast Nat.zero_lt_succ m
            have hzero' : Int.ofNat (m + 1) = 0 := by
              simpa using hzero
            linarith
      | succ n =>
          have hpositive : 0 < suspensionBaseArrival p (Int.ofNat (n + 1)) :=
            zero_lt_suspensionBaseArrival_ofNat_succ p n
          constructor
          · intro hk
            have hmem :=
              (mem_suspensionBaseArrivalIndicesRightClosed_iff 0 t p
                (Int.ofNat (n + 1))).mp hk
            refine Finset.mem_image.mpr ⟨n, ?_, rfl⟩
            rw [Finset.mem_range]
            apply (lt_canonicalRenewalCount_iff_arrivalTime_le_of_tendsto
              (suspensionFuturePath p.1.1) hfuture hmono (p.1.2 + t) n).mpr
            rw [suspensionBaseArrival_ofNat_succ_eq_arrivalTime_sub] at hmem
            linarith
          · intro hk
            rcases Finset.mem_image.mp hk with ⟨m, hm, hmn⟩
            have hmn' : m = n := Nat.add_right_cancel (Int.ofNat.inj hmn)
            subst m
            apply (mem_suspensionBaseArrivalIndicesRightClosed_iff 0 t p
              (Int.ofNat (n + 1))).mpr
            constructor
            · exact hpositive
            · rw [suspensionBaseArrival_ofNat_succ_eq_arrivalTime_sub]
              have hle :=
                (lt_canonicalRenewalCount_iff_arrivalTime_le_of_tendsto
                  (suspensionFuturePath p.1.1) hfuture hmono (p.1.2 + t) n).mp
                  (by simpa [suspensionBaseFutureCount, Finset.mem_range] using hm)
              linarith
  | negSucc n =>
      have hnegative : suspensionBaseArrival p (Int.negSucc n) < 0 := by
        have hindex : Int.negSucc n < 0 := Int.negSucc_lt_zero n
        have hlt := suspensionBaseArrival_strictMono p hindex
        linarith
      constructor
      · intro hk
        have hmem :=
          (mem_suspensionBaseArrivalIndicesRightClosed_iff 0 t p
            (Int.negSucc n)).mp hk
        linarith
      · intro hk
        rcases Finset.mem_image.mp hk with ⟨m, hm, hmn⟩
        have hnonnegative : 0 ≤ Int.ofNat (m + 1) := by
          change 0 ≤ ((m + 1 : ℕ) : ℤ)
          exact Int.natCast_nonneg _
        have hnegativeIndex : Int.negSucc n < 0 := Int.negSucc_lt_zero n
        linarith

/-- The literal physical count of stationary arrivals in `(0,t]` is the
canonical forward-renewal count from the suspension phase. -/
theorem suspensionBaseArrivalIndicesRightClosed_zero_card_eq_futureCount
    (p : GoodSuspensionState) (t : ℝ) (ht : 0 ≤ t) :
    (suspensionBaseArrivalIndicesRightClosed 0 t p).card =
      suspensionBaseFutureCount p t := by
  rw [suspensionBaseArrivalIndicesRightClosed_zero_eq_futureCanonicalIndices p t ht,
    Finset.card_image_of_injective]
  · simp
  · intro a b hab
    apply Nat.succ.inj
    apply Int.ofNat.inj
    simpa using hab

/-- No stationary-base arrivals lie in the empty physical window `(0,0]`. -/
theorem suspensionBaseFutureCount_zero (p : GoodSuspensionState) :
    suspensionBaseFutureCount p 0 = 0 := by
  have hempty : suspensionBaseArrivalIndicesRightClosed 0 0 p = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro k hk
    have hmem := (mem_suspensionBaseArrivalIndicesRightClosed_iff 0 0 p k).mp hk
    linarith
  have hcard := suspensionBaseArrivalIndicesRightClosed_zero_card_eq_futureCount p 0 le_rfl
  rw [hempty] at hcard
  simpa using hcard.symm

/-- A physical stationary renewal count is locally constant from a clock up
to, but excluding, its next labelled arrival. -/
theorem suspensionBaseFutureCount_eq_of_le_lt_nextArrival
    (p : GoodSuspensionState) (s u : ℝ) (hsu : s ≤ u)
    (hu : u < suspensionBaseArrival p
      (Int.ofNat (suspensionBaseFutureCount p s + 1))) :
    suspensionBaseFutureCount p u = suspensionBaseFutureCount p s := by
  have hu' := hu
  simp only [suspensionBaseFutureCount] at hu'
  rw [suspensionBaseArrival_ofNat_succ_eq_arrivalTime_sub] at hu'
  unfold suspensionBaseFutureCount
  apply canonicalRenewalCount_eq_of_le_lt_nextArrival
    (suspensionFuturePath p.1.1) (suspensionGoodGapPath_future p.1.1 p.2.2)
    (p.1.2 + s) (p.1.2 + u) (by linarith)
  linarith

/-- The next positive physical arrival after a clock is strictly later than
that clock. -/
theorem lt_suspensionBaseArrival_succFutureCount
    (p : GoodSuspensionState) (s : ℝ) :
    s < suspensionBaseArrival p
      (Int.ofNat (suspensionBaseFutureCount p s + 1)) := by
  rw [suspensionBaseArrival_ofNat_succ_eq_arrivalTime_sub]
  have hfuture : ∃ n : ℕ,
      p.1.2 + s < arrivalTime n (suspensionFuturePath p.1.1) :=
    (suspensionGoodGapPath_future p.1.1 p.2.2).eventually_gt_atTop _ |>.exists
  have hlt := lt_arrivalTime_canonicalRenewalCount
    (p.1.2 + s) (suspensionFuturePath p.1.1) hfuture
  simpa [suspensionBaseFutureCount] using sub_lt_sub_right hlt p.1.2

/-- A physical stationary renewal count is right-continuous along any
sequence that approaches its clock from above. -/
theorem eventually_eq_suspensionBaseFutureCount_of_tendsto_from_right
    (p : GoodSuspensionState) (s : ℝ) (u : ℕ → ℝ)
    (hu : Filter.Tendsto u Filter.atTop (nhds s))
    (hsu : ∀ m, s ≤ u m) :
    ∀ᶠ m in Filter.atTop,
      suspensionBaseFutureCount p (u m) = suspensionBaseFutureCount p s := by
  filter_upwards [hu.eventually_lt_const
    (lt_suspensionBaseArrival_succFutureCount p s)] with m hm
  exact suspensionBaseFutureCount_eq_of_le_lt_nextArrival p s (u m) (hsu m) hm

/-- A physical stationary renewal count is right-continuous along any
sequence that approaches its clock from above. -/
theorem tendsto_suspensionBaseFutureCount_of_tendsto_from_right
    (p : GoodSuspensionState) (s : ℝ) (u : ℕ → ℝ)
    (hu : Filter.Tendsto u Filter.atTop (nhds s))
    (hsu : ∀ m, s ≤ u m) :
    Filter.Tendsto (fun m => suspensionBaseFutureCount p (u m))
      Filter.atTop (nhds (suspensionBaseFutureCount p s)) := by
  apply tendsto_nhds_of_eventually_eq
  exact eventually_eq_suspensionBaseFutureCount_of_tendsto_from_right p s u hu hsu

/-- The real-valued stationary renewal count is right-continuous along any
sequence that approaches its clock from above. -/
theorem tendsto_coe_suspensionBaseFutureCount_of_tendsto_from_right
    (p : GoodSuspensionState) (s : ℝ) (u : ℕ → ℝ)
    (hu : Filter.Tendsto u Filter.atTop (nhds s))
    (hsu : ∀ m, s ≤ u m) :
    Filter.Tendsto (fun m => (suspensionBaseFutureCount p (u m) : ℝ))
      Filter.atTop (nhds (suspensionBaseFutureCount p s : ℝ)) := by
  apply tendsto_nhds_of_eventually_eq
  filter_upwards [eventually_eq_suspensionBaseFutureCount_of_tendsto_from_right
    p s u hu hsu] with m hm
  exact congrArg (fun count : ℕ => (count : ℝ)) hm

/-- The physical stationary renewal count is nondecreasing in its horizon. -/
theorem monotone_suspensionBaseFutureCount (p : GoodSuspensionState) :
    Monotone (suspensionBaseFutureCount p) := by
  unfold suspensionBaseFutureCount
  intro s t hst
  exact canonicalRenewalCount_monotone_of_tendsto
    (suspensionFuturePath p.1.1) (suspensionGoodGapPath_future p.1.1 p.2.2)
    (by linarith)

/-- The increment of the physical stationary count over a deterministic
right-closed interval is exactly the cardinality of that interval's arrival
ledger. -/
theorem suspensionBaseFutureCount_sub_eq_card_rightClosed
    (p : GoodSuspensionState) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    suspensionBaseFutureCount p b - suspensionBaseFutureCount p a =
      (suspensionBaseArrivalIndicesRightClosed a b p).card := by
  have hb : 0 ≤ b := ha.trans hab
  have hcard := card_suspensionBaseArrivalIndicesRightClosed_add 0 a b p ha hab
  rw [suspensionBaseArrivalIndicesRightClosed_zero_card_eq_futureCount p b hb,
    suspensionBaseArrivalIndicesRightClosed_zero_card_eq_futureCount p a ha] at hcard
  omega

theorem suspensionBaseArrival_goodSuspensionFlow
    (p : GoodSuspensionState) (t : ℝ) (j : ℤ) :
    suspensionBaseArrival (goodSuspensionFlow t p) j =
      suspensionBaseArrival p
        (suspensionCrossingIndexPastClosed t p.1 + j) - t := by
  change candidatePalmArrival (suspensionFlow t p.1).1 j -
      (suspensionFlow t p.1).2 =
    suspensionBaseArrival p
      (suspensionCrossingIndexPastClosed t p.1 + j) - t
  simp only [suspensionFlow]
  rw [candidatePalmArrival_suspensionGapShift]
  simp only [suspensionBaseArrival]
  ring

theorem suspensionBaseArrival_range_goodSuspensionFlow
    (p : GoodSuspensionState) (t : ℝ) :
    Set.range (suspensionBaseArrival (goodSuspensionFlow t p)) =
      (fun u : ℝ => u - t) '' Set.range (suspensionBaseArrival p) := by
  ext x
  constructor
  · rintro ⟨j, rfl⟩
    refine ⟨suspensionBaseArrival p
      (suspensionCrossingIndexPastClosed t p.1 + j), ⟨_, rfl⟩, ?_⟩
    exact (suspensionBaseArrival_goodSuspensionFlow p t j).symm
  · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
    let k := suspensionCrossingIndexPastClosed t p.1
    refine ⟨i - k, ?_⟩
    rw [suspensionBaseArrival_goodSuspensionFlow]
    have hindex : k + (i - k) = i := by dsimp [k]; omega
    rw [hindex]

/-- The finite marked unit-window count is measurable for every measurable
candidate-tagged event. This closes the measurability field of the eventual
Campbell certificate independently of its still-open mass-transport identity. -/
theorem measurable_suspensionBaseMarkedUnitWindowCount
    (s : Set (ℤ → ℝ)) (hs : MeasurableSet s) :
    Measurable (fun p : GoodSuspensionState =>
      Palm.unitWindowCampbellCount suspensionBaseArrivalIndices
        suspensionBaseRecenter s p) := by
  classical
  let state : GoodSuspensionState → ℤ × ℤ := fun p =>
    (suspensionCrossingIndexPastClosed 0 p.1,
      suspensionCrossingIndexPastClosed 1 p.1)
  let indices : ℤ × ℤ → Finset ℤ := fun n => Finset.Icc n.1 n.2
  have hstate : Measurable state := by
    exact ((measurable_suspensionCrossingIndexPastClosed 0).comp measurable_subtype_coe).prodMk
      ((measurable_suspensionCrossingIndexPastClosed 1).comp measurable_subtype_coe)
  let selected : GoodSuspensionState → ℤ → Bool := fun p i =>
    decide (0 ≤ suspensionBaseArrival p i ∧ suspensionBaseArrival p i < 1 ∧
      suspensionBaseRecenter p i ∈ s)
  have hselected : Measurable selected := by
    refine measurable_pi_iff.2 fun i => ?_
    change Measurable (fun p => if
      0 ≤ suspensionBaseArrival p i ∧ suspensionBaseArrival p i < 1 ∧
        suspensionBaseRecenter p i ∈ s then true else false)
    have hleft : MeasurableSet {p : GoodSuspensionState |
        (0 : ℝ) ≤ suspensionBaseArrival p i} :=
      measurableSet_le measurable_const (measurable_suspensionBaseArrival i)
    have hright : MeasurableSet {p : GoodSuspensionState |
        suspensionBaseArrival p i < (1 : ℝ)} :=
      measurableSet_lt (measurable_suspensionBaseArrival i) measurable_const
    have hmark : MeasurableSet {p : GoodSuspensionState |
        suspensionBaseRecenter p i ∈ s} :=
      (measurable_suspensionBaseRecenter i) hs
    exact Measurable.ite (hleft.inter (hright.inter hmark))
      measurable_const measurable_const
  have hcount := Palm.measurable_count_from_countable_parameter state hstate indices
    selected hselected
  change Measurable (fun p =>
    ((suspensionBaseArrivalIndices 0 1 p).filter fun i =>
      suspensionBaseRecenter p i ∈ s).card)
  convert hcount using 1
  funext p
  simp only [state, indices, selected, suspensionBaseArrivalIndices,
    Finset.filter_filter, decide_eq_true_eq]
  congr 1
  apply Finset.filter_congr
  intro i hi
  constructor <;> intro h
  · exact ⟨h.1.1, h.1.2, h.2⟩
  · exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩

/-- The raw fixed-index summand in the marked suspension transport.  It is
the same selected-arrival event as the good-state Campbell count, before the
full-measure good carrier is packaged as a subtype. -/
noncomputable def suspensionMarkedUnitSummand
    (s : Set (ℤ → ℝ)) (i : ℤ) (p : (ℤ → ℝ) × ℝ) : ℝ≥0∞ := by
  classical
  exact if 0 ≤ candidatePalmArrival p.1 i - p.2 ∧
      candidatePalmArrival p.1 i - p.2 < 1 ∧
      suspensionGapShift i p.1 ∈ s then 1 else 0

theorem measurable_suspensionMarkedUnitSummand
    (s : Set (ℤ → ℝ)) (hs : MeasurableSet s) (i : ℤ) :
    Measurable (suspensionMarkedUnitSummand s i) := by
  classical
  have hleft : MeasurableSet {p : (ℤ → ℝ) × ℝ |
      (0 : ℝ) ≤ candidatePalmArrival p.1 i - p.2} :=
    measurableSet_le measurable_const
      (((measurable_candidatePalmArrival i).comp measurable_fst).sub measurable_snd)
  have hright : MeasurableSet {p : (ℤ → ℝ) × ℝ |
      candidatePalmArrival p.1 i - p.2 < (1 : ℝ)} :=
    measurableSet_lt
      (((measurable_candidatePalmArrival i).comp measurable_fst).sub measurable_snd)
      measurable_const
  have hmark : MeasurableSet {p : (ℤ → ℝ) × ℝ |
      suspensionGapShift i p.1 ∈ s} :=
    ((measurable_suspensionGapShift i).comp measurable_fst) hs
  change Measurable (fun p : (ℤ → ℝ) × ℝ => if
      0 ≤ candidatePalmArrival p.1 i - p.2 ∧
        candidatePalmArrival p.1 i - p.2 < 1 ∧
        suspensionGapShift i p.1 ∈ s then (1 : ℝ≥0∞) else 0)
  exact Measurable.ite (hleft.inter (hright.inter hmark))
    measurable_const measurable_const

/-- The remaining raw mass-transport theorem: fixed-index reindexing carries
the selected branches to a partition of a unit phase strip. -/
def HasSuspensionMarkedUnitTransport (rate : ℝ) : Prop :=
  ∀ s : Set (ℤ → ℝ), MeasurableSet s →
    ∑' i : ℤ, ∫⁻ p, suspensionMarkedUnitSummand s i p
      ∂suspensionMeasure rate =
      ENNReal.ofReal rate * twoSidedInterarrivalMeasure rate s

/-- On the literal good suspension state space, the finite marked unit-window
count is the finite sum of the raw fixed-index summands. -/
theorem suspensionBaseMarkedUnitWindowCount_eq_sum
    (s : Set (ℤ → ℝ)) (p : GoodSuspensionState) :
    Palm.unitWindowCampbellCount
      suspensionBaseArrivalIndices suspensionBaseRecenter s p =
      (by
        classical
        exact ∑ i ∈ suspensionBaseArrivalIndices 0 1 p,
          if 0 ≤ suspensionBaseArrival p i ∧
              suspensionBaseArrival p i < 1 ∧
              suspensionBaseRecenter p i ∈ s then 1 else 0) := by
  classical
  change ((suspensionBaseArrivalIndices 0 1 p).filter fun i =>
    suspensionBaseRecenter p i ∈ s).card = _
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro i hi
  have hinterval : 0 ≤ suspensionBaseArrival p i ∧
      suspensionBaseArrival p i < 1 :=
    (mem_suspensionBaseArrivalIndices_iff 0 1 p i).mp hi
  by_cases hmark : suspensionBaseRecenter p i ∈ s
  · simp [hinterval, hmark]
  · simp [hinterval, hmark]

theorem suspensionBaseMarkedUnitWindowCount_coe_eq_tsum
    (s : Set (ℤ → ℝ)) (p : GoodSuspensionState) :
    (Palm.unitWindowCampbellCount
      suspensionBaseArrivalIndices suspensionBaseRecenter s p : ℝ≥0∞) =
      ∑' i : ℤ, suspensionMarkedUnitSummand s i p.1 := by
  classical
  rw [suspensionBaseMarkedUnitWindowCount_eq_sum]
  rw [tsum_eq_sum (s := suspensionBaseArrivalIndices 0 1 p)]
  · simp only [suspensionMarkedUnitSummand]
    norm_cast
  · intro i hi
    have hnot : ¬ (0 ≤ suspensionBaseArrival p i ∧
        suspensionBaseArrival p i < 1) := by
      intro h
      exact hi ((mem_suspensionBaseArrivalIndices_iff 0 1 p i).mpr h)
    change suspensionMarkedUnitSummand s i p.1 = 0
    change (if 0 ≤ suspensionBaseArrival p i ∧
        suspensionBaseArrival p i < 1 ∧
        suspensionBaseRecenter p i ∈ s then (1 : ℝ≥0∞) else 0) = 0
    have hnot' : ¬ (0 ≤ suspensionBaseArrival p i ∧
        suspensionBaseArrival p i < 1 ∧ suspensionBaseRecenter p i ∈ s) := by
      rintro ⟨hzero, hone, _⟩
      exact hnot ⟨hzero, hone⟩
    simp [hnot']

/-- Coercing the good carrier back to the raw suspension coordinates pushes
its probability law exactly to the normalized suspension measure. -/
theorem map_goodSuspensionMeasure_subtype_val
    {rate : ℝ} (hrate : 0 < rate) :
    Measure.map (Subtype.val : GoodSuspensionState → ((ℤ → ℝ) × ℝ))
      (goodSuspensionMeasure rate) = suspensionMeasure rate := by
  let I : GoodSuspensionState → ((ℤ → ℝ) × ℝ) := Subtype.val
  have hI : MeasurableEmbedding I :=
    MeasurableEmbedding.subtype_coe measurableSet_goodSuspensionState
  change Measure.map I (Measure.comap I (suspensionMeasure rate)) =
    suspensionMeasure rate
  rw [hI.map_comap]
  apply Measure.restrict_eq_self_of_ae_mem
  filter_upwards [ae_goodSuspensionState hrate] with p hp
  exact ⟨⟨p, hp⟩, rfl⟩

/-- A raw marked branch-transport theorem yields the exact marked
unit-window formula for the stationary good-suspension base.  This removes
all subtype and Tonelli bookkeeping from the remaining analytic seam. -/
theorem suspensionBaseMarkedUnitCampbell_of_transport
    {rate : ℝ} (hrate : 0 < rate)
    (htransport : HasSuspensionMarkedUnitTransport rate)
    (s : Set (ℤ → ℝ)) (hs : MeasurableSet s) :
    ∫⁻ p, (Palm.unitWindowCampbellCount
      suspensionBaseArrivalIndices suspensionBaseRecenter s p : ℝ≥0∞)
      ∂goodSuspensionMeasure rate =
      ENNReal.ofReal rate * twoSidedInterarrivalMeasure rate s := by
  calc
    ∫⁻ p, (Palm.unitWindowCampbellCount
        suspensionBaseArrivalIndices suspensionBaseRecenter s p : ℝ≥0∞)
        ∂goodSuspensionMeasure rate =
      ∫⁻ p, ∑' i : ℤ, suspensionMarkedUnitSummand s i p.1
        ∂goodSuspensionMeasure rate := by
          apply MeasureTheory.lintegral_congr
          intro p
          exact suspensionBaseMarkedUnitWindowCount_coe_eq_tsum s p
    _ = ∑' i : ℤ, ∫⁻ p, suspensionMarkedUnitSummand s i p.1
        ∂goodSuspensionMeasure rate := by
          exact MeasureTheory.lintegral_tsum fun i =>
            ((measurable_suspensionMarkedUnitSummand s hs i).comp
              measurable_subtype_coe).aemeasurable
    _ = ∑' i : ℤ, ∫⁻ p, suspensionMarkedUnitSummand s i p
        ∂suspensionMeasure rate := by
          apply tsum_congr
          intro i
          calc
            ∫⁻ p, suspensionMarkedUnitSummand s i p.1
                ∂goodSuspensionMeasure rate =
                ∫⁻ p, suspensionMarkedUnitSummand s i p
                  ∂Measure.map (Subtype.val : GoodSuspensionState → ((ℤ → ℝ) × ℝ))
                    (goodSuspensionMeasure rate) := by
                      exact (MeasureTheory.lintegral_map
                        (measurable_suspensionMarkedUnitSummand s hs i)
                        measurable_subtype_coe).symm
            _ = ∫⁻ p, suspensionMarkedUnitSummand s i p
                ∂suspensionMeasure rate := by
                  rw [map_goodSuspensionMeasure_subtype_val hrate]
    _ = ENNReal.ofReal rate * twoSidedInterarrivalMeasure rate s :=
      htransport s hs

/-- Certificate-ready pointwise facts, expressed in the almost-everywhere
form used by `CampbellPalmTaggedArrivalCertificate`. -/
theorem ae_suspensionBaseArrival_strict
    {rate : ℝ} (hrate : 0 < rate) :
    ∀ᵐ p ∂(goodSuspensionShiftInvariantLaw hrate).Pbase,
      StrictMono (suspensionBaseArrival p) :=
  Filter.Eventually.of_forall suspensionBaseArrival_strictMono

theorem ae_suspensionBaseArrivalIndices_spec
    {rate : ℝ} (hrate : 0 < rate) (a b : ℝ) :
    ∀ᵐ p ∂(goodSuspensionShiftInvariantLaw hrate).Pbase, ∀ i,
      i ∈ suspensionBaseArrivalIndices a b p ↔
        a ≤ suspensionBaseArrival p i ∧ suspensionBaseArrival p i < b :=
  Filter.Eventually.of_forall fun p i =>
    mem_suspensionBaseArrivalIndices_iff a b p i

theorem ae_suspensionBaseArrival_shift
    {rate : ℝ} (hrate : 0 < rate) (t : ℝ) :
    ∀ᵐ p ∂(goodSuspensionShiftInvariantLaw hrate).Pbase,
      Set.range (suspensionBaseArrival
        ((goodSuspensionShiftInvariantLaw hrate).shift t p)) =
        (fun u : ℝ => u - t) '' Set.range (suspensionBaseArrival p) :=
  Filter.Eventually.of_forall fun p =>
    suspensionBaseArrival_range_goodSuspensionFlow p t

/-- All non-mass-transport fields of the stationary Campbell/Palm certificate
are now concrete. Supplying `hcampbell` is exactly the remaining marked
Campbell theorem; it is not hidden by this constructor. -/
noncomputable def goodSuspensionCampbellCertificate
    {rate : ℝ} (hrate : 0 < rate)
    (hcampbell : ∀ s : Set (ℤ → ℝ), MeasurableSet s →
      ∫⁻ p, (↑(Palm.unitWindowCampbellCount suspensionBaseArrivalIndices
        suspensionBaseRecenter s p) : ENNReal)
        ∂(goodSuspensionShiftInvariantLaw hrate).Pbase =
        ENNReal.ofReal rate * (candidateTaggedArrivalAtZero rate hrate).Ptag s) :
    Palm.CampbellPalmTaggedArrivalCertificate
      (goodSuspensionShiftInvariantLaw hrate)
      (candidateTaggedArrivalAtZero rate hrate) where
  arrivalRate := rate
  arrivalRate_pos := hrate
  baseArrivals := suspensionBaseArrival
  baseArrivals_measurable := measurable_suspensionBaseArrival
  baseArrivals_strict := ae_suspensionBaseArrival_strict hrate
  arrivalsIn := suspensionBaseArrivalIndices
  arrivalsIn_spec := fun a b => ae_suspensionBaseArrivalIndices_spec hrate a b
  recenterAt := suspensionBaseRecenter
  recenterAt_measurable := measurable_suspensionBaseRecenter
  recenter_arrivals := Filter.Eventually.of_forall fun p i j =>
    suspensionBaseRecenter_candidateTagged_arrivals hrate p i j
  baseArrivals_shift := fun t => ae_suspensionBaseArrival_shift hrate t
  campbellCount_aemeasurable := fun s hs =>
    (measurable_suspensionBaseMarkedUnitWindowCount s hs).aemeasurable
  campbell_unit_interval := hcampbell

/-- The raw fixed-index transport closes the sole analytic field of the
good-suspension Campbell/Palm certificate. -/
noncomputable def goodSuspensionCampbellCertificate_of_transport
    {rate : ℝ} (hrate : 0 < rate)
    (htransport : HasSuspensionMarkedUnitTransport rate) :
    Palm.CampbellPalmTaggedArrivalCertificate
      (goodSuspensionShiftInvariantLaw hrate)
      (candidateTaggedArrivalAtZero rate hrate) :=
  goodSuspensionCampbellCertificate hrate (fun s hs => by
    simpa [candidateTaggedArrivalAtZero] using
      (suspensionBaseMarkedUnitCampbell_of_transport hrate htransport s hs))

end

end AppliedModelingLib.Probability.PoissonProcess
