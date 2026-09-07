import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith

/-!
# Ordered Pair Topology

Small reusable facts about strict ordered regions in `ℝ × ℝ`.  These support
continuous-ranking and pairwise-comparison arguments where minimizers often lie
on the diagonal boundary of a strict ordered-pair domain.
-/

namespace AppliedModelingLib

/-- Strict upper ordered pairs in `ℝ × ℝ`. -/
def strictUpperPairSet : Set (ℝ × ℝ) :=
  {q : ℝ × ℝ | q.2 < q.1}

/-- Closed upper ordered pairs in `ℝ × ℝ`. -/
def closedUpperPairSet : Set (ℝ × ℝ) :=
  {q : ℝ × ℝ | q.2 ≤ q.1}

/-- Closed square of ordered-pair coordinates in `[a,b]`. -/
def closedPairBox (a b : ℝ) : Set (ℝ × ℝ) :=
  Set.Icc a b ×ˢ Set.Icc a b

/-- Closed upper ordered pairs restricted to the closed interval `[a,b]`. -/
def closedUpperPairSetOn (a b : ℝ) : Set (ℝ × ℝ) :=
  closedUpperPairSet ∩ closedPairBox a b

/-- Strict upper ordered pairs restricted to the closed interval `[a,b]`. -/
def strictUpperPairSetOn (a b : ℝ) : Set (ℝ × ℝ) :=
  strictUpperPairSet ∩ closedPairBox a b

/-- Strict upper ordered pairs whose coordinates lie in the open interval `(a,b)`. -/
def strictUpperPairOpenOn (a b : ℝ) : Set (ℝ × ℝ) :=
  strictUpperPairSet ∩ (Set.Ioo a b ×ˢ Set.Ioo a b)

/-- The strict upper ordered-pair region is open. -/
theorem isOpen_strictUpperPairSet : IsOpen strictUpperPairSet := by
  have hcont : Continuous (fun q : ℝ × ℝ => q.1 - q.2) := by
    exact continuous_fst.sub continuous_snd
  have hset :
      strictUpperPairSet =
        (fun q : ℝ × ℝ => q.1 - q.2) ⁻¹' Set.Ioi (0 : ℝ) := by
    ext q
    constructor <;> intro h <;> dsimp [strictUpperPairSet, Set.Ioi] at h ⊢ <;>
      linarith
  rw [hset]
  exact (isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ))).preimage hcont

/-- The closed upper ordered-pair region is closed. -/
theorem isClosed_closedUpperPairSet : IsClosed closedUpperPairSet := by
  have hcont : Continuous (fun q : ℝ × ℝ => q.2 - q.1) := by
    exact continuous_snd.sub continuous_fst
  have hset :
      closedUpperPairSet =
        (fun q : ℝ × ℝ => q.2 - q.1) ⁻¹' Set.Iic (0 : ℝ) := by
    ext q
    constructor <;> intro h <;> dsimp [closedUpperPairSet, Set.Iic] at h ⊢ <;>
      linarith
  rw [hset]
  exact (isClosed_Iic : IsClosed (Set.Iic (0 : ℝ))).preimage hcont

/-- The closed coordinate box `[a,b] × [a,b]` is compact. -/
theorem isCompact_closedPairBox (a b : ℝ) :
    IsCompact (closedPairBox a b) := by
  simpa [closedPairBox] using (isCompact_Icc.prod isCompact_Icc :
    IsCompact (Set.Icc a b ×ˢ Set.Icc a b))

/-- The bounded closed upper ordered-pair region is compact. -/
theorem isCompact_closedUpperPairSetOn (a b : ℝ) :
    IsCompact (closedUpperPairSetOn a b) := by
  simpa [closedUpperPairSetOn, Set.inter_comm] using
    (isCompact_closedPairBox a b).inter_right isClosed_closedUpperPairSet

/-- The bounded strict upper region lies in its closed coordinate box. -/
theorem strictUpperPairSetOn_subset_closedPairBox (a b : ℝ) :
    strictUpperPairSetOn a b ⊆ closedPairBox a b := by
  intro q hq
  exact hq.2

/-- The bounded strict upper region lies in the bounded closed upper region. -/
theorem strictUpperPairSetOn_subset_closedUpperPairSetOn (a b : ℝ) :
    strictUpperPairSetOn a b ⊆ closedUpperPairSetOn a b := by
  intro q hq
  exact ⟨by simpa [closedUpperPairSet] using (le_of_lt hq.1), hq.2⟩

/-- The bounded strict upper region lies in the global strict upper region. -/
theorem strictUpperPairSetOn_subset_strictUpperPairSet (a b : ℝ) :
    strictUpperPairSetOn a b ⊆ strictUpperPairSet := by
  intro q hq
  exact hq.1

/-- The first coordinate of a bounded closed pair lies in `[a,b]`. -/
theorem closedPairBox_fst_mem_Icc {a b : ℝ} {q : ℝ × ℝ}
    (hq : q ∈ closedPairBox a b) :
    q.1 ∈ Set.Icc a b :=
  hq.1

/-- The second coordinate of a bounded closed pair lies in `[a,b]`. -/
theorem closedPairBox_snd_mem_Icc {a b : ℝ} {q : ℝ × ℝ}
    (hq : q ∈ closedPairBox a b) :
    q.2 ∈ Set.Icc a b :=
  hq.2

/-- The first coordinate of a bounded closed upper pair lies in `[a,b]`. -/
theorem closedUpperPairSetOn_fst_mem_Icc {a b : ℝ} {q : ℝ × ℝ}
    (hq : q ∈ closedUpperPairSetOn a b) :
    q.1 ∈ Set.Icc a b :=
  closedPairBox_fst_mem_Icc hq.2

/-- The second coordinate of a bounded closed upper pair lies in `[a,b]`. -/
theorem closedUpperPairSetOn_snd_mem_Icc {a b : ℝ} {q : ℝ × ℝ}
    (hq : q ∈ closedUpperPairSetOn a b) :
    q.2 ∈ Set.Icc a b :=
  closedPairBox_snd_mem_Icc hq.2

/-- Coordinates of a bounded closed upper pair satisfy `q.2 <= q.1`. -/
theorem closedUpperPairSetOn_snd_le_fst {a b : ℝ} {q : ℝ × ℝ}
    (hq : q ∈ closedUpperPairSetOn a b) :
    q.2 ≤ q.1 :=
  hq.1

/-- The open bounded strict upper region is open. -/
theorem isOpen_strictUpperPairOpenOn (a b : ℝ) :
    IsOpen (strictUpperPairOpenOn a b) := by
  simpa [strictUpperPairOpenOn] using
    isOpen_strictUpperPairSet.inter (isOpen_Ioo.prod isOpen_Ioo :
      IsOpen (Set.Ioo a b ×ˢ Set.Ioo a b))

/-- The open bounded strict upper region is contained in the bounded closed one. -/
theorem strictUpperPairOpenOn_subset_strictUpperPairSetOn (a b : ℝ) :
    strictUpperPairOpenOn a b ⊆ strictUpperPairSetOn a b := by
  intro q hq
  exact ⟨hq.1, ⟨⟨hq.2.1.1.le, hq.2.1.2.le⟩,
    ⟨hq.2.2.1.le, hq.2.2.2.le⟩⟩⟩

/-- The open bounded strict upper region lies inside the interior of the closed one. -/
theorem strictUpperPairOpenOn_subset_interior_strictUpperPairSetOn (a b : ℝ) :
    strictUpperPairOpenOn a b ⊆ interior (strictUpperPairSetOn a b) :=
  (isOpen_strictUpperPairOpenOn a b).subset_interior_iff.mpr
    (strictUpperPairOpenOn_subset_strictUpperPairSetOn a b)

/-- The strict upper ordered-pair region is its own interior. -/
theorem interior_strictUpperPairSet :
    interior strictUpperPairSet = strictUpperPairSet :=
  isOpen_strictUpperPairSet.interior_eq

/--
Every diagonal point is in the closure of the strict upper ordered-pair
region.  Equivalently, strict ordered pairs can approach the diagonal from the
upper side.
-/
theorem diagonal_mem_closure_strictUpperPairSet (x : ℝ) :
    (x, x) ∈ closure strictUpperPairSet := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  refine ⟨(x + ε / 2, x), ?_, ?_⟩
  · dsimp [strictUpperPairSet]
    linarith
  · have hdist : |ε / 2| < ε := by
      rw [abs_of_nonneg (le_of_lt (half_pos hε))]
      linarith
    simpa [Real.dist_eq, Prod.dist_eq] using hdist

/-- Diagonal points lie in the closure of the interior of the strict upper region. -/
theorem diagonal_mem_closure_interior_strictUpperPairSet (x : ℝ) :
    (x, x) ∈ closure (interior strictUpperPairSet) := by
  simpa [interior_strictUpperPairSet] using
    diagonal_mem_closure_strictUpperPairSet x

/--
Interior diagonal points of `[a,b]` lie in the closure of the interior of the
bounded strict upper region.
-/
theorem diagonal_mem_closure_interior_strictUpperPairSetOn
    {a b x : ℝ} (hx : x ∈ Set.Ioo a b) :
    (x, x) ∈ closure (interior (strictUpperPairSetOn a b)) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  let δ : ℝ := min (ε / 2) ((b - x) / 2)
  have hδ_pos : 0 < δ := by
    exact lt_min (half_pos hε) (half_pos (sub_pos.mpr hx.2))
  refine ⟨(x + δ / 2, x), ?_, ?_⟩
  · apply strictUpperPairOpenOn_subset_interior_strictUpperPairSetOn
    constructor
    · dsimp [strictUpperPairSet]
      linarith
    · constructor
      · constructor
        · linarith [hx.1, hδ_pos]
        · have hδ_le : δ ≤ (b - x) / 2 := min_le_right _ _
          linarith
      · exact hx
  · have hδ_le : δ ≤ ε / 2 := min_le_left _ _
    have hdist : |δ / 2| < ε := by
      rw [abs_of_nonneg (le_of_lt (half_pos hδ_pos))]
      linarith
    simpa [Real.dist_eq, Prod.dist_eq] using hdist

/--
Weak coordinate ordering becomes strict when the second coordinate is injective
on the set: two points with strictly ordered first coordinates cannot share a
second coordinate.
-/
theorem strict_snd_order_of_ordered_snd_of_injOn_snd
    {S : Set (ℝ × ℝ)}
    (hordered : ∀ p ∈ S, ∀ q ∈ S, p.1 < q.1 → p.2 ≤ q.2)
    (hinj : S.InjOn Prod.snd) :
    ∀ p ∈ S, ∀ q ∈ S, p.1 < q.1 → p.2 < q.2 := by
  intro p hp q hq hpq
  apply lt_of_le_of_ne (hordered p hp q hq hpq)
  intro hsnd
  have hpq_eq : p = q := hinj hp hq hsnd
  exact (ne_of_lt hpq) (by simp [hpq_eq])

/--
For a compact set whose second coordinate is strictly ordered by its first,
a gap in the first-coordinate projection ending at a represented point induces
an open gap in the second-coordinate projection.  The maximum second coordinate
to the left of the first gap supplies the lower endpoint of the induced gap.
-/
theorem exists_snd_gap_of_isCompact_of_strict_order_of_fst_gap
    {S : Set (ℝ × ℝ)} {a b d : ℝ}
    (hcompact : IsCompact S)
    (hinj : S.InjOn Prod.fst)
    (hstrict : ∀ p ∈ S, ∀ q ∈ S, p.1 < q.1 → p.2 < q.2)
    (hab : a < b)
    (hgap : ∀ p ∈ S, ¬ (a < p.1 ∧ p.1 < b))
    (hleft : ∃ p ∈ S, p.1 ≤ a)
    (hbd : (b, d) ∈ S) :
    ∃ c : ℝ, c < d ∧ Set.Ioo c d ⊆ (Prod.snd '' S)ᶜ := by
  let T : Set (ℝ × ℝ) := S ∩ Prod.fst ⁻¹' Set.Iic a
  have hTcompact : IsCompact T := by
    exact hcompact.inter_right (isClosed_Iic.preimage continuous_fst)
  have hTnonempty : T.Nonempty := by
    rcases hleft with ⟨p, hpS, hpa⟩
    exact ⟨p, hpS, hpa⟩
  obtain ⟨pmax, hpmaxT, hpmax⟩ := hTcompact.exists_isMaxOn hTnonempty
    continuous_snd.continuousOn
  refine ⟨pmax.2, ?_, ?_⟩
  · exact hstrict pmax hpmaxT.1 (b, d) hbd (lt_of_le_of_lt hpmaxT.2 hab)
  · intro y hy
    rintro ⟨p, hpS, rfl⟩
    by_cases hpa : p.1 ≤ a
    · have hpT : p ∈ T := ⟨hpS, hpa⟩
      have hle : p.2 ≤ pmax.2 := hpmax hpT
      exact (not_lt_of_ge hle) hy.1
    · have hpa : a < p.1 := lt_of_not_ge hpa
      by_cases hpb : p.1 < b
      · exact (hgap p hpS) ⟨hpa, hpb⟩
      · have hbp : b ≤ p.1 := le_of_not_gt hpb
        by_cases hbp_eq : b = p.1
        · have hp_eq : p = (b, d) := hinj hpS hbd (by simp [hbp_eq])
          subst p
          exact (lt_irrefl d) hy.2
        · have hbp_lt : b < p.1 := lt_of_le_of_ne hbp hbp_eq
          have hdp : d < p.2 := hstrict (b, d) hbd p hpS hbp_lt
          exact (not_lt_of_ge hdp.le) hy.2

end AppliedModelingLib
