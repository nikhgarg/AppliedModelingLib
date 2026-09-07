import AppliedModelingLib.Foundations.Math.FiniteSimplexFixedPoint

/-!
# KKM intersection theorems

This file derives the finite Knaster--Kuratowski--Mazurkiewicz (KKM) lemma
from the library's Brouwer theorem, then transports it through continuous
finite barycentric maps and compactness.  The resulting compact theorem is
suited to compact convex spaces represented by explicit finite mixtures, such
as probability-law spaces with their weak topology.
-/

namespace AppliedModelingLib

/--
Finite KKM lemma on a standard simplex.  If every point lies in one closed set
whose index has strictly positive simplex coordinate, then all of the closed
sets intersect.
-/
theorem finiteKKM_stdSimplex
    {I : Type*} [Fintype I] [Nonempty I]
    (C : I → Set (stdSimplex ℝ I))
    (hclosed : ∀ i, IsClosed (C i))
    (hcover : ∀ x : stdSimplex ℝ I,
      ∃ i, 0 < x i ∧ x ∈ C i) :
    ∃ x : stdSimplex ℝ I, ∀ i, x ∈ C i := by
  classical
  by_contra hintersection
  push Not at hintersection
  have hCnonempty : ∀ i, (C i).Nonempty := by
    intro i
    let vertex : stdSimplex ℝ I :=
      ⟨Pi.single i 1, single_mem_stdSimplex ℝ i⟩
    obtain ⟨j, hjpositive, hjmem⟩ := hcover vertex
    have hji : j = i := by
      by_contra hji
      simp [vertex, hji] at hjpositive
    exact ⟨vertex, hji ▸ hjmem⟩
  let gap : stdSimplex ℝ I → I → ℝ :=
    fun x i => Metric.infDist x (C i)
  have hgap_nonneg : ∀ x i, 0 ≤ gap x i := by
    intro x i
    exact Metric.infDist_nonneg
  have hgap_sum_pos : ∀ x, 0 < ∑ i, gap x i := by
    intro x
    obtain ⟨i, hi⟩ := hintersection x
    have hgap_pos : 0 < gap x i := by
      exact ((hclosed i).notMem_iff_infDist_pos (hCnonempty i)).mp hi
    exact hgap_pos.trans_le <|
      Finset.single_le_sum (fun j _ => hgap_nonneg x j) (Finset.mem_univ i)
  let response : stdSimplex ℝ I → stdSimplex ℝ I := fun x =>
    ⟨fun i => gap x i / ∑ j, gap x j, by
      constructor
      · intro i
        exact div_nonneg (hgap_nonneg x i) (hgap_sum_pos x).le
      · rw [← Finset.sum_div]
        exact div_self (ne_of_gt (hgap_sum_pos x))⟩
  have hgap_sum_continuous : Continuous (fun x : stdSimplex ℝ I => ∑ i, gap x i) := by
    apply continuous_finset_sum Finset.univ
    intro i _
    exact Metric.continuous_infDist_pt (C i)
  have hresponse_continuous : Continuous response := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    exact (Metric.continuous_infDist_pt (C i)).div hgap_sum_continuous
      (fun x => ne_of_gt (hgap_sum_pos x))
  obtain ⟨x, hxfixed⟩ := exists_fixedPoint_finiteSimplex response hresponse_continuous
  obtain ⟨i, hipositive, himem⟩ := hcover x
  have hresponse_positive : 0 < response x i := by
    simpa [hxfixed] using hipositive
  have hgap_positive : 0 < gap x i := by
    change 0 < gap x i / ∑ j, gap x j at hresponse_positive
    rcases div_pos_iff.mp hresponse_positive with hpositive | hnegative
    · exact hpositive.1
    · exact False.elim ((not_lt_of_ge (hgap_nonneg x i)) hnegative.1)
  exact (((hclosed i).notMem_iff_infDist_pos (hCnonempty i)).mpr hgap_positive) himem

/--
A continuous finite barycentric map transfers the finite KKM conclusion from
the standard simplex to its image.
-/
theorem finiteKKM_barycentric
    {Action I : Type*} [TopologicalSpace Action] [Fintype I] [Nonempty I]
    (barycenter : stdSimplex ℝ I → Action) (hbarycenter : Continuous barycenter)
    (C : I → Set Action) (hclosed : ∀ i, IsClosed (C i))
    (hcover : ∀ weights : stdSimplex ℝ I,
      ∃ i, 0 < weights i ∧ barycenter weights ∈ C i) :
    ∃ x : Action, ∀ i, x ∈ C i := by
  obtain ⟨weights, hweights⟩ := finiteKKM_stdSimplex
    (fun i => barycenter ⁻¹' C i)
    (fun i => (hclosed i).preimage hbarycenter)
    hcover
  exact ⟨barycenter weights, hweights⟩

/--
Compact barycentric KKM theorem.  A closed family on a compact action space
has a common point when every nonempty finite subfamily admits a continuous
barycentric map satisfying the KKM support cover.
-/
theorem compactKKM_barycentric
    {Action : Type*} [TopologicalSpace Action] [CompactSpace Action] [Nonempty Action]
    (C : Action → Set Action) (hclosed : ∀ action, IsClosed (C action))
    (hbarycenter : ∀ (s : Finset Action), s.Nonempty →
      ∃ barycenter : stdSimplex ℝ s → Action, Continuous barycenter ∧
        ∀ weights : stdSimplex ℝ s,
          ∃ action : s, 0 < weights action ∧ barycenter weights ∈ C action) :
    ∃ x : Action, ∀ action, x ∈ C action := by
  classical
  have hfinite_intersection : ∀ s : Finset Action, (⋂ action ∈ s, C action).Nonempty := by
    intro s
    by_cases hs : s.Nonempty
    · obtain ⟨action, haction⟩ := hs
      letI : Nonempty s := ⟨⟨action, haction⟩⟩
      obtain ⟨barycenter, hbarycenter_continuous, hcover⟩ :=
        hbarycenter s ⟨action, haction⟩
      obtain ⟨x, hx⟩ := finiteKKM_barycentric barycenter hbarycenter_continuous
        (fun action : s => C action) (fun action => hclosed action) hcover
      exact ⟨x, Set.mem_iInter₂.2 fun action haction => hx ⟨action, haction⟩⟩
    · rw [Finset.not_nonempty_iff_eq_empty.mp hs]
      simp
  obtain ⟨x, hx⟩ := CompactSpace.iInter_nonempty hclosed hfinite_intersection
  exact ⟨x, fun action => Set.mem_iInter.mp hx action⟩

end AppliedModelingLib
