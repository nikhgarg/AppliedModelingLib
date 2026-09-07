import AppliedModelingLib.Foundations.Graph.AlternatingPairing

/-!
# Orienting the cycles of two alternating pairings

Two edge-disjoint fixed-point-free involutions form even alternating cycles.
This file chooses one of the two vertex classes on every such cycle.  The
choice is completely finite and supplies the directed cycle orientation used
by the final Feder--Subi triangle-packing construction.
-/

namespace AppliedModelingLib
namespace Foundations
namespace Graph

variable {α : Type*} [Fintype α] [DecidableEq α]

namespace AlternatingPairing

/-- Advance through the first pairing and then the second pairing.  Its
cycles are one of the two alternating vertex classes of the union cycle. -/
noncomputable def advancePerm (A : AlternatingPairing α) : Equiv.Perm α :=
  A.first.perm.trans A.second.perm

theorem advancePerm_apply (A : AlternatingPairing α) (x : α) :
    A.advancePerm x = A.second.perm (A.first.perm x) := rfl

theorem firstPerm_inv (A : AlternatingPairing α) : (A.first.perm)⁻¹ = A.first.perm := by
  ext x
  apply A.first.perm.injective
  change A.first.perm (A.first.perm.symm x) = A.first.perm (A.first.perm x)
  rw [A.first.perm.apply_symm_apply, A.first.apply_apply]

theorem secondPerm_inv (A : AlternatingPairing α) : (A.second.perm)⁻¹ = A.second.perm := by
  ext x
  apply A.second.perm.injective
  change A.second.perm (A.second.perm.symm x) = A.second.perm (A.second.perm x)
  rw [A.second.perm.apply_symm_apply, A.second.apply_apply]

theorem advancePerm_eq_mul (A : AlternatingPairing α) :
    A.advancePerm = A.second.perm * A.first.perm := rfl

/-- Reflecting an advance cycle through the first pairing reverses it. -/
theorem firstPerm_conj_advancePerm (A : AlternatingPairing α) :
    A.first.perm * A.advancePerm * (A.first.perm)⁻¹ = (A.advancePerm)⁻¹ := by
  have hfirst_sq : A.first.perm * A.first.perm = 1 := by
    ext x
    exact A.first.apply_apply x
  calc
    A.first.perm * A.advancePerm * (A.first.perm)⁻¹ =
        A.first.perm * (A.second.perm * A.first.perm) * A.first.perm := by
          rw [A.advancePerm_eq_mul, A.firstPerm_inv]
    _ = A.first.perm * A.second.perm := by
      calc
        A.first.perm * (A.second.perm * A.first.perm) * A.first.perm =
            A.first.perm * A.second.perm * (A.first.perm * A.first.perm) := by
              group
        _ = A.first.perm * A.second.perm := by rw [hfirst_sq, mul_one]
    _ = (A.advancePerm)⁻¹ := by
      rw [A.advancePerm_eq_mul, mul_inv_rev, A.firstPerm_inv, A.secondPerm_inv]

theorem inv_mem_cycleFactorsFinset {f c : Equiv.Perm α}
    (hc : c ∈ f.cycleFactorsFinset) :
    c⁻¹ ∈ (f⁻¹).cycleFactorsFinset := by
  rw [Equiv.Perm.mem_cycleFactorsFinset_iff] at hc ⊢
  refine ⟨hc.1.inv, ?_⟩
  intro a ha
  have hcsupport : c⁻¹ a ∈ c.support := by
    rw [Equiv.Perm.mem_support]
    simpa using (Equiv.Perm.mem_support.mp ha).symm
  apply f.injective
  calc
    f (c⁻¹ a) = c (c⁻¹ a) := (hc.2 _ hcsupport).symm
    _ = a := c.apply_symm_apply a
    _ = f (f⁻¹ a) := (f.apply_symm_apply a).symm

/-- The partner advance factor on the other vertex class of the same
alternating cycle. -/
noncomputable def factorMate (A : AlternatingPairing α)
    (c : A.advancePerm.cycleFactorsFinset) : A.advancePerm.cycleFactorsFinset := by
  let a := A.first.perm
  let f := A.advancePerm
  refine ⟨a * (c : Equiv.Perm α)⁻¹ * a⁻¹, ?_⟩
  have hc_inv : (c : Equiv.Perm α)⁻¹ ∈ (f⁻¹).cycleFactorsFinset :=
    inv_mem_cycleFactorsFinset c.2
  have hconj_inv : a * f⁻¹ * a⁻¹ = f := by
    calc
      a * f⁻¹ * a⁻¹ = (a * f * a⁻¹)⁻¹ := by group
      _ = (f⁻¹)⁻¹ := by rw [show a * f * a⁻¹ = f⁻¹ from A.firstPerm_conj_advancePerm]
      _ = f := inv_inv _
  have hmem := (Equiv.Perm.mem_cycleFactorsFinset_conj f⁻¹ a
    ((c : Equiv.Perm α)⁻¹)).mpr hc_inv
  rw [hconj_inv] at hmem
  exact hmem

theorem factorMate_apply_apply (A : AlternatingPairing α)
    (c : A.advancePerm.cycleFactorsFinset) : A.factorMate (A.factorMate c) = c := by
  apply Subtype.ext
  have hfirst_sq : A.first.perm * A.first.perm = 1 := by
    ext x
    exact A.first.apply_apply x
  simp only [factorMate, A.firstPerm_inv]
  rw [mul_inv_rev, mul_inv_rev, inv_inv, A.firstPerm_inv]
  calc
    A.first.perm * (A.first.perm * (c : Equiv.Perm α) * A.first.perm) *
        A.first.perm =
        (A.first.perm * A.first.perm) * (c : Equiv.Perm α) *
          (A.first.perm * A.first.perm) := by simp only [mul_assoc]
    _ = c := by rw [hfirst_sq]; simp

theorem firstPerm_mem_factorMate_support (A : AlternatingPairing α)
    (c : A.advancePerm.cycleFactorsFinset) (x : α)
    (hx : x ∈ (c : Equiv.Perm α).support) :
    A.first.perm x ∈ (A.factorMate c : Equiv.Perm α).support := by
  have hcinv_ne : (c : Equiv.Perm α)⁻¹ x ≠ x := by
    intro heq
    apply Equiv.Perm.mem_support.mp hx
    calc
      (c : Equiv.Perm α) x = (c : Equiv.Perm α) ((c : Equiv.Perm α)⁻¹ x) := by
        rw [heq]
      _ = x := (c : Equiv.Perm α).apply_symm_apply x
  rw [Equiv.Perm.mem_support]
  change (A.first.perm * (c : Equiv.Perm α)⁻¹ * (A.first.perm)⁻¹)
      (A.first.perm x) ≠ A.first.perm x
  rw [A.firstPerm_inv]
  simp only [Equiv.Perm.coe_mul, Function.comp_apply]
  rw [show A.first.perm (A.first.perm x) = x from A.first.apply_apply x]
  exact fun hfix => hcinv_ne (A.first.perm.injective hfix)

theorem factorMate_ne (A : AlternatingPairing α)
    (c : A.advancePerm.cycleFactorsFinset) : A.factorMate c ≠ c := by
  classical
  intro hself
  have hself' : A.first.perm * (c : Equiv.Perm α)⁻¹ * (A.first.perm)⁻¹ = c := by
    have hself_val := congrArg Subtype.val hself
    simpa only [factorMate] using hself_val
  have hconj : A.first.perm * (c : Equiv.Perm α) * (A.first.perm)⁻¹ =
      (c : Equiv.Perm α)⁻¹ := by
    calc
      A.first.perm * (c : Equiv.Perm α) * (A.first.perm)⁻¹ =
          (A.first.perm * (c : Equiv.Perm α)⁻¹ * (A.first.perm)⁻¹)⁻¹ := by
            group
      _ = (c : Equiv.Perm α)⁻¹ := by rw [hself']
  have hcomm : A.first.perm * (c : Equiv.Perm α) =
      (c : Equiv.Perm α)⁻¹ * A.first.perm := by
    calc
      A.first.perm * (c : Equiv.Perm α) =
          (A.first.perm * (c : Equiv.Perm α) * (A.first.perm)⁻¹) * A.first.perm := by
            group
      _ = (c : Equiv.Perm α)⁻¹ * A.first.perm := by rw [hconj]
  have hcomm_pow : ∀ n : ℕ,
      A.first.perm * (c : Equiv.Perm α) ^ n =
        ((c : Equiv.Perm α)⁻¹) ^ n * A.first.perm := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ]
      calc
        A.first.perm * ((c : Equiv.Perm α) ^ n * c) =
            (A.first.perm * (c : Equiv.Perm α) ^ n) * c := by group
        _ = (((c : Equiv.Perm α)⁻¹ ^ n) * A.first.perm) * c := by rw [ih]
        _ = ((c : Equiv.Perm α)⁻¹) ^ n *
            (A.first.perm * c) := by group
        _ = ((c : Equiv.Perm α)⁻¹) ^ n *
            ((c : Equiv.Perm α)⁻¹ * A.first.perm) := by rw [hcomm]
        _ = ((c : Equiv.Perm α)⁻¹) ^ (n + 1) * A.first.perm := by
            rw [pow_succ]
            group
  have hc := Equiv.Perm.mem_cycleFactorsFinset_iff.mp c.2
  obtain ⟨x, hx⟩ := Equiv.Perm.IsCycle.nonempty_support hc.1
  have hax : A.first.perm x ∈ (c : Equiv.Perm α).support := by
    have h := A.firstPerm_mem_factorMate_support c x hx
    rwa [hself] at h
  obtain ⟨k, hk⟩ := hc.1.exists_pow_eq
    (Equiv.Perm.mem_support.mp hx) (Equiv.Perm.mem_support.mp hax)
  rcases Nat.even_or_odd k with hk_even | hk_odd
  · obtain ⟨n, hn⟩ := hk_even
    have hkn : k = n + n := by omega
    have hfixed : A.first.perm (((c : Equiv.Perm α) ^ n) x) =
        ((c : Equiv.Perm α) ^ n) x := by
      change (A.first.perm * (c : Equiv.Perm α) ^ n) x =
        ((c : Equiv.Perm α) ^ n) x
      rw [hcomm_pow n]
      rw [inv_pow]
      simp only [Equiv.Perm.coe_mul, Function.comp_apply]
      have hpower : (c : Equiv.Perm α) ^ (n + n) =
          (c : Equiv.Perm α) ^ n * (c : Equiv.Perm α) ^ n :=
        pow_add _ _ _
      rw [← hk, hkn, hpower]
      change (((c : Equiv.Perm α) ^ n)⁻¹ *
        ((c : Equiv.Perm α) ^ n * (c : Equiv.Perm α) ^ n)) x =
          ((c : Equiv.Perm α) ^ n) x
      congr 1
      group
    exact A.first.apply_ne _ hfixed
  · obtain ⟨n, hn⟩ := hk_odd
    have hkn : k = (n + 1) + n := by omega
    have hay : A.first.perm (((c : Equiv.Perm α) ^ (n + 1)) x) =
        ((c : Equiv.Perm α) ^ n) x := by
      change (A.first.perm * (c : Equiv.Perm α) ^ (n + 1)) x =
        ((c : Equiv.Perm α) ^ n) x
      rw [hcomm_pow (n + 1)]
      rw [inv_pow]
      simp only [Equiv.Perm.coe_mul, Function.comp_apply]
      have hpower : (c : Equiv.Perm α) ^ ((n + 1) + n) =
          (c : Equiv.Perm α) ^ (n + 1) * (c : Equiv.Perm α) ^ n :=
        pow_add _ _ _
      rw [← hk, hkn, hpower]
      change (((c : Equiv.Perm α) ^ (n + 1))⁻¹ *
        ((c : Equiv.Perm α) ^ (n + 1) * (c : Equiv.Perm α) ^ n)) x =
            ((c : Equiv.Perm α) ^ n) x
      congr 1
      group
    have hxn : ((c : Equiv.Perm α) ^ n) x ∈
        (c : Equiv.Perm α).support :=
      Equiv.Perm.pow_apply_mem_support.2 hx
    have hadvance : A.advancePerm (((c : Equiv.Perm α) ^ n) x) =
        (c : Equiv.Perm α) (((c : Equiv.Perm α) ^ n) x) :=
      (hc.2 _ hxn).symm
    have hsecond : A.second.perm (((c : Equiv.Perm α) ^ (n + 1)) x) =
        ((c : Equiv.Perm α) ^ (n + 1)) x := by
      change (A.second.perm * (c : Equiv.Perm α) ^ (n + 1)) x =
        ((c : Equiv.Perm α) ^ (n + 1)) x
      have hfirst_sq : A.first.perm * A.first.perm = 1 := by
        ext x
        exact A.first.apply_apply x
      have hsecond_eq : A.second.perm = A.advancePerm * A.first.perm := by
        calc
          A.second.perm = A.second.perm * (A.first.perm * A.first.perm) := by
            rw [hfirst_sq, mul_one]
          _ = (A.second.perm * A.first.perm) * A.first.perm := by group
          _ = A.advancePerm * A.first.perm := by rw [A.advancePerm_eq_mul]
      rw [hsecond_eq]
      simp only [Equiv.Perm.coe_mul, Function.comp_apply, hay, hadvance]
      rw [pow_succ]
      change ((c : Equiv.Perm α) *
        (c : Equiv.Perm α) ^ n) x =
          ((c : Equiv.Perm α) ^ n * c) x
      congr 1
      group
    exact A.second.apply_ne _ hsecond

theorem advancePerm_ne (A : AlternatingPairing α) (x : α) : A.advancePerm x ≠ x := by
  intro h
  apply A.distinct x
  have h' := congrArg A.second.perm h
  change A.second.perm (A.second.perm (A.first.perm x)) = A.second.perm x at h'
  rw [A.second.apply_apply] at h'
  exact h'

/-- Choose one side of every paired pair of advance factors. -/
noncomputable def factorColor (A : AlternatingPairing α)
    (c : A.advancePerm.cycleFactorsFinset) : Bool := by
  letI : LinearOrder A.advancePerm.cycleFactorsFinset :=
    (Fintype.equivFin A.advancePerm.cycleFactorsFinset).linearOrder
  exact if c < A.factorMate c then false else true

theorem factorColor_factorMate (A : AlternatingPairing α)
    (c : A.advancePerm.cycleFactorsFinset) :
    A.factorColor (A.factorMate c) = !(A.factorColor c) := by
  classical
  letI : LinearOrder A.advancePerm.cycleFactorsFinset :=
    (Fintype.equivFin A.advancePerm.cycleFactorsFinset).linearOrder
  unfold factorColor
  rw [A.factorMate_apply_apply]
  by_cases hlt : c < A.factorMate c
  · have hnot : ¬ A.factorMate c < c := not_lt_of_ge (le_of_lt hlt)
    simp [hlt, hnot]
  · have hrev : A.factorMate c < c :=
      (lt_or_gt_of_ne (A.factorMate_ne c)).resolve_right hlt
    simp [hlt, hrev]

/-- The advance factor containing a vertex. -/
noncomputable def advanceFactor (A : AlternatingPairing α) (x : α) :
    A.advancePerm.cycleFactorsFinset := by
  refine ⟨A.advancePerm.cycleOf x, ?_⟩
  rw [Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff, Equiv.Perm.mem_support]
  exact A.advancePerm_ne x

theorem advanceFactor_first (A : AlternatingPairing α) (x : α) :
    A.advanceFactor (A.first.perm x) = A.factorMate (A.advanceFactor x) := by
  have hx : x ∈ A.advancePerm.support :=
    Equiv.Perm.mem_support.mpr (A.advancePerm_ne x)
  have hmem : A.first.perm x ∈
      (A.factorMate (A.advanceFactor x) : Equiv.Perm α).support :=
    A.firstPerm_mem_factorMate_support (A.advanceFactor x) x (by
      simpa [advanceFactor] using hx)
  apply Subtype.ext
  symm
  exact (Equiv.Perm.eq_cycleOf_of_mem_cycleFactorsFinset_iff A.advancePerm
    (A.factorMate (A.advanceFactor x))
    (A.factorMate (A.advanceFactor x)).2 (A.first.perm x)).mpr hmem

theorem advanceFactor_advance (A : AlternatingPairing α) (x : α) :
    A.advanceFactor (A.advancePerm x) = A.advanceFactor x := by
  apply Subtype.ext
  simp [advanceFactor]

theorem advanceFactor_second (A : AlternatingPairing α) (x : α) :
    A.advanceFactor (A.second.perm x) = A.factorMate (A.advanceFactor x) := by
  have hstep : A.advancePerm (A.first.perm x) = A.second.perm x := by
    rw [A.advancePerm_apply, A.first.apply_apply]
  calc
    A.advanceFactor (A.second.perm x) = A.advanceFactor (A.advancePerm (A.first.perm x)) := by
      rw [hstep]
    _ = A.advanceFactor (A.first.perm x) := A.advanceFactor_advance (A.first.perm x)
    _ = A.factorMate (A.advanceFactor x) := A.advanceFactor_first x

/-- A two-colouring of the alternating union.  Both pairing edges flip this
colour, exactly as required to orient every union-cycle. -/
noncomputable def vertexColor (A : AlternatingPairing α) (x : α) : Bool :=
  A.factorColor (A.advanceFactor x)

theorem vertexColor_first (A : AlternatingPairing α) (x : α) :
    A.vertexColor (A.first.perm x) = !A.vertexColor x := by
  unfold vertexColor
  rw [A.advanceFactor_first, A.factorColor_factorMate]

theorem vertexColor_second (A : AlternatingPairing α) (x : α) :
    A.vertexColor (A.second.perm x) = !A.vertexColor x := by
  unfold vertexColor
  rw [A.advanceFactor_second, A.factorColor_factorMate]

/-- Direct every alternating-cycle vertex to one of its two paired
neighbours.  A first-pairing edge is directed from the `false` colour class,
and a second-pairing edge from the `true` class. -/
noncomputable def orientedPartner (A : AlternatingPairing α) (x : α) : α :=
  if A.vertexColor x = false then A.first.perm x else A.second.perm x

theorem orientedPartner_eq_first_of_color_false (A : AlternatingPairing α) (x : α)
    (hx : A.vertexColor x = false) : A.orientedPartner x = A.first.perm x := by
  simp [orientedPartner, hx]

theorem orientedPartner_eq_second_of_color_ne_false (A : AlternatingPairing α) (x : α)
    (hx : A.vertexColor x ≠ false) : A.orientedPartner x = A.second.perm x := by
  simp [orientedPartner, hx]

theorem orientedPartner_ne (A : AlternatingPairing α) (x : α) :
    A.orientedPartner x ≠ x := by
  by_cases hx : A.vertexColor x = false
  · rw [A.orientedPartner_eq_first_of_color_false x hx]
    exact A.first.apply_ne x
  · rw [A.orientedPartner_eq_second_of_color_ne_false x hx]
    exact A.second.apply_ne x

/-- Every first-pairing edge has exactly one endpoint from which it is
directed.  This is the formal version of orienting an even alternating
cycle. -/
theorem first_edge_oriented (A : AlternatingPairing α) (x : α) :
    A.orientedPartner x = A.first.perm x ∨
      A.orientedPartner (A.first.perm x) = x := by
  by_cases hx : A.vertexColor x = false
  · left
    exact A.orientedPartner_eq_first_of_color_false x hx
  · right
    have hneighbor : A.vertexColor (A.first.perm x) = false := by
      cases hcolor : A.vertexColor x with
      | false => exact False.elim (hx hcolor)
      | true => rw [A.vertexColor_first, hcolor]; rfl
    rw [A.orientedPartner_eq_first_of_color_false _ hneighbor]
    exact A.first.apply_apply x

/-- Every second-pairing edge has exactly one endpoint from which it is
directed. -/
theorem second_edge_oriented (A : AlternatingPairing α) (x : α) :
    A.orientedPartner x = A.second.perm x ∨
      A.orientedPartner (A.second.perm x) = x := by
  by_cases hx : A.vertexColor x = false
  · right
    have hneighbor : A.vertexColor (A.second.perm x) ≠ false := by
      rw [A.vertexColor_second]
      simpa [hx]
    rw [A.orientedPartner_eq_second_of_color_ne_false _ hneighbor]
    exact A.second.apply_apply x
  · left
    exact A.orientedPartner_eq_second_of_color_ne_false x hx

/-- A selected direction never immediately reverses itself. -/
theorem orientedPartner_not_reverse (A : AlternatingPairing α) (x : α) :
    A.orientedPartner (A.orientedPartner x) ≠ x := by
  by_cases hx : A.vertexColor x = false
  · rw [A.orientedPartner_eq_first_of_color_false x hx]
    have hneighbor : A.vertexColor (A.first.perm x) ≠ false := by
      rw [A.vertexColor_first, hx]
      decide
    rw [A.orientedPartner_eq_second_of_color_ne_false _ hneighbor]
    intro h
    apply A.distinct x
    have h' := congrArg A.second.perm h
    change A.second.perm (A.second.perm (A.first.perm x)) = A.second.perm x at h'
    rw [A.second.apply_apply] at h'
    exact h'
  · rw [A.orientedPartner_eq_second_of_color_ne_false x hx]
    have hneighbor : A.vertexColor (A.second.perm x) = false := by
      rw [A.vertexColor_second]
      simpa [hx]
    rw [A.orientedPartner_eq_first_of_color_false _ hneighbor]
    intro h
    apply A.distinct x
    have h' := congrArg A.first.perm h
    change A.first.perm (A.first.perm (A.second.perm x)) = A.first.perm x at h'
    rw [A.first.apply_apply] at h'
    exact h'.symm

end AlternatingPairing

end Graph
end Foundations
end AppliedModelingLib
