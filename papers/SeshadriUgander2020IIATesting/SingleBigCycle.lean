import SeshadriUgander2020IIATesting.AllEvenSubsetsTesting

/-!
# The source's single pair-comparison cycle

For `n ≥ 3`, choice set `i` compares item `i` with its successor in the
cyclic order on `Fin n`.  This is the elementary special comparison frame in
Section 7 of Seshadri--Ugander (2020).
-/

namespace SeshadriUgander2020IIATesting

namespace SingleBigCycle

private theorem rotate_ne (k : ℕ) (i : Fin (k + 3)) :
    finRotate (k + 3) i ≠ i := by
  by_cases hlast : i = Fin.last (k + 2)
  · subst i
    rw [finRotate_last]
    intro h
    have hval := congrArg Fin.val h
    simp at hval
  · intro h
    have hval := congrArg Fin.val h
    rw [coe_finRotate_of_ne_last hlast] at hval
    omega

private theorem inverse_rotate_ne (k : ℕ) (x : Fin (k + 3)) :
    x ≠ (finRotate (k + 3)).symm x := by
  intro h
  apply rotate_ne k x
  have h' := (finRotate (k + 3)).apply_symm_apply x
  rw [← h] at h'
  exact h'

/-- The `n` pairwise comparisons arranged in a cyclic order. -/
def frame (k : ℕ) : ChoiceFrame where
  Item := Fin (k + 3)
  instFintypeItem := by infer_instance
  instDecidableEqItem := by infer_instance
  SetId := Fin (k + 3)
  instFintypeSetId := by infer_instance
  instDecidableEqSetId := by infer_instance
  members C := Finset.cons C {finRotate (k + 3) C} (by
    intro h
    exact rotate_ne k C (Finset.mem_singleton.mp h).symm)
  nonempty_sets := ⟨0⟩
  card_two_le C := by
    rw [Finset.card_cons]
    norm_num

@[simp] theorem members_card (k : ℕ) (C : (frame k).SetId) :
    ((frame k).members C).card = 2 := by
  unfold frame
  rw [Finset.card_cons]
  norm_num

private theorem occurrences_eq_pair (k : ℕ) (x : (frame k).Item) :
    (frame k).occurrences x = Finset.cons x {(finRotate (k + 3)).symm x}
      (by
        intro h
        exact inverse_rotate_ne k x (Finset.mem_singleton.mp h)) := by
  have hC : ∀ C : Fin (k + 3),
      C ∉ ({finRotate (k + 3) C} : Finset (Fin (k + 3))) := by
    intro C hC
    exact rotate_ne k C (Finset.mem_singleton.mp hC).symm
  change Finset.univ.filter (fun C : Fin (k + 3) =>
    x ∈ Finset.cons C {finRotate (k + 3) C} (hC C)) =
      Finset.cons x {(finRotate (k + 3)).symm x} _
  ext C
  constructor
  · intro h
    have hx := (Finset.mem_filter.mp h).2
    rcases Finset.mem_cons.mp hx with hxc | hxr
    · apply Finset.mem_cons.mpr
      exact Or.inl hxc.symm
    · apply Finset.mem_cons.mpr
      apply Or.inr
      have hxr' : x = finRotate (k + 3) C := Finset.mem_singleton.mp hxr
      have h' := (finRotate (k + 3)).symm_apply_apply C
      have h'' : (finRotate (k + 3)).symm x = C := by
        rw [hxr']
        exact h'
      exact Finset.mem_singleton.mpr h''.symm
  · intro h
    rcases Finset.mem_cons.mp h with hcx | hcinv
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, Finset.mem_cons.mpr (Or.inl hcx.symm)⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, Finset.mem_cons.mpr (Or.inr ?_)⟩
      have hcinv' : C = (finRotate (k + 3)).symm x := Finset.mem_singleton.mp hcinv
      rw [hcinv']
      exact Finset.mem_singleton.mpr ((finRotate (k + 3)).apply_symm_apply x).symm

@[simp] theorem occurrences_card (k : ℕ) (x : (frame k).Item) :
    ((frame k).occurrences x).card = 2 := by
  rw [occurrences_eq_pair]
  let y : Fin (k + 3) := (finRotate (k + 3)).symm x
  have hxy : x ∉ ({y} : Finset (Fin (k + 3))) := by
    intro h
    exact inverse_rotate_ne k x (Finset.mem_singleton.mp h)
  change (Finset.cons x {y} hxy).card = 2
  calc
    (Finset.cons x {y} hxy).card = ({y} : Finset (Fin (k + 3))).card + 1 :=
      Finset.card_cons hxy
    _ = 2 := by norm_num

/-- Every item and every comparison vertex in the cyclic pair frame has
degree two, so its comparison-incidence graph is Eulerian. -/
theorem frame_eulerian (k : ℕ) : (frame k).Eulerian where
  set_even C := by simp
  item_even x := by simp

@[simp] theorem frame_itemCard (k : ℕ) : Fintype.card (frame k).Item = k + 3 :=
  by simpa [frame] using Fintype.card_fin (k + 3)

/-- The source incidence count for the single pair-comparison cycle. -/
theorem incidenceCount_eq_two_mul (k : ℕ) : (frame k).incidenceCount = 2 * (k + 3) := by
  change (∑ C : Fin (k + 3), ((frame k).members C).card) = 2 * (k + 3)
  simp_rw [members_card]
  rw [Finset.sum_const, Finset.card_univ]
  simp only [nsmul_eq_mul]
  rw [Fintype.card_fin]
  simp [Nat.add_mul, Nat.mul_add]
  exact Nat.mul_comm _ _

/-- The risk lower-bound expression is antitone in its chi-square exponent. -/
private theorem riskLower_antitone_exponent {a b : ℝ} (hab : a ≤ b) :
    1 / 2 - (1 / 4 : ℝ) * Real.sqrt (Real.exp b - 1) ≤
      1 / 2 - (1 / 4 : ℝ) * Real.sqrt (Real.exp a - 1) := by
  have hexp : Real.exp a ≤ Real.exp b := Real.exp_le_exp.mpr hab
  have hsqrt : Real.sqrt (Real.exp a - 1) ≤ Real.sqrt (Real.exp b - 1) :=
    Real.sqrt_le_sqrt (by linarith)
  linarith

/-- The source's finite lower-bound consequence for a pair-comparison cycle.
The explicit `128 n⁴` coefficient is a valid finite replacement for the
unspecified constant in the source's `c n⁴` exponent. -/
theorem productTestingLowerBound
    (k : ℕ) (δ : ℝ) (hδ_nonneg : 0 ≤ δ)
    (hsmall : 4 * ((k + 3 : ℕ) : ℝ) * δ ≤ 1) (N : ℕ) :
    ChoiceSystem.ProductTestingLowerBound (F := frame k) N δ
      (1 / 2 - (1 / 4 : ℝ) *
        Real.sqrt (Real.exp (128 * ((k + 3 : ℕ) : ℝ) ^ 4 *
          (N : ℝ) ^ 2 * δ ^ 4) - 1)) := by
  obtain ⟨P, hcomplete, W₀, hlength, _hsum⟩ :=
    (frame k).eulerian_incidenceGraph_exists_bounded_alternatingCycleDecomposition
      (frame_eulerian k)
  let D := (frame k).cycleDecompositionOfCompletePacking P hcomplete
  let W : D.AlternatingCycleWitness := by
    simpa [D] using W₀
  let t : ℝ := 2 * ((k + 3 : ℕ) : ℝ)
  let d : ℝ := ((frame k).incidenceCount : ℝ)
  have hmean' :=
    ((frame k).cycleDecompositionOfCompletePacking P hcomplete).cycleMean_le_of_forall_length_le
      (2 * Fintype.card (frame k).Item) hlength
  have hmean : D.cycleMean ≤ t := by
    simpa [D, t, frame_itemCard, Nat.cast_mul] using hmean'
  have hdispersion' :=
    ((frame k).cycleDecompositionOfCompletePacking P hcomplete).cycleDispersion_le_of_forall_length_le
      (2 * Fintype.card (frame k).Item) hlength
  have hdispersion :
      CycleMixture.cycleDispersion (frame k).incidenceCount D.length ≤ t := by
    simpa [D, t, frame_itemCard, Nat.cast_mul] using hdispersion'
  have hcount : d = t := by
    dsimp [d, t]
    rw [incidenceCount_eq_two_mul]
    norm_num
  have htpos : 0 < t := by
    dsimp [t]
    positivity
  have hsmallD : 2 * D.cycleMean * δ ≤ 1 := by
    calc
      2 * D.cycleMean * δ = D.cycleMean * (2 * δ) := by ring
      _ ≤ t * (2 * δ) :=
        mul_le_mul_of_nonneg_right hmean (by positivity)
      _ = 4 * ((k + 3 : ℕ) : ℝ) * δ := by
        dsimp [t]
        ring
      _ ≤ 1 := hsmall
  have hbase := D.theorem1_productTestingLowerBound W δ hδ_nonneg hsmallD N
  let a : ℝ :=
    (8 * D.cycleMean ^ 4 *
      CycleMixture.cycleDispersion (frame k).incidenceCount D.length *
        (N : ℝ) ^ 2 * δ ^ 4) / d
  let b : ℝ := (8 * t ^ 5 * (N : ℝ) ^ 2 * δ ^ 4) / d
  have hdisp_nonneg : 0 ≤
      CycleMixture.cycleDispersion (frame k).incidenceCount D.length := by
    unfold CycleMixture.cycleDispersion
    positivity
  have hmean_pow : D.cycleMean ^ 4 ≤ t ^ 4 :=
    pow_le_pow_left₀ D.cycleMean_pos.le hmean 4
  have hproduct : D.cycleMean ^ 4 *
      CycleMixture.cycleDispersion (frame k).incidenceCount D.length ≤ t ^ 5 := by
    calc
      D.cycleMean ^ 4 *
          CycleMixture.cycleDispersion (frame k).incidenceCount D.length ≤
          t ^ 4 * CycleMixture.cycleDispersion (frame k).incidenceCount D.length :=
        mul_le_mul_of_nonneg_right hmean_pow hdisp_nonneg
      _ ≤ t ^ 4 * t :=
        mul_le_mul_of_nonneg_left hdispersion (pow_nonneg htpos.le 4)
      _ = t ^ 5 := by ring
  have hfactor : 0 ≤ 8 * (N : ℝ) ^ 2 * δ ^ 4 := by positivity
  have hab : a ≤ b := by
    dsimp [a, b]
    calc
      (8 * D.cycleMean ^ 4 *
          CycleMixture.cycleDispersion (frame k).incidenceCount D.length *
            (N : ℝ) ^ 2 * δ ^ 4) / d =
          (D.cycleMean ^ 4 *
            CycleMixture.cycleDispersion (frame k).incidenceCount D.length) *
              (8 * (N : ℝ) ^ 2 * δ ^ 4) / d := by ring
      _ ≤ t ^ 5 * (8 * (N : ℝ) ^ 2 * δ ^ 4) / d :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hproduct hfactor) (htpos.le.trans (le_of_eq hcount.symm))
      _ = (8 * t ^ 5 * (N : ℝ) ^ 2 * δ ^ 4) / d := by ring
  have hratio : b = 128 * ((k + 3 : ℕ) : ℝ) ^ 4 * (N : ℝ) ^ 2 * δ ^ 4 := by
    dsimp [b, t, d]
    rw [incidenceCount_eq_two_mul]
    norm_num
    field_simp
    ring
  have hlower :
      1 / 2 - (1 / 4 : ℝ) *
          Real.sqrt (Real.exp (128 * ((k + 3 : ℕ) : ℝ) ^ 4 *
            (N : ℝ) ^ 2 * δ ^ 4) - 1) ≤
        1 / 2 - (1 / 4 : ℝ) * Real.sqrt (Real.exp a - 1) := by
    rw [← hratio]
    exact riskLower_antitone_exponent hab
  intro φ
  obtain ⟨q, hseparated, herror⟩ := hbase φ
  refine ⟨q, hseparated, ?_⟩
  apply hlower.trans
  simpa [a, d] using herror

end SingleBigCycle

end SeshadriUgander2020IIATesting
