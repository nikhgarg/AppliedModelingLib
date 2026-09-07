import SeshadriUgander2020IIATesting.AppendixCyclePackingComposition
import AppliedModelingLib.Foundations.Graph.AlternatingPairing
import AppliedModelingLib.Foundations.Math.FinsetParity

/-!
# The all-even-subsets comparison frame

The appendix corollary specializes the comparison graph to every nonempty
even-cardinality subset.  Empty sets contribute no observations and are
excluded so that the source's standing choice-set-size hypothesis remains
literal.
-/

namespace SeshadriUgander2020IIATesting

/-- The nonempty even-cardinality choice sets on `Fin n`. -/
abbrev AllEvenChoiceSet (n : ℕ) :=
  {s : Finset (Fin n) // 2 ≤ s.card ∧ Even s.card}

namespace AllEvenChoiceSet

private def togglePair {α : Type} [DecidableEq α] (a b : α) (s : Finset α) :
    Finset α :=
  if ha : a ∈ s then
    if hb : b ∈ s then (s.erase a).erase b else insert b (s.erase a)
  else if hb : b ∈ s then insert a (s.erase b) else insert b (insert a s)

private theorem mem_togglePair_left {α : Type} [DecidableEq α]
    {a b : α} (hab : a ≠ b) (s : Finset α) :
    a ∈ togglePair a b s ↔ a ∉ s := by
  by_cases ha : a ∈ s <;> by_cases hb : b ∈ s <;>
    simp [togglePair, ha, hb, hab]

private theorem togglePair_ne {α : Type} [DecidableEq α]
    {a b : α} (hab : a ≠ b) (s : Finset α) :
    togglePair a b s ≠ s := by
  intro h
  have hmem : a ∈ s ↔ a ∉ s := by
    simpa [h] using mem_togglePair_left hab s
  by_cases ha : a ∈ s
  · exact (hmem.mp ha) ha
  · exact ha (hmem.mpr ha)

private theorem togglePair_involutive {α : Type} [DecidableEq α]
    {a b : α} (hab : a ≠ b) (s : Finset α) :
    togglePair a b (togglePair a b s) = s := by
  by_cases ha : a ∈ s
  · by_cases hb : b ∈ s
    · ext c
      simp [togglePair, ha, hb, hab, hab.symm]
      constructor
      · intro h
        rcases h with hcb | hca | hrest
        · simpa [hcb] using hb
        · simpa [hca] using ha
        · exact hrest.2.2
      · intro hc
        by_cases hcb : c = b
        · exact Or.inl hcb
        · by_cases hca : c = a
          · exact Or.inr (Or.inl hca)
          · exact Or.inr (Or.inr ⟨hcb, hca, hc⟩)
    · ext c
      simp [togglePair, ha, hb, hab, hab.symm]
  · by_cases hb : b ∈ s
    · ext c
      simp [togglePair, ha, hb, hab, hab.symm]
    · ext c
      simp [togglePair, ha, hb, hab, hab.symm]
      constructor
      · intro h
        rcases h.2.2 with hcb | hca | hc
        · exact False.elim (h.1 hcb)
        · exact False.elim (h.2.1 hca)
        · exact hc
      · intro hc
        refine ⟨?_, ?_, Or.inr (Or.inr hc)⟩
        · intro hcb
          apply hb
          simpa [hcb] using hc
        · intro hca
          apply ha
          simpa [hca] using hc

private theorem even_card_togglePair {α : Type} [DecidableEq α]
    {a b : α} (hab : a ≠ b) (s : Finset α) (hs : Even s.card) :
    Even (togglePair a b s).card := by
  by_cases ha : a ∈ s
  · by_cases hb : b ∈ s
    · have hcard : (togglePair a b s).card = s.card - 2 := by
        simp [togglePair, ha, hb, hab.symm, Nat.sub_sub]
      rw [hcard]
      have htwole : 2 ≤ s.card := by
        calc
          2 = ({a, b} : Finset α).card := by simp [hab]
          _ ≤ s.card := Finset.card_le_card (by
            intro c hc
            simp only [Finset.mem_insert, Finset.mem_singleton] at hc
            rcases hc with rfl | rfl
            · exact ha
            · exact hb)
      exact (Nat.even_sub htwole).mpr ⟨fun _ => even_two, fun _ => hs⟩
    · have hcard : (togglePair a b s).card = s.card := by
        have hpos : 0 < s.card := Finset.card_pos.mpr ⟨a, ha⟩
        simp [togglePair, ha, hb]
        omega
      simpa [hcard] using hs
  · by_cases hb : b ∈ s
    · have hcard : (togglePair a b s).card = s.card := by
        have hpos : 0 < s.card := Finset.card_pos.mpr ⟨b, hb⟩
        simp [togglePair, ha, hb, hab]
        omega
      simpa [hcard] using hs
    · have hcard : (togglePair a b s).card = s.card + 2 := by
        simp [togglePair, ha, hb, hab.symm, add_comm, add_left_comm]
      rw [hcard]
      exact hs.add even_two

private theorem mem_togglePair_of_ne {α : Type} [DecidableEq α]
    {a b x : α} (hxa : x ≠ a) (hxb : x ≠ b) (s : Finset α) :
    x ∈ togglePair a b s ↔ x ∈ s := by
  by_cases ha : a ∈ s <;> by_cases hb : b ∈ s <;>
    simp [togglePair, ha, hb, hxa, hxb]

private def first (n : ℕ) (hn : 2 ≤ n) : Fin n :=
  ⟨0, lt_of_lt_of_le (by omega) hn⟩

private def second (n : ℕ) (hn : 2 ≤ n) : Fin n :=
  ⟨1, lt_of_lt_of_le (by omega) hn⟩

private theorem first_ne_second (n : ℕ) (hn : 2 ≤ n) :
    first n hn ≠ second n hn := by
  intro h
  have := congrArg Fin.val h
  simp [first, second] at this

/-- The source's all-even-subsets choice frame. -/
noncomputable def frame (n : ℕ) (hn : 2 ≤ n) : ChoiceFrame where
  Item := Fin n
  instFintypeItem := inferInstance
  instDecidableEqItem := inferInstance
  SetId := AllEvenChoiceSet n
  instFintypeSetId := inferInstance
  instDecidableEqSetId := inferInstance
  members := fun C => C.1
  nonempty_sets := by
    refine ⟨⟨{first n hn, second n hn}, ?_⟩⟩
    constructor
    · simp [first_ne_second n hn]
    · simp [first_ne_second n hn]
  card_two_le := fun C => C.2.1

@[simp] theorem frame_itemCard (n : ℕ) (hn : 2 ≤ n) :
    Fintype.card (frame n hn).Item = n := by
  change Fintype.card (Fin n) = n
  exact Fintype.card_fin n

private def otherFirst (k : ℕ) (x : Fin (k + 3)) : Fin (k + 3) :=
  x.succAbove 0

private def otherSecond (k : ℕ) (x : Fin (k + 3)) : Fin (k + 3) :=
  x.succAbove 1

private theorem otherFirst_ne (k : ℕ) (x : Fin (k + 3)) :
    otherFirst k x ≠ x :=
  Fin.succAbove_ne _ _

private theorem otherSecond_ne (k : ℕ) (x : Fin (k + 3)) :
    otherSecond k x ≠ x :=
  Fin.succAbove_ne _ _

private theorem otherFirst_ne_otherSecond (k : ℕ) (x : Fin (k + 3)) :
    otherFirst k x ≠ otherSecond k x := by
  intro h
  apply Fin.zero_ne_one
  exact Fin.succAbove_right_injective h

private def occurrenceToggle (k : ℕ) (x : Fin (k + 3))
    (C : {C : (frame (k + 3) (by omega)).SetId //
      x ∈ (frame (k + 3) (by omega)).members C}) :
    {C : (frame (k + 3) (by omega)).SetId //
      x ∈ (frame (k + 3) (by omega)).members C} := by
  let a := otherFirst k x
  let b := otherSecond k x
  refine ⟨⟨togglePair a b C.1.1, ?_⟩, ?_⟩
  constructor
  · have heven := even_card_togglePair (otherFirst_ne_otherSecond k x) C.1.1 C.1.2.2
    have hx : x ∈ togglePair a b C.1.1 := by
      apply (mem_togglePair_of_ne (a := a) (b := b)
        (by simpa [a] using (otherFirst_ne k x).symm)
        (by simpa [b] using (otherSecond_ne k x).symm) C.1.1).mpr
      simpa [frame] using C.2
    rcases heven with ⟨q, hq⟩
    have hpos : 0 < (togglePair a b C.1.1).card := Finset.card_pos.mpr ⟨x, hx⟩
    rw [hq] at hpos ⊢
    omega
  · exact even_card_togglePair (otherFirst_ne_otherSecond k x) C.1.1 C.1.2.2
  · simpa [frame] using
      (mem_togglePair_of_ne (a := a) (b := b)
        (by simpa [a] using (otherFirst_ne k x).symm)
        (by simpa [b] using (otherSecond_ne k x).symm) C.1.1).mpr C.2

private theorem occurrenceToggle_involutive (k : ℕ) (x : Fin (k + 3))
    (C : {C : (frame (k + 3) (by omega)).SetId //
      x ∈ (frame (k + 3) (by omega)).members C}) :
    occurrenceToggle k x (occurrenceToggle k x C) = C := by
  apply Subtype.ext
  apply Subtype.ext
  exact togglePair_involutive (otherFirst_ne_otherSecond k x) C.1.1

private theorem occurrenceToggle_ne (k : ℕ) (x : Fin (k + 3))
    (C : {C : (frame (k + 3) (by omega)).SetId //
      x ∈ (frame (k + 3) (by omega)).members C}) :
    occurrenceToggle k x C ≠ C := by
  intro h
  have hval := congrArg (fun D => D.1.1) h
  exact togglePair_ne (otherFirst_ne_otherSecond k x) C.1.1 hval

private noncomputable def occurrencePairing (k : ℕ) (x : Fin (k + 3)) :
    AppliedModelingLib.Foundations.Graph.EvenPairing
      {C : (frame (k + 3) (by omega)).SetId //
        x ∈ (frame (k + 3) (by omega)).members C} where
  perm :=
    { toFun := occurrenceToggle k x
      invFun := occurrenceToggle k x
      left_inv := occurrenceToggle_involutive k x
      right_inv := occurrenceToggle_involutive k x }
  apply_apply := occurrenceToggle_involutive k x
  apply_ne := occurrenceToggle_ne k x

/-- Every item occurs in an even number of nonempty even-cardinality sets
once the item universe has at least three elements. -/
theorem occurrence_even (k : ℕ) (x : Fin (k + 3)) :
    Even ((frame (k + 3) (by omega)).occurrences x).card := by
  rw [← (frame (k + 3) (by omega)).occurrence_card x]
  exact AppliedModelingLib.Foundations.Graph.EvenPairing.even_card (occurrencePairing k x)

/-- The all-even-subsets comparison incidence graph is Eulerian for `n ≥ 3`.
The excluded `n = 2` case has one nonempty choice set and odd item degrees. -/
theorem frame_eulerian (k : ℕ) : (frame (k + 3) (by omega)).Eulerian where
  set_even := fun C => C.2.2
  item_even := occurrence_even k

/-- Odd-cardinality subsets of a finite item complement. -/
private abbrev OddFinsets (m : ℕ) :=
  AppliedModelingLib.Foundations.Math.FinsetParity.OddFinsets (Fin m)

/-- An occurrence of `x` in the all-even-subsets frame. -/
private abbrev Occurrence (k : ℕ) (x : Fin (k + 3)) :=
  {C : (frame (k + 3) (by omega)).SetId //
    x ∈ (frame (k + 3) (by omega)).members C}

/-- Removing the distinguished item converts an even choice set containing it
into an odd subset of the remaining `k + 2` items. -/
private noncomputable def occurrenceEncode (k : ℕ) (x : Fin (k + 3)) (C : Occurrence k x) :
    OddFinsets (k + 2) := by
  let e := x.succAboveEmb
  let R := C.1.1.erase x
  refine ⟨R.preimage e e.injective.injOn, ?_⟩
  have hx : x ∈ C.1.1 := by simpa [frame] using C.2
  have hmap : (R.preimage e e.injective.injOn).map e = R := by
    apply Finset.Subset.antisymm
    · intro z hz
      rcases Finset.mem_map.mp hz with ⟨w, hw, rfl⟩
      exact Finset.mem_preimage.mp hw
    · intro z hz
      have hzx : z ≠ x := (Finset.mem_erase.mp hz).1
      have hzrange : z ∈ Set.range e := by
        change z ∈ Set.range x.succAbove
        rw [Fin.range_succAbove]
        simpa using hzx
      rcases hzrange with ⟨w, hw⟩
      refine Finset.mem_map.mpr ⟨w, ?_, ?_⟩
      · apply Finset.mem_preimage.mpr
        simpa [R, e, hw] using hz
      · simpa [e] using hw
  have hcard : (R.preimage e e.injective.injOn).card = R.card := by
    have h := congrArg Finset.card hmap
    simpa using h
  rw [hcard]
  have hsize : 1 ≤ C.1.1.card := Nat.le_trans (by decide) C.1.2.1
  simpa [R, Finset.card_erase_of_mem hx] using
    Nat.Even.sub_odd hsize C.1.2.2 odd_one

private theorem occurrenceEncode_map (k : ℕ) (x : Fin (k + 3)) (C : Occurrence k x) :
    (occurrenceEncode k x C).1.map x.succAboveEmb = C.1.1.erase x := by
  let e := x.succAboveEmb
  let R := C.1.1.erase x
  change (R.preimage e e.injective.injOn).map e = R
  apply Finset.Subset.antisymm
  · intro z hz
    rcases Finset.mem_map.mp hz with ⟨w, hw, rfl⟩
    exact Finset.mem_preimage.mp hw
  · intro z hz
    have hzx : z ≠ x := (Finset.mem_erase.mp hz).1
    have hzrange : z ∈ Set.range e := by
      change z ∈ Set.range x.succAbove
      rw [Fin.range_succAbove]
      simpa using hzx
    rcases hzrange with ⟨w, hw⟩
    refine Finset.mem_map.mpr ⟨w, ?_, ?_⟩
    · apply Finset.mem_preimage.mpr
      simpa [R, e, hw] using hz
    · simpa [e] using hw

/-- Inserting a distinguished item into an odd subset of its complement
reconstructs an even choice set containing that item. -/
private def occurrenceDecode (k : ℕ) (x : Fin (k + 3)) (S : OddFinsets (k + 2)) :
    Occurrence k x := by
  let e := x.succAboveEmb
  have hxnot : x ∉ S.1.map e := by
    intro hx
    rcases Finset.mem_map.mp hx with ⟨z, hz, hzx⟩
    exact Fin.succAbove_ne x z (by simpa [e] using hzx)
  refine ⟨⟨insert x (S.1.map e), ?_⟩, ?_⟩
  · constructor
    · rcases S.2 with ⟨q, hq⟩
      rw [Finset.card_insert_of_notMem hxnot, Finset.card_map, hq]
      omega
    · rw [Finset.card_insert_of_notMem hxnot, Finset.card_map]
      rcases S.2 with ⟨q, hq⟩
      refine ⟨q + 1, ?_⟩
      omega
  · exact Finset.mem_insert_self _ _

private theorem occurrenceDecode_encode (k : ℕ) (x : Fin (k + 3))
    (C : Occurrence k x) :
    occurrenceDecode k x (occurrenceEncode k x C) = C := by
  apply Subtype.ext
  apply Subtype.ext
  change insert x ((occurrenceEncode k x C).1.map x.succAboveEmb) = C.1.1
  rw [occurrenceEncode_map]
  exact Finset.insert_erase (by simpa [frame] using C.2)

private theorem occurrenceEncode_decode (k : ℕ) (x : Fin (k + 3))
    (S : OddFinsets (k + 2)) :
    occurrenceEncode k x (occurrenceDecode k x S) = S := by
  apply Subtype.ext
  let e := x.succAboveEmb
  have hxnot : x ∉ S.1.map e := by
    intro hx
    rcases Finset.mem_map.mp hx with ⟨z, hz, hzx⟩
    exact Fin.succAbove_ne x z (by simpa [e] using hzx)
  change ((insert x (S.1.map e)).erase x).preimage e e.injective.injOn = S.1
  rw [Finset.erase_insert hxnot]
  exact Finset.preimage_map e S.1

private noncomputable def occurrenceEquivOdd (k : ℕ) (x : Fin (k + 3)) :
    Occurrence k x ≃ OddFinsets (k + 2) where
  toFun := occurrenceEncode k x
  invFun := occurrenceDecode k x
  left_inv := occurrenceDecode_encode k x
  right_inv := occurrenceEncode_decode k x

/-- Each item belongs to exactly `2^(n-2)` nonempty even-cardinality choice
sets when `n = k + 3`. -/
theorem occurrence_card_eq_pow (k : ℕ) (x : Fin (k + 3)) :
    ((frame (k + 3) (by omega)).occurrences x).card = 2 ^ (k + 1) := by
  calc
    ((frame (k + 3) (by omega)).occurrences x).card = Fintype.card (Occurrence k x) :=
      (frame (k + 3) (by omega)).occurrence_card x |>.symm
    _ = Fintype.card (OddFinsets (k + 2)) :=
      Fintype.card_congr (occurrenceEquivOdd k x)
    _ = 2 ^ (k + 1) := by
      simpa [show k + 2 = (k + 1) + 1 by omega] using
        AppliedModelingLib.Foundations.Math.FinsetParity.card_oddFinsets_fin_succ (k + 1)

/-- The all-even-subsets frame has the exact source incidence count
`n 2^(n-2)` for `n = k + 3`. -/
theorem incidenceCount_eq_source (k : ℕ) :
    (frame (k + 3) (by omega)).incidenceCount = (k + 3) * 2 ^ (k + 1) := by
  rw [← (frame (k + 3) (by omega)).sum_occurrence_card_eq_incidenceCount]
  simp_rw [occurrence_card_eq_pow]
  change (∑ _ : Fin (k + 3), 2 ^ (k + 1)) = (k + 3) * 2 ^ (k + 1)
  simp

/-- Appendix Lemma 10 specialized to the concrete all-even-subsets frame:
the source-capped short phase and a complete `2n` residual phase produce
source-faithful two-tier cycle bounds. -/
noncomputable def sourceTwoTierCycleBounds (k : ℕ) :=
  (frame (k + 3) (by omega)).eulerian_incidenceGraph_exists_source_twoTierCycleBounds
    (frame_eulerian k)

private theorem nat_le_two_pow (r : ℕ) : r ≤ 2 ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
    cases r with
    | zero => norm_num
    | succ r =>
      calc
        Nat.succ (Nat.succ r) ≤ 2 * Nat.succ r := by omega
        _ ≤ 2 * 2 ^ Nat.succ r := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ Nat.succ (Nat.succ r) := by
          simp [pow_succ, Nat.mul_comm]

private theorem four_mul_sub_le_two_pow (n : ℕ) (hn : 4 ≤ n) :
    4 * (n - 4) ≤ 2 ^ (n - 2) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hpow : 4 * 2 ^ r = 2 ^ (4 + r - 2) := by
    rw [show 4 + r - 2 = r + 2 by omega, pow_add]
    ring
  calc
    4 * (4 + r - 4) = 4 * r := by omega
    _ ≤ 4 * 2 ^ r := Nat.mul_le_mul_left 4 (nat_le_two_pow r)
    _ = 2 ^ (4 + r - 2) := hpow

private theorem two_le_logb_two (n : ℕ) (hn : 4 ≤ n) :
    (2 : ℝ) ≤ Real.logb 2 (n : ℝ) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by omega) hn)
  apply (Real.le_logb_iff_rpow_le (by norm_num) hnpos).mpr
  calc
    (2 : ℝ) ^ (2 : ℝ) = 4 := by norm_num
    _ ≤ (n : ℝ) := by exact_mod_cast hn

private theorem alpha_source_expression_le_five_log (n : ℕ) (hn : 4 ≤ n) :
    4 * Real.logb 2 (n : ℝ) +
        (4 * (n : ℝ) * (2 * (n : ℝ) - 4 * Real.logb 2 (n : ℝ))) /
          ((n : ℝ) * (2 ^ (n - 2) : ℕ)) ≤
      5 * Real.logb 2 (n : ℝ) := by
  let l : ℝ := Real.logb 2 (n : ℝ)
  let e : ℝ := (2 ^ (n - 2) : ℕ)
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by omega) hn)
  have hepos : 0 < e := by
    dsimp [e]
    positivity
  have hlog : 2 ≤ l := two_le_logb_two n hn
  have hpowNat := four_mul_sub_le_two_pow n hn
  have hpow : 4 * ((n : ℝ) - 4) ≤ e := by
    dsimp [e]
    exact_mod_cast hpowNat
  have hfactor : 2 * (n : ℝ) - 4 * l ≤ 2 * ((n : ℝ) - 4) := by
    dsimp [l] at hlog ⊢
    linarith
  have hnum :
      4 * (n : ℝ) * (2 * (n : ℝ) - 4 * l) ≤ 2 * ((n : ℝ) * e) := by
    calc
      4 * (n : ℝ) * (2 * (n : ℝ) - 4 * l) ≤
          4 * (n : ℝ) * (2 * ((n : ℝ) - 4)) :=
        mul_le_mul_of_nonneg_left hfactor (by positivity)
      _ = (2 * (n : ℝ)) * (4 * ((n : ℝ) - 4)) := by ring
      _ ≤ (2 * (n : ℝ)) * e :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = 2 * ((n : ℝ) * e) := by ring
  have hdiv :
      (4 * (n : ℝ) * (2 * (n : ℝ) - 4 * l)) / ((n : ℝ) * e) ≤ 2 := by
    apply (div_le_iff₀ (mul_pos hnpos hepos)).mpr
    nlinarith
  change 4 * l +
      (4 * (n : ℝ) * (2 * (n : ℝ) - 4 * l)) / ((n : ℝ) * e) ≤ 5 * l
  linarith

private theorem mean_source_expression_le_five_log (n : ℕ) (hn : 4 ≤ n)
    (hden : 0 < (n : ℝ) * (2 ^ (n - 2) : ℕ) - 4 * (n : ℝ) +
      2 * (4 * Real.logb 2 (n : ℝ))) :
    ((n : ℝ) * (2 ^ (n - 2) : ℕ) * (4 * Real.logb 2 (n : ℝ))) /
        ((n : ℝ) * (2 ^ (n - 2) : ℕ) - 4 * (n : ℝ) +
          2 * (4 * Real.logb 2 (n : ℝ))) ≤
      5 * Real.logb 2 (n : ℝ) := by
  let l : ℝ := Real.logb 2 (n : ℝ)
  let e : ℝ := (2 ^ (n - 2) : ℕ)
  let d : ℝ := (n : ℝ) * e
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by omega) hn)
  have hlog : 2 ≤ l := two_le_logb_two n hn
  have hpowNat := four_mul_sub_le_two_pow n hn
  have hpow : 4 * ((n : ℝ) - 4) ≤ e := by
    dsimp [e]
    exact_mod_cast hpowNat
  have hde : 4 * (n : ℝ) * ((n : ℝ) - 4) ≤ d := by
    calc
      4 * (n : ℝ) * ((n : ℝ) - 4) = (n : ℝ) * (4 * ((n : ℝ) - 4)) := by ring
      _ ≤ (n : ℝ) * e := mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = d := rfl
  have hpoly : 20 * (n : ℝ) ≤ 4 * (n : ℝ) * ((n : ℝ) - 4) + 80 := by
    by_cases hfour : n = 4
    · subst n
      norm_num
    · have hfive : 5 ≤ n := by omega
      have hprod : 0 ≤ ((n : ℝ) - 4) * ((n : ℝ) - 5) :=
        mul_nonneg (sub_nonneg.mpr (by exact_mod_cast hn))
          (sub_nonneg.mpr (by exact_mod_cast hfive))
      nlinarith
  have hbudget : 20 * (n : ℝ) ≤ d + 40 * l := by
    calc
      20 * (n : ℝ) ≤ 4 * (n : ℝ) * ((n : ℝ) - 4) + 80 := hpoly
      _ ≤ d + 40 * l := by
        apply add_le_add hde
        nlinarith
  have hcore : 4 * d ≤ 5 * (d - 4 * (n : ℝ) + 8 * l) := by
    nlinarith
  have hmul : d * (4 * l) ≤ 5 * l * (d - 4 * (n : ℝ) + 8 * l) := by
    calc
      d * (4 * l) = (4 * d) * l := by ring
      _ ≤ (5 * (d - 4 * (n : ℝ) + 8 * l)) * l :=
        mul_le_mul_of_nonneg_right hcore (by linarith)
      _ = 5 * l * (d - 4 * (n : ℝ) + 8 * l) := by ring
  change (d * (4 * l)) / (d - 4 * (n : ℝ) + 2 * (4 * l)) ≤ 5 * l
  apply (div_le_iff₀ (by simpa [d, e, l] using hden)).mpr
  convert hmul using 1; ring

private theorem source_denominator_pos (n : ℕ) (hn : 4 ≤ n) :
    0 < (n : ℝ) * (2 ^ (n - 2) : ℕ) - 4 * (n : ℝ) +
      2 * (4 * Real.logb 2 (n : ℝ)) := by
  let l : ℝ := Real.logb 2 (n : ℝ)
  let e : ℝ := (2 ^ (n - 2) : ℕ)
  let d : ℝ := (n : ℝ) * e
  have hlog : 2 ≤ l := two_le_logb_two n hn
  have hpowNat := four_mul_sub_le_two_pow n hn
  have hpow : 4 * ((n : ℝ) - 4) ≤ e := by
    dsimp [e]
    exact_mod_cast hpowNat
  by_cases hfour : n = 4
  · subst n
    have hlog' : (2 : ℝ) ≤ Real.logb 2 (4 : ℝ) := by simpa [l] using hlog
    have hpositive : (0 : ℝ) < 8 * Real.logb 2 (4 : ℝ) := by nlinarith
    convert hpositive using 1; norm_num; ring
  · have hfive : 5 ≤ n := by omega
    have hde : 4 * (n : ℝ) ≤ d := by
      calc
        4 * (n : ℝ) = (n : ℝ) * 4 := by ring
        _ ≤ (n : ℝ) * e := by
          apply mul_le_mul_of_nonneg_left
          · calc
              (4 : ℝ) ≤ 4 * ((n : ℝ) - 4) := by
                have : (1 : ℝ) ≤ (n : ℝ) - 4 := by
                  exact_mod_cast (show 1 ≤ n - 4 by omega)
                nlinarith
              _ ≤ e := hpow
          · positivity
        _ = d := rfl
    change 0 < d - 4 * (n : ℝ) + 2 * (4 * l)
    nlinarith

private theorem six_le_five_logb_three :
    (6 : ℝ) ≤ 5 * Real.logb 2 (3 : ℝ) := by
  have hpow : ((2 : ℝ) ^ ((6 : ℝ) / 5)) ^ (5 : ℝ) ≤ (3 : ℝ) ^ (5 : ℝ) := by
    calc
      ((2 : ℝ) ^ ((6 : ℝ) / 5)) ^ (5 : ℝ) =
          (2 : ℝ) ^ (((6 : ℝ) / 5) * 5) :=
        (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) _ _).symm
      _ = (2 : ℝ) ^ (6 : ℝ) := by norm_num
      _ = 64 := by norm_num [Real.rpow_natCast]
      _ ≤ (3 : ℝ) ^ (5 : ℝ) := by norm_num [Real.rpow_natCast]
  have hroot : (2 : ℝ) ^ ((6 : ℝ) / 5) ≤ 3 :=
    (Real.rpow_le_rpow_iff
      (Real.rpow_nonneg (by norm_num) _) (by norm_num) (by norm_num : (0 : ℝ) < 5)).mp hpow
  have hlog : (6 : ℝ) / 5 ≤ Real.logb 2 (3 : ℝ) :=
    (Real.le_logb_iff_rpow_le (by norm_num) (by norm_num)).mpr hroot
  linarith

/-- The concrete frame is Eulerian for every item count in its corrected
source range `n ≥ 3`. -/
theorem frame_eulerian_of_three (n : ℕ) (hn : 3 ≤ n) :
    (frame n (by omega)).Eulerian := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  simpa [Nat.add_comm] using frame_eulerian k

/-- The exact source incidence count in the corrected range `n ≥ 3`. -/
theorem incidenceCount_eq_source_of_three (n : ℕ) (hn : 3 ≤ n) :
    (frame n (by omega)).incidenceCount = n * 2 ^ (n - 2) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  simpa [Nat.add_comm, show k + 3 - 2 = k + 1 by omega] using
    incidenceCount_eq_source k

/-- Corrected Appendix Corollary: for the all-even-subsets frame with at
least four items, the constructed two-tier decomposition has both source
statistics bounded by `5 log₂ n`. -/
theorem exists_cycleDecomposition_five_log (n : ℕ) (hn : 4 ≤ n) :
    ∃ D : ChoiceSystem.CycleDecomposition (frame n (by omega)),
      D.cycleMean ≤ 5 * Real.logb 2 (n : ℝ) ∧
      CycleMixture.cycleDispersion (frame n (by omega)).incidenceCount D.length ≤
        5 * Real.logb 2 (n : ℝ) := by
  obtain ⟨P, Q, hbudget, hQcomplete⟩ :=
    (frame n (by omega)).eulerian_incidenceGraph_has_short_residual_cycle_packings
      (frame_eulerian_of_three n (by omega))
  have hitemNat : Fintype.card (frame n (by omega)).Item = n := frame_itemCard _ _
  have hitem : (Fintype.card (frame n (by omega)).Item : ℝ) = (n : ℝ) := by
    exact_mod_cast hitemNat
  have hincidence : ((frame n (by omega)).incidenceCount : ℝ) =
      (n : ℝ) * (2 ^ (n - 2) : ℕ) := by
    exact_mod_cast (incidenceCount_eq_source_of_three n (by omega))
  let D := (frame n (by omega)).composedCycleDecomposition P Q hQcomplete
  refine ⟨D, ?_, ?_⟩
  · have hfour : 4 ≤ Fintype.card (frame n (by omega)).Item := by
      rw [hitemNat]
      exact hn
    have hden : 0 < ((frame n (by omega)).incidenceCount : ℝ) -
        4 * (Fintype.card (frame n (by omega)).Item : ℝ) +
          2 * (4 * Real.logb 2 (Fintype.card (frame n (by omega)).Item)) := by
      rw [hincidence, hitem]
      exact source_denominator_pos n hn
    have hmean :=
      (frame n (by omega)).sourceComposed_cycleMean_le_source_min
        P Q hQcomplete hbudget hfour hden
    dsimp [D]
    refine (hmean.trans (min_le_left _ _)).trans ?_
    rw [hincidence, hitem]
    exact mean_source_expression_le_five_log n hn (source_denominator_pos n hn)
  · have hfour : 4 ≤ Fintype.card (frame n (by omega)).Item := by
      rw [hitemNat]
      exact hn
    have halpha :=
      (frame n (by omega)).sourceComposed_cycleDispersion_le_source_min
        P Q hQcomplete hbudget hfour
    dsimp [D]
    refine (halpha.trans (min_le_left _ _)).trans ?_
    rw [hincidence, hitem]
    exact alpha_source_expression_le_five_log n hn

/-- The corrected three-item edge case uses only the unconditional `2n`
cycle cap together with the exact inequality `6 ≤ 5 log₂ 3`. -/
theorem exists_cycleDecomposition_five_log_three :
    ∃ D : ChoiceSystem.CycleDecomposition (frame 3 (by omega)),
      D.cycleMean ≤ 5 * Real.logb 2 (3 : ℝ) ∧
      CycleMixture.cycleDispersion (frame 3 (by omega)).incidenceCount D.length ≤
        5 * Real.logb 2 (3 : ℝ) := by
  obtain ⟨P, Q, _hbudget, hQcomplete⟩ :=
    (frame 3 (by omega)).eulerian_incidenceGraph_has_short_residual_cycle_packings
      (frame_eulerian 0)
  let D := (frame 3 (by omega)).composedCycleDecomposition P Q hQcomplete
  refine ⟨D, ?_, ?_⟩
  · dsimp [D]
    calc
      ((frame 3 (by omega)).composedCycleDecomposition P Q hQcomplete).cycleMean ≤
          (6 : ℝ) :=
        by
          simpa [Nat.cast_mul] using
            (frame 3 (by omega)).sourceComposed_cycleMean_le_two_mul P Q hQcomplete
      _ ≤ 5 * Real.logb 2 (3 : ℝ) := six_le_five_logb_three
  · dsimp [D]
    calc
      CycleMixture.cycleDispersion (frame 3 (by omega)).incidenceCount
          ((frame 3 (by omega)).composedCycleDecomposition P Q hQcomplete).length ≤
          (6 : ℝ) :=
        by
          simpa [Nat.cast_mul] using
            (frame 3 (by omega)).sourceComposed_cycleDispersion_le_two_mul P Q hQcomplete
      _ ≤ 5 * Real.logb 2 (3 : ℝ) := six_le_five_logb_three

/-- Corrected Appendix Corollary over its full valid range.  The source's
`n = 2` endpoint is excluded because its all-even frame is not Eulerian. -/
theorem exists_cycleDecomposition_five_log_of_three (n : ℕ) (hn : 3 ≤ n) :
    ∃ D : ChoiceSystem.CycleDecomposition (frame n (by omega)),
      D.cycleMean ≤ 5 * Real.logb 2 (n : ℝ) ∧
      CycleMixture.cycleDispersion (frame n (by omega)).incidenceCount D.length ≤
        5 * Real.logb 2 (n : ℝ) := by
  by_cases hfour : 4 ≤ n
  · exact exists_cycleDecomposition_five_log n hfour
  · have hthree : n = 3 := by omega
    subst n
    exact exists_cycleDecomposition_five_log_three

/-- The corrected all-even-subsets corollary together with the concrete
alternating traversal needed to instantiate the paper's testing theorem. -/
theorem exists_cycleDecomposition_five_log_withWitness_of_three
    (n : ℕ) (hn : 3 ≤ n) :
    ∃ (D : ChoiceSystem.CycleDecomposition (frame n (by omega))),
      ∃ _W : D.AlternatingCycleWitness,
        D.cycleMean ≤ 5 * Real.logb 2 (n : ℝ) ∧
          CycleMixture.cycleDispersion (frame n (by omega)).incidenceCount D.length ≤
            5 * Real.logb 2 (n : ℝ) := by
  by_cases hfour : 4 ≤ n
  · obtain ⟨P, Q, hbudget, hQcomplete⟩ :=
      (frame n (by omega)).eulerian_incidenceGraph_has_short_residual_cycle_packings
        (frame_eulerian_of_three n (by omega))
    have hitemNat : Fintype.card (frame n (by omega)).Item = n := frame_itemCard _ _
    have hitem : (Fintype.card (frame n (by omega)).Item : ℝ) = (n : ℝ) := by
      exact_mod_cast hitemNat
    have hincidence : ((frame n (by omega)).incidenceCount : ℝ) =
        (n : ℝ) * (2 ^ (n - 2) : ℕ) := by
      exact_mod_cast (incidenceCount_eq_source_of_three n (by omega))
    let D := (frame n (by omega)).composedCycleDecomposition P Q hQcomplete
    let W := (frame n (by omega)).composedCycleDecomposition_alternatingCycleWitness
      P Q hQcomplete
    refine ⟨D, W, ?_, ?_⟩
    · have hfour' : 4 ≤ Fintype.card (frame n (by omega)).Item := by
        rw [hitemNat]
        exact hfour
      have hden : 0 < ((frame n (by omega)).incidenceCount : ℝ) -
          4 * (Fintype.card (frame n (by omega)).Item : ℝ) +
            2 * (4 * Real.logb 2 (Fintype.card (frame n (by omega)).Item)) := by
        rw [hincidence, hitem]
        exact source_denominator_pos n hfour
      have hmean :=
        (frame n (by omega)).sourceComposed_cycleMean_le_source_min
          P Q hQcomplete hbudget hfour' hden
      dsimp [D]
      refine (hmean.trans (min_le_left _ _)).trans ?_
      rw [hincidence, hitem]
      exact mean_source_expression_le_five_log n hfour (source_denominator_pos n hfour)
    · have hfour' : 4 ≤ Fintype.card (frame n (by omega)).Item := by
        rw [hitemNat]
        exact hfour
      have halpha :=
        (frame n (by omega)).sourceComposed_cycleDispersion_le_source_min
          P Q hQcomplete hbudget hfour'
      dsimp [D]
      refine (halpha.trans (min_le_left _ _)).trans ?_
      rw [hincidence, hitem]
      exact alpha_source_expression_le_five_log n hfour
  · have hthree : n = 3 := by omega
    subst n
    obtain ⟨P, Q, _hbudget, hQcomplete⟩ :=
      (frame 3 (by omega)).eulerian_incidenceGraph_has_short_residual_cycle_packings
        (frame_eulerian 0)
    let D := (frame 3 (by omega)).composedCycleDecomposition P Q hQcomplete
    let W := (frame 3 (by omega)).composedCycleDecomposition_alternatingCycleWitness
      P Q hQcomplete
    refine ⟨D, W, ?_, ?_⟩
    · dsimp [D]
      calc
        ((frame 3 (by omega)).composedCycleDecomposition P Q hQcomplete).cycleMean ≤
            (6 : ℝ) :=
          by
            simpa [Nat.cast_mul] using
              (frame 3 (by omega)).sourceComposed_cycleMean_le_two_mul P Q hQcomplete
        _ ≤ 5 * Real.logb 2 (3 : ℝ) := six_le_five_logb_three
    · dsimp [D]
      calc
        CycleMixture.cycleDispersion (frame 3 (by omega)).incidenceCount
            ((frame 3 (by omega)).composedCycleDecomposition P Q hQcomplete).length ≤
            (6 : ℝ) :=
          by
            simpa [Nat.cast_mul] using
              (frame 3 (by omega)).sourceComposed_cycleDispersion_le_two_mul P Q hQcomplete
        _ ≤ 5 * Real.logb 2 (3 : ℝ) := six_le_five_logb_three

theorem members_eq (n : ℕ) (hn : 2 ≤ n)
    (C : (frame n hn).SetId) :
    (frame n hn).members C = C.1 := rfl

end AllEvenChoiceSet

end SeshadriUgander2020IIATesting
