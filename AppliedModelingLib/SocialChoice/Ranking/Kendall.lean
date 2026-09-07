import AppliedModelingLib.SocialChoice.Ranking.Basic
import Mathlib.Data.Fin.SuccPredOrder
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Order.SuccPred.Archimedean
import Mathlib.Order.Interval.Finset.Fin

open scoped BigOperators

namespace AppliedModelingLib
namespace SocialChoice
namespace Ranking

/--
A pair of candidates is inverted by `π` relative to the reference ranking `ρ` when
`ρ` puts the first candidate above the second, but `π` puts the second above the
first.

This is the finite combinatorial core of the Mallows model: all Mallows weights
are powers of the number of such inversions.
-/
def invertedPair {n : ℕ} (ρ π : Ranking n) (ab : Candidate n × Candidate n) : Prop :=
  rankOf ρ ab.1 < rankOf ρ ab.2 ∧ rankOf π ab.2 < rankOf π ab.1

/-- The finite set of inversions of `π` relative to `ρ`. -/
noncomputable def inversionFinset {n : ℕ} (ρ π : Ranking n) :
    Finset (Candidate n × Candidate n) := by
  classical
  exact Finset.univ.filter (fun ab => invertedPair ρ π ab)

/-- Inversions involving a fixed candidate. -/
noncomputable def inversionFinsetInvolving {n : ℕ} (ρ π : Ranking n)
    (c : Candidate n) : Finset (Candidate n × Candidate n) := by
  classical
  exact (inversionFinset ρ π).filter (fun ab => ab.1 = c ∨ ab.2 = c)

/-- Inversions not involving a fixed candidate. -/
noncomputable def inversionFinsetNotInvolving {n : ℕ} (ρ π : Ranking n)
    (c : Candidate n) : Finset (Candidate n × Candidate n) := by
  classical
  exact (inversionFinset ρ π).filter (fun ab => ¬(ab.1 = c ∨ ab.2 = c))

/-- Inversions involving the second choice but not the first choice. -/
noncomputable def inversionFinsetInvolvingSecondNotFirst {n : ℕ}
    (ρ π : Ranking n) : Finset (Candidate n × Candidate n) := by
  classical
  exact (inversionFinset ρ π).filter
    (fun ab =>
      (ab.1 = secondChoice π ∨ ab.2 = secondChoice π) ∧
        ab.1 ≠ firstChoice π ∧ ab.2 ≠ firstChoice π)

/-- Kendall-tau distance from `π` to the reference ranking `ρ`. -/
noncomputable def kendallTau {n : ℕ} (ρ π : Ranking n) : ℕ :=
  (inversionFinset ρ π).card

@[simp] theorem invertedPair_self_false {n : ℕ} (ρ : Ranking n)
    (ab : Candidate n × Candidate n) :
    ¬ invertedPair ρ ρ ab := by
  intro h
  exact (lt_asymm h.1) h.2

@[simp] theorem inversionFinset_self {n : ℕ} (ρ : Ranking n) :
    inversionFinset ρ ρ = ∅ := by
  classical
  ext ab
  simp [inversionFinset]

@[simp] theorem kendallTau_self {n : ℕ} (ρ : Ranking n) :
    kendallTau ρ ρ = 0 := by
  simp [kendallTau]

theorem rankOf_ne_zero_of_ne_firstChoice {n : ℕ} (π : Ranking n)
    {c : Candidate n} (hc : c ≠ firstChoice π) :
    rankOf π c ≠ 0 := by
  intro h
  apply hc
  have hπ : π (rankOf π c) = c := by
    simp [rankOf]
  simpa [firstChoice, h] using hπ.symm

theorem zero_lt_rankOf_of_ne_firstChoice {n : ℕ} (π : Ranking n)
    {c : Candidate n} (hc : c ≠ firstChoice π) :
    (0 : Candidate n) < rankOf π c := by
  have hne := rankOf_ne_zero_of_ne_firstChoice π hc
  change 0 < (rankOf π c).val
  by_contra hnot
  have hzero : (rankOf π c).val = 0 := by omega
  exact hne (Fin.ext hzero)

theorem inversionFinsetInvolving_firstChoice_eq_image_Iio {n : ℕ}
    (ρ π : Ranking n) :
    inversionFinsetInvolving ρ π (firstChoice π) =
      (Finset.Iio (rankOf ρ (firstChoice π))).map
        ⟨fun i : Candidate n => (ρ i, firstChoice π),
          by
            intro i j h
            exact ρ.injective (Prod.ext_iff.mp h).1⟩ := by
  classical
  ext ab
  constructor
  · intro hab
    have hinv : ab ∈ inversionFinset ρ π :=
      (Finset.mem_filter.mp hab).1
    have hinvolves : ab.1 = firstChoice π ∨ ab.2 = firstChoice π :=
      (Finset.mem_filter.mp hab).2
    have hinv_prop : invertedPair ρ π ab := by
      simpa [inversionFinset] using hinv
    rcases hinvolves with hfirst | hsecond
    · exfalso
      have hrank_first : rankOf π ab.1 = 0 := by
        rw [hfirst]
        simp [rankOf, firstChoice]
      have hnonneg : ¬ rankOf π ab.2 < rankOf π ab.1 := by
        rw [hrank_first]
        exact not_lt_bot
      exact hnonneg hinv_prop.2
    · refine Finset.mem_map.mpr ?_
      refine ⟨rankOf ρ ab.1, ?_, ?_⟩
      · simpa [firstChoice, hsecond] using hinv_prop.1
      · ext <;> simp [rankOf, hsecond]
  · intro hab
    rcases Finset.mem_map.mp hab with ⟨i, hi, hab_eq⟩
    have hi_lt : i < rankOf ρ (firstChoice π) := by
      simpa using hi
    have hne : ρ i ≠ firstChoice π := by
      intro h
      have hi_eq : i = rankOf ρ (firstChoice π) := by
        simpa [rankOf] using congrArg ρ.symm h
      exact (lt_irrefl i) (hi_lt.trans_eq hi_eq.symm)
    have hπ : rankOf π (firstChoice π) < rankOf π (ρ i) := by
      simpa [rankOf, firstChoice] using
        zero_lt_rankOf_of_ne_firstChoice π hne
    have hinv : invertedPair ρ π (ρ i, firstChoice π) := by
      constructor
      · simpa [rankOf] using hi_lt
      · simpa using hπ
    have hinv' : invertedPair ρ π (ρ i, π 0) := by
      simpa [firstChoice] using hinv
    rw [← hab_eq]
    unfold inversionFinsetInvolving inversionFinset
    simp [hinv']

theorem inversionFinsetInvolving_firstChoice_card {n : ℕ}
    (ρ π : Ranking n) :
    (inversionFinsetInvolving ρ π (firstChoice π)).card =
      (rankOf ρ (firstChoice π) : ℕ) := by
  rw [inversionFinsetInvolving_firstChoice_eq_image_Iio]
  simp

theorem inversionFinsetInvolving_card_add_notInvolving_card {n : ℕ}
    (ρ π : Ranking n) (c : Candidate n) :
    (inversionFinsetInvolving ρ π c).card +
        (inversionFinsetNotInvolving ρ π c).card =
      (inversionFinset ρ π).card := by
  classical
  simpa [inversionFinsetInvolving, inversionFinsetNotInvolving] using
    (Finset.card_filter_add_card_filter_not
      (s := inversionFinset ρ π) (p := fun ab => ab.1 = c ∨ ab.2 = c))

theorem kendallTau_eq_firstChoice_rank_add_notInvolving_card {n : ℕ}
    (ρ π : Ranking n) :
    kendallTau ρ π =
      (rankOf ρ (firstChoice π) : ℕ) +
        (inversionFinsetNotInvolving ρ π (firstChoice π)).card := by
  rw [kendallTau]
  rw [← inversionFinsetInvolving_card_add_notInvolving_card
    (ρ := ρ) (π := π) (c := firstChoice π)]
  rw [inversionFinsetInvolving_firstChoice_card]

theorem rankOf_eq_zero_iff_eq_firstChoice {n : ℕ}
    (π : Ranking n) (c : Candidate n) :
    rankOf π c = 0 ↔ c = firstChoice π := by
  constructor
  · intro h
    have hc : π (rankOf π c) = c := by
      simp [rankOf]
    simpa [firstChoice, h] using hc.symm
  · intro h
    rw [h]
    simp [rankOf, firstChoice]

theorem rankOf_lt_one_eq_zero {n : ℕ}
    {i : Candidate n} (hi : i < (1 : Candidate n)) :
    i = 0 := by
  apply Fin.ext
  change i.val = 0
  have hlt : i.val < 1 := hi
  omega

theorem one_le_of_ne_zero {n : ℕ}
    {i : Candidate n} (hi : i ≠ 0) :
    (1 : Candidate n) ≤ i := by
  change 1 ≤ i.val
  have hval : i.val ≠ 0 := by
    intro h
    exact hi (Fin.ext h)
  omega

@[simp] theorem candidate_val_add_one_of_lt {n : ℕ}
    {i j : Candidate n} (hij : i < j) :
    ((i + 1 : Candidate n) : ℕ) = (i : ℕ) + 1 := by
  have hij_val : (i : ℕ) < (j : ℕ) := hij
  have hj_lt : (j : ℕ) < n + 2 := j.is_lt
  exact Fin.val_add_one_of_lt' (by omega)

theorem inversionFinsetInvolvingSecondNotFirst_eq_map_Ico {n : ℕ}
    (τ : Ranking n) (hfirst : firstChoice τ = 0) :
    inversionFinsetInvolvingSecondNotFirst (Equiv.refl (Candidate n)) τ =
      (Finset.Ico (1 : Candidate n) (secondChoice τ)).map
        ⟨fun i : Candidate n => (i, secondChoice τ),
          by
            intro i j h
            exact (Prod.ext_iff.mp h).1⟩ := by
  classical
  ext ab
  constructor
  · intro hab
    have hinv : ab ∈ inversionFinset (Equiv.refl (Candidate n)) τ :=
      (Finset.mem_filter.mp hab).1
    have hprops :
        (ab.1 = secondChoice τ ∨ ab.2 = secondChoice τ) ∧
          ab.1 ≠ firstChoice τ ∧ ab.2 ≠ firstChoice τ :=
      (Finset.mem_filter.mp hab).2
    have hinv_prop :
        invertedPair (Equiv.refl (Candidate n)) τ ab := by
      simpa [inversionFinset] using hinv
    rcases hprops.1 with hleft | hright
    · exfalso
      have hrank_lt_one : rankOf τ ab.2 < (1 : Candidate n) := by
        simpa [rankOf, hleft] using hinv_prop.2
      have hrank_zero : rankOf τ ab.2 = 0 :=
        rankOf_lt_one_eq_zero hrank_lt_one
      have hab2_first : ab.2 = firstChoice τ :=
        (rankOf_eq_zero_iff_eq_firstChoice τ ab.2).mp hrank_zero
      exact hprops.2.2 hab2_first
    · refine Finset.mem_map.mpr ?_
      refine ⟨ab.1, ?_, ?_⟩
      · exact Finset.mem_Ico.mpr
          ⟨one_le_of_ne_zero (by
              intro hzero
              exact hprops.2.1 (by
                rw [hfirst]
                exact hzero)),
            by simpa [rankOf, hright] using hinv_prop.1⟩
      · ext <;> simp [hright]
  · intro hab
    rcases Finset.mem_map.mp hab with ⟨i, hi, hab_eq⟩
    have hi_bounds := Finset.mem_Ico.mp hi
    have hi_ne_first : i ≠ firstChoice τ := by
      intro h
      have hi0 : i = 0 := by
        rw [h, hfirst]
      have hnot : ¬ (1 : Candidate n) ≤ i := by
        rw [hi0]
        intro hle
        have hleNat : (1 : ℕ) ≤ (0 : ℕ) := hle
        omega
      exact hnot hi_bounds.1
    have hi_ne_second : i ≠ secondChoice τ :=
      ne_of_lt hi_bounds.2
    have hrank : rankOf τ (secondChoice τ) < rankOf τ i := by
      rw [rankOf_secondChoice]
      exact one_lt_rankOf_of_ne_first_second τ hi_ne_first hi_ne_second
    have hinv : invertedPair (Equiv.refl (Candidate n)) τ (i, secondChoice τ) := by
      constructor
      · simpa [rankOf] using hi_bounds.2
      · simpa using hrank
    have hinv' : invertedPair (Equiv.refl (Candidate n)) τ (i, τ 1) := by
      simpa [secondChoice] using hinv
    have hi_ne_first' : i ≠ τ 0 := by
      simpa [firstChoice] using hi_ne_first
    have hsecond_ne_first : τ 1 ≠ τ 0 := by
      simpa [firstChoice, secondChoice] using
        (firstChoice_ne_secondChoice τ).symm
    rw [← hab_eq]
    unfold inversionFinsetInvolvingSecondNotFirst inversionFinset
    simp [hinv', hi_ne_first', hsecond_ne_first]

theorem inversionFinsetInvolvingSecondNotFirst_card {n : ℕ}
    (τ : Ranking n) (hfirst : firstChoice τ = 0) :
    (inversionFinsetInvolvingSecondNotFirst
      (Equiv.refl (Candidate n)) τ).card =
      (secondChoice τ : ℕ) - 1 := by
  rw [inversionFinsetInvolvingSecondNotFirst_eq_map_Ico τ hfirst]
  rw [Finset.card_map]
  simpa using
    (Finset.card_Ico (a := (1 : Candidate n)) (b := secondChoice τ))

theorem inversionFinsetInvolving_secondChoice_eq_involvingSecondNotFirst {n : ℕ}
    (τ : Ranking n) (hfirst : firstChoice τ = 0) :
    inversionFinsetInvolving (Equiv.refl (Candidate n)) τ (secondChoice τ) =
      inversionFinsetInvolvingSecondNotFirst (Equiv.refl (Candidate n)) τ := by
  classical
  ext ab
  constructor
  · intro hab
    have hinv_mem : ab ∈ inversionFinset (Equiv.refl (Candidate n)) τ :=
      (Finset.mem_filter.mp hab).1
    have hinvolves : ab.1 = secondChoice τ ∨ ab.2 = secondChoice τ :=
      (Finset.mem_filter.mp hab).2
    have hinv : invertedPair (Equiv.refl (Candidate n)) τ ab := by
      simpa [inversionFinset] using hinv_mem
    have hnot_first_left : ab.1 ≠ firstChoice τ := by
      intro hleft
      have hnot : ¬ rankOf τ ab.2 < rankOf τ ab.1 := by
        rw [hleft, rankOf_firstChoice]
        exact not_lt_bot
      exact hnot hinv.2
    have hnot_first_right : ab.2 ≠ firstChoice τ := by
      intro hright
      have hnot :
          ¬ rankOf (Equiv.refl (Candidate n)) ab.1 <
            rankOf (Equiv.refl (Candidate n)) ab.2 := by
        rw [hright, hfirst]
        exact not_lt_bot
      exact hnot hinv.1
    exact Finset.mem_filter.mpr
      ⟨hinv_mem, ⟨hinvolves, hnot_first_left, hnot_first_right⟩⟩
  · intro hab
    have hmem : ab ∈ inversionFinset (Equiv.refl (Candidate n)) τ :=
      (Finset.mem_filter.mp hab).1
    have hinvolves :
        ab.1 = secondChoice τ ∨ ab.2 = secondChoice τ :=
      (Finset.mem_filter.mp hab).2.1
    exact Finset.mem_filter.mpr ⟨hmem, hinvolves⟩

theorem inversionFinsetInvolving_secondChoice_card_of_first_zero {n : ℕ}
    (τ : Ranking n) (hfirst : firstChoice τ = 0) :
    (inversionFinsetInvolving (Equiv.refl (Candidate n)) τ
      (secondChoice τ)).card =
      (secondChoice τ : ℕ) - 1 := by
  rw [inversionFinsetInvolving_secondChoice_eq_involvingSecondNotFirst τ hfirst]
  exact inversionFinsetInvolvingSecondNotFirst_card τ hfirst

theorem cycleRange_lt_cycleRange_iff_of_ne {n : ℕ}
    (r a b : Candidate n) (ha : a ≠ r) (hb : b ≠ r) :
    Fin.cycleRange r a < Fin.cycleRange r b ↔ a < b := by
  rcases lt_trichotomy a r with ha_lt | ha_eq | ha_gt
  · rcases lt_trichotomy b r with hb_lt | hb_eq | hb_gt
    · rw [Fin.cycleRange_of_lt ha_lt, Fin.cycleRange_of_lt hb_lt]
      constructor <;> intro h <;> fin_omega
    · exact (hb hb_eq).elim
    · rw [Fin.cycleRange_of_lt ha_lt, Fin.cycleRange_of_gt hb_gt]
      constructor
      · intro _
        exact lt_trans ha_lt hb_gt
      · intro _
        fin_omega
  · exact (ha ha_eq).elim
  · rcases lt_trichotomy b r with hb_lt | hb_eq | hb_gt
    · rw [Fin.cycleRange_of_gt ha_gt, Fin.cycleRange_of_lt hb_lt]
      constructor <;> intro h <;> fin_omega
    · exact (hb hb_eq).elim
    · rw [Fin.cycleRange_of_gt ha_gt, Fin.cycleRange_of_gt hb_gt]

theorem cycleIcc_one_apply_of_ne {n : ℕ}
    {s x : Candidate n} (hx : x ≠ s) :
    Fin.cycleIcc (1 : Candidate n) s x =
      if x < (1 : Candidate n) then x else if x < s then x + 1 else x := by
  by_cases hx_one : x < (1 : Candidate n)
  · rw [Fin.cycleIcc_of_lt hx_one]
    simp [hx_one]
  · by_cases hxs : x < s
    · have hle : (1 : Candidate n) ≤ x := le_of_not_gt hx_one
      rw [Fin.cycleIcc_of_ge_of_lt hle hxs]
      simp [hx_one, hxs]
    · have hsx : s < x := lt_of_le_of_ne (le_of_not_gt hxs) (Ne.symm hx)
      rw [Fin.cycleIcc_of_gt hsx]
      simp [hx_one, hxs]

theorem cycleIcc_one_val_of_ne {n : ℕ}
    {s x : Candidate n} (hx : x ≠ s) :
    ((Fin.cycleIcc (1 : Candidate n) s x) : ℕ) =
      if x < (1 : Candidate n) then (x : ℕ)
      else if x < s then (x : ℕ) + 1
      else (x : ℕ) := by
  by_cases hx_one : x < (1 : Candidate n)
  · rw [Fin.cycleIcc_of_lt hx_one]
    simp [hx_one]
  · by_cases hxs : x < s
    · have hle : (1 : Candidate n) ≤ x := le_of_not_gt hx_one
      rw [Fin.cycleIcc_of_ge_of_lt hle hxs]
      simp [hx_one, hxs, candidate_val_add_one_of_lt hxs]
    · have hsx : s < x := lt_of_le_of_ne (le_of_not_gt hxs) (Ne.symm hx)
      rw [Fin.cycleIcc_of_gt hsx]
      simp [hx_one, hxs]

theorem cycleIcc_one_lt_cycleIcc_one_iff_of_ne {n : ℕ}
    (s a b : Candidate n) (ha : a ≠ s) (hb : b ≠ s) :
    Fin.cycleIcc (1 : Candidate n) s a <
        Fin.cycleIcc (1 : Candidate n) s b ↔
      a < b := by
  by_cases hs0 : s = 0
  · subst s
    simp
  have hs1 : (1 : Candidate n) ≤ s := one_le_of_ne_zero hs0
  change
    ((Fin.cycleIcc (1 : Candidate n) s a) : ℕ) <
        ((Fin.cycleIcc (1 : Candidate n) s b) : ℕ) ↔
      (a : ℕ) < (b : ℕ)
  rw [cycleIcc_one_val_of_ne ha, cycleIcc_one_val_of_ne hb]
  split_ifs
  all_goals
    try
      have hsb : s < b :=
        lt_of_le_of_ne (le_of_not_gt (by assumption : ¬ b < s)) (Ne.symm hb)
    try omega
    try fin_omega

theorem invertedPair_refl_trans_cycleIcc_one_iff_of_ne {n : ℕ}
    (τ : Ranking n) (s a b : Candidate n) (ha : a ≠ s) (hb : b ≠ s) :
    invertedPair (Equiv.refl (Candidate n))
        (τ.trans (Fin.cycleIcc (1 : Candidate n) s))
        (Fin.cycleIcc (1 : Candidate n) s a,
          Fin.cycleIcc (1 : Candidate n) s b) ↔
      invertedPair (Equiv.refl (Candidate n)) τ (a, b) := by
  constructor
  · intro h
    constructor
    · exact (cycleIcc_one_lt_cycleIcc_one_iff_of_ne s a b ha hb).mp h.1
    · simpa [rankOf] using h.2
  · intro h
    constructor
    · exact (cycleIcc_one_lt_cycleIcc_one_iff_of_ne s a b ha hb).mpr h.1
    · simpa [rankOf] using h.2

theorem inversionFinsetNotInvolving_secondChoice_card_eq_cycleIcc_one {n : ℕ}
    (τ : Ranking n) (hfirst : firstChoice τ = 0) :
    (inversionFinsetNotInvolving (Equiv.refl (Candidate n)) τ
        (secondChoice τ)).card =
      (inversionFinset (Equiv.refl (Candidate n))
        (τ.trans (Fin.cycleIcc (1 : Candidate n) (secondChoice τ)))).card := by
  classical
  let s : Candidate n := secondChoice τ
  let E : Ranking n := Fin.cycleIcc (1 : Candidate n) s
  have hs_ne_zero : s ≠ 0 := by
    intro hs0
    have hsame : firstChoice τ = secondChoice τ := by
      rw [hfirst, ← hs0]
    exact (firstChoice_ne_secondChoice τ) hsame
  have hs1 : (1 : Candidate n) ≤ s := one_le_of_ne_zero hs_ne_zero
  have hE_s : E s = 1 := by
    simp [E, Fin.cycleIcc_of_last hs1]
  have h01 : (0 : Candidate n) < 1 := by
    change (0 : ℕ) < 1
    omega
  have hE_zero : E 0 = 0 := by
    simpa [E] using
      (Fin.cycleIcc_of_lt (i := (1 : Candidate n)) (j := s) h01)
  have hfirst_norm : firstChoice (τ.trans E) = 0 := by
    have hτ0 : τ 0 = 0 := by
      simpa [firstChoice] using hfirst
    simp [firstChoice, hτ0, hE_zero]
  have hsecond_norm : secondChoice (τ.trans E) = 1 := by
    have hτ1 : τ 1 = s := by
      simp [s]
    simp [secondChoice, hτ1, hE_s]
  refine Finset.card_bij
    (s := inversionFinsetNotInvolving (Equiv.refl (Candidate n)) τ s)
    (t := inversionFinset (Equiv.refl (Candidate n)) (τ.trans E))
    (i := fun ab _ => (E ab.1, E ab.2)) ?hi ?hinj ?hsurj
  · intro ab hab
    have hinv : invertedPair (Equiv.refl (Candidate n)) τ ab := by
      simpa [inversionFinsetNotInvolving, inversionFinset] using
        (Finset.mem_filter.mp hab).1
    have hnot : ¬(ab.1 = s ∨ ab.2 = s) := by
      simpa [inversionFinsetNotInvolving] using (Finset.mem_filter.mp hab).2
    have ha : ab.1 ≠ s := fun h => hnot (Or.inl h)
    have hb : ab.2 ≠ s := fun h => hnot (Or.inr h)
    have hnorm :
        invertedPair (Equiv.refl (Candidate n)) (τ.trans E)
          (E ab.1, E ab.2) := by
      simpa [E, s] using
        (invertedPair_refl_trans_cycleIcc_one_iff_of_ne τ s ab.1 ab.2
          ha hb).2 hinv
    simpa [inversionFinset] using hnorm
  · intro ab _ cd _ h
    exact Prod.ext
      (E.injective (Prod.ext_iff.mp h).1)
      (E.injective (Prod.ext_iff.mp h).2)
  · intro ab hab
    have hinvNorm :
        invertedPair (Equiv.refl (Candidate n)) (τ.trans E) ab := by
      simpa [inversionFinset] using hab
    have hrank_one : rankOf (τ.trans E) (1 : Candidate n) = 1 := by
      conv_lhs =>
        rw [← hsecond_norm]
      exact rankOf_secondChoice (τ.trans E)
    have hab1_ne_one : ab.1 ≠ (1 : Candidate n) := by
      intro h1
      have hrank_y2_lt : rankOf (τ.trans E) ab.2 < (1 : Candidate n) := by
        simpa [h1, hrank_one] using hinvNorm.2
      have hrank_y2_zero : rankOf (τ.trans E) ab.2 = 0 :=
        rankOf_lt_one_eq_zero hrank_y2_lt
      have hy2_zero : ab.2 = 0 := by
        have hy2_first :=
          (rankOf_eq_zero_iff_eq_firstChoice (τ.trans E) ab.2).mp
            hrank_y2_zero
        rw [hfirst_norm] at hy2_first
        exact hy2_first
      have hbad : (1 : Candidate n) < 0 := by
        simpa [rankOf, h1, hy2_zero] using hinvNorm.1
      have hbadNat : (1 : ℕ) < 0 := hbad
      omega
    have hab2_ne_one : ab.2 ≠ (1 : Candidate n) := by
      intro h2
      have hy1_lt_one : ab.1 < (1 : Candidate n) := by
        simpa [rankOf, h2] using hinvNorm.1
      have hy1_zero : ab.1 = 0 := rankOf_lt_one_eq_zero hy1_lt_one
      have hrank_y1_zero : rankOf (τ.trans E) ab.1 = 0 := by
        rw [hy1_zero]
        conv_lhs =>
          rw [← hfirst_norm]
        exact rankOf_firstChoice (τ.trans E)
      have hbad : (1 : Candidate n) < 0 := by
        have hlt := hinvNorm.2
        rw [h2, hrank_one, hrank_y1_zero] at hlt
        exact hlt
      have hbadNat : (1 : ℕ) < 0 := hbad
      omega
    let pre : Candidate n × Candidate n := (E.symm ab.1, E.symm ab.2)
    have hpre1 : pre.1 ≠ s := by
      intro h
      apply hab1_ne_one
      have hE : E pre.1 = E s := by rw [h]
      simpa [pre, hE_s] using hE
    have hpre2 : pre.2 ≠ s := by
      intro h
      apply hab2_ne_one
      have hE : E pre.2 = E s := by rw [h]
      simpa [pre, hE_s] using hE
    have hinvPre :
        invertedPair (Equiv.refl (Candidate n)) τ pre := by
      have hnorm :
          invertedPair (Equiv.refl (Candidate n)) (τ.trans E)
            (E pre.1, E pre.2) := by
        simpa [pre] using hinvNorm
      simpa [E, s, pre] using
        (invertedPair_refl_trans_cycleIcc_one_iff_of_ne τ s pre.1 pre.2
          hpre1 hpre2).1 hnorm
    refine ⟨pre, ?_, ?_⟩
    · simp [inversionFinsetNotInvolving, inversionFinset, hinvPre, hpre1, hpre2]
    · simp [pre]

theorem kendallTau_eq_secondChoice_sub_one_add_cycleIcc_one {n : ℕ}
    (τ : Ranking n) (hfirst : firstChoice τ = 0) :
    kendallTau (Equiv.refl (Candidate n)) τ =
      ((secondChoice τ : ℕ) - 1) +
        kendallTau (Equiv.refl (Candidate n))
          (τ.trans (Fin.cycleIcc (1 : Candidate n) (secondChoice τ))) := by
  rw [kendallTau]
  rw [← inversionFinsetInvolving_card_add_notInvolving_card
    (ρ := Equiv.refl (Candidate n)) (π := τ) (c := secondChoice τ)]
  rw [inversionFinsetInvolving_secondChoice_card_of_first_zero τ hfirst]
  rw [inversionFinsetNotInvolving_secondChoice_card_eq_cycleIcc_one τ hfirst]
  rfl

@[simp] theorem firstChoice_trans {n : ℕ}
    (π e : Ranking n) :
    firstChoice (π.trans e) = e (firstChoice π) := by
  simp [firstChoice]

@[simp] theorem secondChoice_trans {n : ℕ}
    (π e : Ranking n) :
    secondChoice (π.trans e) = e (secondChoice π) := by
  simp [secondChoice]

@[simp] theorem rankOf_trans_apply {n : ℕ}
    (π e : Ranking n) (c : Candidate n) :
    rankOf (π.trans e) (e c) = rankOf π c := by
  simp [rankOf]

/-- Right-composition by a fixed relabeling is a bijection on rankings. -/
def rankingRightTransEquiv {n : ℕ} (e : Ranking n) :
    Ranking n ≃ Ranking n where
  toFun π := π.trans e
  invFun π := π.trans e.symm
  left_inv π := by
    ext x
    simp
  right_inv π := by
    ext x
    simp

theorem invertedPair_refl_trans_cycleRange_iff_of_ne {n : ℕ}
    (τ : Ranking n) (r a b : Candidate n) (ha : a ≠ r) (hb : b ≠ r) :
    invertedPair (Equiv.refl (Candidate n)) (τ.trans (Fin.cycleRange r))
        (Fin.cycleRange r a, Fin.cycleRange r b) ↔
      invertedPair (Equiv.refl (Candidate n)) τ (a, b) := by
  constructor
  · intro h
    constructor
    · exact (cycleRange_lt_cycleRange_iff_of_ne r a b ha hb).mp h.1
    · simpa [rankOf] using h.2
  · intro h
    constructor
    · exact (cycleRange_lt_cycleRange_iff_of_ne r a b ha hb).mpr h.1
    · simpa [rankOf] using h.2

@[simp] theorem firstChoice_trans_cycleRange_firstChoice {n : ℕ}
    (τ : Ranking n) :
    firstChoice (τ.trans (Fin.cycleRange (firstChoice τ))) = 0 := by
  simp [Fin.cycleRange_self]

theorem inversionFinsetNotInvolving_firstChoice_card_eq_cycleRange {n : ℕ}
    (τ : Ranking n) :
    (inversionFinsetNotInvolving (Equiv.refl (Candidate n)) τ
        (firstChoice τ)).card =
      (inversionFinset (Equiv.refl (Candidate n))
        (τ.trans (Fin.cycleRange (firstChoice τ)))).card := by
  classical
  let r : Candidate n := firstChoice τ
  let E : Ranking n := Fin.cycleRange r
  refine Finset.card_bij
    (s := inversionFinsetNotInvolving (Equiv.refl (Candidate n)) τ r)
    (t := inversionFinset (Equiv.refl (Candidate n)) (τ.trans E))
    (i := fun ab _ => (E ab.1, E ab.2)) ?hi ?hinj ?hsurj
  · intro ab hab
    have hinv : invertedPair (Equiv.refl (Candidate n)) τ ab := by
      simpa [inversionFinsetNotInvolving, inversionFinset] using
        (Finset.mem_filter.mp hab).1
    have hnot : ¬(ab.1 = r ∨ ab.2 = r) := by
      simpa [inversionFinsetNotInvolving] using (Finset.mem_filter.mp hab).2
    have ha : ab.1 ≠ r := fun h => hnot (Or.inl h)
    have hb : ab.2 ≠ r := fun h => hnot (Or.inr h)
    have hnorm :
        invertedPair (Equiv.refl (Candidate n)) (τ.trans E)
          (E ab.1, E ab.2) := by
      simpa [E, r] using
        (invertedPair_refl_trans_cycleRange_iff_of_ne τ r ab.1 ab.2 ha hb).2 hinv
    simpa [inversionFinset] using hnorm
  · intro ab _ cd _ h
    exact Prod.ext
      (E.injective (Prod.ext_iff.mp h).1)
      (E.injective (Prod.ext_iff.mp h).2)
  · intro ab hab
    have hinvNorm :
        invertedPair (Equiv.refl (Candidate n)) (τ.trans E) ab := by
      simpa [inversionFinset] using hab
    have hab1_ne_zero : ab.1 ≠ 0 := by
      intro hzero
      have hfirst : firstChoice (τ.trans E) = 0 := by
        simp [E, r]
      have hrank : rankOf (τ.trans E) ab.1 = 0 := by
        rw [hzero]
        conv_lhs =>
          rw [← hfirst]
        exact rankOf_firstChoice (τ.trans E)
      have hnot : ¬ rankOf (τ.trans E) ab.2 < rankOf (τ.trans E) ab.1 := by
        rw [hrank]
        exact not_lt_bot
      exact hnot hinvNorm.2
    have hab2_ne_zero : ab.2 ≠ 0 := by
      intro hzero
      have hrank : rankOf (Equiv.refl (Candidate n)) ab.2 = 0 := by
        simp [rankOf, hzero]
      have hnot :
          ¬ rankOf (Equiv.refl (Candidate n)) ab.1 <
            rankOf (Equiv.refl (Candidate n)) ab.2 := by
        rw [hrank]
        exact not_lt_bot
      exact hnot hinvNorm.1
    let pre : Candidate n × Candidate n := (E.symm ab.1, E.symm ab.2)
    have hpre1 : pre.1 ≠ r := by
      intro h
      apply hab1_ne_zero
      have hE : E pre.1 = E r := by rw [h]
      simpa [pre, E, r, Fin.cycleRange_self] using hE
    have hpre2 : pre.2 ≠ r := by
      intro h
      apply hab2_ne_zero
      have hE : E pre.2 = E r := by rw [h]
      simpa [pre, E, r, Fin.cycleRange_self] using hE
    have hinvPre :
        invertedPair (Equiv.refl (Candidate n)) τ pre := by
      have hnorm :
          invertedPair (Equiv.refl (Candidate n)) (τ.trans E)
            (E pre.1, E pre.2) := by
        simpa [pre]
          using hinvNorm
      simpa [E, r, pre] using
        (invertedPair_refl_trans_cycleRange_iff_of_ne τ r pre.1 pre.2
          hpre1 hpre2).1 hnorm
    refine ⟨pre, ?_, ?_⟩
    · simp [inversionFinsetNotInvolving, inversionFinset, hinvPre, hpre1, hpre2]
    · simp [pre]

theorem kendallTau_eq_firstChoice_add_cycleRange {n : ℕ}
    (τ : Ranking n) :
    kendallTau (Equiv.refl (Candidate n)) τ =
      (firstChoice τ : ℕ) +
        kendallTau (Equiv.refl (Candidate n))
          (τ.trans (Fin.cycleRange (firstChoice τ))) := by
  rw [kendallTau_eq_firstChoice_rank_add_notInvolving_card
    (ρ := Equiv.refl (Candidate n)) (π := τ)]
  rw [inversionFinsetNotInvolving_firstChoice_card_eq_cycleRange]
  simp [rankOf, kendallTau]

theorem kendallTau_center_trans {n : ℕ}
    (ρ τ : Ranking n) :
    kendallTau ρ (τ.trans ρ) =
      kendallTau (Equiv.refl (Candidate n)) τ := by
  classical
  unfold kendallTau
  refine (Finset.card_bij
    (s := inversionFinset (Equiv.refl (Candidate n)) τ)
    (t := inversionFinset ρ (τ.trans ρ))
    (i := fun ab _ => (ρ ab.1, ρ ab.2)) ?hi ?hinj ?hsurj).symm
  · intro ab hab
    have hinv :
        invertedPair (Equiv.refl (Candidate n)) τ ab := by
      simpa [inversionFinset] using hab
    have hinv' : invertedPair ρ (τ.trans ρ) (ρ ab.1, ρ ab.2) := by
      simpa [invertedPair, rankOf] using hinv
    simpa [inversionFinset] using hinv'
  · intro ab _ cd _ h
    exact Prod.ext
      (ρ.injective (Prod.ext_iff.mp h).1)
      (ρ.injective (Prod.ext_iff.mp h).2)
  · intro ab hab
    have hinv :
        invertedPair ρ (τ.trans ρ) ab := by
      simpa [inversionFinset] using hab
    let pre : Candidate n × Candidate n := (ρ.symm ab.1, ρ.symm ab.2)
    have hinvPre :
        invertedPair (Equiv.refl (Candidate n)) τ pre := by
      simpa [pre, invertedPair, rankOf] using hinv
    refine ⟨pre, ?_, ?_⟩
    · simpa [inversionFinset] using hinvPre
    · simp [pre]

/--
A ranking with no inversions relative to a reference ranking is the reference
ranking.
-/
theorem eq_of_forall_not_invertedPair {n : ℕ} (ρ π : Ranking n)
    (h : ∀ ab : Candidate n × Candidate n, ¬ invertedPair ρ π ab) :
    π = ρ := by
  have hmono : Monotone (ρ.trans π.symm) := by
    intro i j hij
    by_contra hnot
    have hij_ne : i ≠ j := by
      intro heq
      subst j
      exact hnot le_rfl
    have hij_lt : i < j := lt_of_le_of_ne hij hij_ne
    have hlt : (ρ.trans π.symm) j < (ρ.trans π.symm) i :=
      lt_of_not_ge hnot
    have hinv : invertedPair ρ π (ρ i, ρ j) := by
      constructor
      · simpa [rankOf] using hij_lt
      · simpa [rankOf, Equiv.trans_apply] using hlt
    exact h (ρ i, ρ j) hinv
  have hperm : ρ.trans π.symm = 1 :=
    (Equiv.Perm.monotone_iff (ρ.trans π.symm)).mp hmono
  apply Equiv.ext
  intro i
  have hi : (ρ.trans π.symm) i = i := by
    rw [hperm]
    rfl
  have happly : ρ i = π i := by
    simpa [Equiv.trans_apply] using congrArg π hi
  exact happly.symm

/-- Any ranking different from the reference has at least one inversion. -/
theorem exists_invertedPair_of_ne {n : ℕ} {ρ π : Ranking n}
    (hneq : π ≠ ρ) :
    ∃ ab : Candidate n × Candidate n, invertedPair ρ π ab := by
  by_contra hno
  apply hneq
  exact eq_of_forall_not_invertedPair ρ π (by
    intro ab hinv
    exact hno ⟨ab, hinv⟩)

/--
A ranking with no adjacent inversions relative to a reference ranking is the
reference ranking.

The adjacent pairs are indexed in the reference order: for `i : Fin (n + 1)`,
the pair `(ρ i.castSucc, ρ i.succ)` is the pair of candidates occupying
neighboring positions `i` and `i + 1` under `ρ`.
-/
theorem eq_of_forall_not_adjacent_invertedPair {n : ℕ} (ρ π : Ranking n)
    (h : ∀ i : Fin (n + 1),
      ¬ invertedPair ρ π (ρ i.castSucc, ρ i.succ)) :
    π = ρ := by
  have hmono : Monotone (ρ.trans π.symm) := by
    refine monotone_of_le_succ ?_
    intro a ha
    obtain ⟨i, rfl⟩ :=
      Fin.eq_castSucc_of_ne_last (by simpa using ha)
    have hcenter_lt : rankOf ρ (ρ i.castSucc) < rankOf ρ (ρ i.succ) := by
      simpa [rankOf] using i.castSucc_lt_succ
    have hnot_rev :
        ¬ rankOf π (ρ i.succ) < rankOf π (ρ i.castSucc) := by
      intro hrev
      exact h i ⟨hcenter_lt, hrev⟩
    have hle_rank :
        rankOf π (ρ i.castSucc) ≤ rankOf π (ρ i.succ) :=
      le_of_not_gt hnot_rev
    simpa [rankOf, Equiv.trans_apply] using hle_rank
  have hperm : ρ.trans π.symm = 1 :=
    (Equiv.Perm.monotone_iff (ρ.trans π.symm)).mp hmono
  apply Equiv.ext
  intro i
  have hi : (ρ.trans π.symm) i = i := by
    rw [hperm]
    rfl
  have happly : ρ i = π i := by
    simpa [Equiv.trans_apply] using congrArg π hi
  exact happly.symm

/--
Any ranking different from the reference has at least one adjacent inversion in
the reference order.
-/
theorem exists_adjacent_invertedPair_of_ne {n : ℕ} {ρ π : Ranking n}
    (hneq : π ≠ ρ) :
    ∃ i : Fin (n + 1), invertedPair ρ π (ρ i.castSucc, ρ i.succ) := by
  by_contra hno
  apply hneq
  exact eq_of_forall_not_adjacent_invertedPair ρ π (by
    intro i hinv
    exact hno ⟨i, hinv⟩)

/-- The candidates occupying positions `i` and `j` in a ranking are distinct. -/
theorem apply_ne_apply_of_ne {n : ℕ} (π : Ranking n) {i j : Candidate n}
    (hij : i ≠ j) : π i ≠ π j := by
  intro h
  exact hij (π.injective h)

/-- The reference first candidate is ranked above the reference second candidate. -/
theorem rankOf_center_first_lt_second {n : ℕ} (ρ : Ranking n) :
    rankOf ρ (firstChoice ρ) < rankOf ρ (secondChoice ρ) := by
  simp [rankOf, firstChoice, secondChoice]

/-- A value vector is strictly decreasing down the reference ranking. -/
def StrictlyOrderedBy {n : ℕ} (ρ : Ranking n) (value : Candidate n → ℝ) : Prop :=
  ∀ {a b : Candidate n}, rankOf ρ a < rankOf ρ b → value b < value a

/-- A value vector is weakly decreasing down the reference ranking. -/
def WeaklyOrderedBy {n : ℕ} (ρ : Ranking n) (value : Candidate n → ℝ) : Prop :=
  ∀ {a b : Candidate n}, rankOf ρ a < rankOf ρ b → value b ≤ value a

/-- A strict reference ordering implies the corresponding weak reference ordering. -/
theorem weaklyOrderedBy_of_strictlyOrderedBy {n : ℕ}
    {ρ : Ranking n} {value : Candidate n → ℝ}
    (h : StrictlyOrderedBy ρ value) :
    WeaklyOrderedBy ρ value := by
  intro a b hab
  exact le_of_lt (h hab)

/--
Any candidate different from the reference top candidate is ranked strictly
below it in the reference ranking.
-/
theorem rankOf_firstChoice_lt_rankOf_of_ne {n : ℕ}
    (ρ : Ranking n) {c : Candidate n} (hc : c ≠ firstChoice ρ) :
    rankOf ρ (firstChoice ρ) < rankOf ρ c := by
  simpa [rankOf, firstChoice] using zero_lt_rankOf_of_ne_firstChoice ρ hc

/-- The value gap between the first and second candidates of a ranking. -/
def topTwoValueGap {n : ℕ} (value : Candidate n → ℝ) (π : Ranking n) : ℝ :=
  value (firstChoice π) - value (secondChoice π)

/-- Strict reference-ordering gives a positive top-two value gap at the reference ranking. -/
theorem center_topTwoValueGap_pos_of_strictlyOrderedBy {n : ℕ}
    {ρ : Ranking n} {value : Candidate n → ℝ}
    (hvalue : StrictlyOrderedBy ρ value) :
    0 < topTwoValueGap value ρ := by
  unfold topTwoValueGap
  exact sub_pos.mpr (hvalue (rankOf_center_first_lt_second ρ))

/-- Weak reference-ordering gives a nonnegative top-two value gap at the reference ranking. -/
theorem center_topTwoValueGap_nonneg_of_weaklyOrderedBy {n : ℕ}
    {ρ : Ranking n} {value : Candidate n → ℝ}
    (hvalue : WeaklyOrderedBy ρ value) :
    0 ≤ topTwoValueGap value ρ := by
  unfold topTwoValueGap
  exact sub_nonneg.mpr (hvalue (rankOf_center_first_lt_second ρ))

end Ranking
end SocialChoice
end AppliedModelingLib
