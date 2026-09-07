import AppliedModelingLib.Foundations.Probability.IidFirstHitRestart

/-!
# Capped first hits in an IID stream

This module makes the finite-horizon version of a measurable IID first-hit
time into a total prefix stopping index.  At the deterministic cap, the index
is used both when a first hit occurs at that coordinate and when no earlier
hit occurred.  Thus the construction is genuinely total and bounded; an
all-time geometric stopping result must separately take the cap to infinity.
-/

namespace AppliedModelingLib.Probability.IIDStream

open MeasureTheory ProbabilityTheory

noncomputable section

variable {α : Type*} [MeasurableSpace α]

/-- The first hit strictly before `cap`, with `cap` as the total fallback.
The fallback deliberately does not distinguish a hit at `cap` from no earlier
hit, because both alternatives inspect the coordinate at the cap. -/
noncomputable def firstHitCapped (hit : Set α) (cap : ℕ) :
    (ℕ → α) → ℕ := fun omega => by
  classical
  exact if h : ∃ n, n < cap ∧ omega n ∈ hit then Nat.find h else cap

/-- A capped first-hit index never exceeds its deterministic cap. -/
theorem firstHitCapped_le (hit : Set α) (cap : ℕ) (omega : ℕ → α) :
    firstHitCapped hit cap omega ≤ cap := by
  classical
  unfold firstHitCapped
  split_ifs with h
  · exact (Nat.find_spec h).1.le
  · exact le_rfl

/-- Strictly before the cap, the capped index has the ordinary first-hit
characterization. -/
theorem firstHitCapped_eq_iff_of_lt
    (hit : Set α) {cap n : ℕ} (hn : n < cap) (omega : ℕ → α) :
    firstHitCapped hit cap omega = n ↔
      omega n ∈ hit ∧ ∀ m < n, omega m ∉ hit := by
  classical
  constructor
  · intro heq
    unfold firstHitCapped at heq
    by_cases hex : ∃ m, m < cap ∧ omega m ∈ hit
    · have hspec : Nat.find hex < cap ∧ omega (Nat.find hex) ∈ hit :=
        Nat.find_spec hex
      rw [dif_pos hex] at heq
      refine ⟨?_, ?_⟩
      · subst n
        exact hspec.2
      · intro m hm hmem
        have hlt : m < Nat.find hex := by simpa [heq] using hm
        exact (Nat.find_min hex hlt) ⟨lt_trans hm hn, hmem⟩
    · rw [dif_neg hex] at heq
      exact False.elim ((ne_of_lt hn) heq.symm)
  · rintro ⟨hhit, hprevious⟩
    let hex : ∃ m, m < cap ∧ omega m ∈ hit := ⟨n, hn, hhit⟩
    rw [firstHitCapped, dif_pos hex]
    apply Nat.le_antisymm
    · exact Nat.find_min' hex (m := n) ⟨hn, hhit⟩
    · apply le_of_not_gt
      intro hlt
      exact hprevious (Nat.find hex) hlt (Nat.find_spec hex).2

/-- At the cap, the capped first-hit index says precisely that no earlier
coordinate hit. -/
theorem firstHitCapped_eq_cap_iff
    (hit : Set α) (cap : ℕ) (omega : ℕ → α) :
    firstHitCapped hit cap omega = cap ↔ ∀ m < cap, omega m ∉ hit := by
  classical
  constructor
  · intro heq
    unfold firstHitCapped at heq
    by_cases hex : ∃ m, m < cap ∧ omega m ∈ hit
    · have hlt : Nat.find hex < cap := (Nat.find_spec hex).1
      rw [dif_pos hex] at heq
      exact False.elim ((ne_of_lt hlt) heq)
    · rw [dif_neg hex] at heq
      intro m hm hmem
      exact hex ⟨m, hm, hmem⟩
  · intro hprevious
    have hnone : ¬ ∃ m, m < cap ∧ omega m ∈ hit := by
      rintro ⟨m, hm, hmem⟩
      exact hprevious m hm hmem
    simp [firstHitCapped, hnone]

/-- A measurable capped first-hit time is a total prefix stopping index. -/
noncomputable def firstHitCappedStoppingIndex
    (hit : Set α) (hhit : MeasurableSet hit) (cap : ℕ) :
    PrefixStoppingIndex (α := α) where
  toFun := firstHitCapped hit cap
  event_prefix_measurable := by
    intro n
    by_cases hlt : n < cap
    · rw [show {omega | firstHitCapped hit cap omega = n} = firstHitEvent hit n by
        ext omega
        exact firstHitCapped_eq_iff_of_lt hit hlt omega]
      exact firstHitEvent_prefix_measurable hit hhit n
    · by_cases heq : n = cap
      · subst n
        let embed : Fin cap → Finset.range (cap + 1) := fun m =>
          ⟨m, Finset.mem_range.mpr
            (Nat.lt_succ_of_le (Nat.le_of_lt m.isLt))⟩
        let noEarlierHit : Set (Finset.range (cap + 1) → α) := {x |
          ∀ m : Fin cap, x (embed m) ∉ hit}
        have hnoEarlierHit : MeasurableSet noEarlierHit := by
          rw [show noEarlierHit = ⋂ m : Fin cap,
              (fun x => x (embed m)) ⁻¹' hitᶜ by
              ext x
              simp [noEarlierHit]]
          apply MeasurableSet.iInter
          intro m
          exact (measurable_pi_apply (embed m)) hhit.compl
        refine MeasurableSpace.measurableSet_comap.2 ⟨noEarlierHit, hnoEarlierHit, ?_⟩
        ext omega
        simp only [Set.mem_preimage, Set.mem_setOf_eq]
        constructor
        · intro h
          exact (firstHitCapped_eq_cap_iff hit cap omega).mpr (by
            intro m hm
            exact h ⟨m, hm⟩)
        · intro h
          have hno := (firstHitCapped_eq_cap_iff hit cap omega).mp h
          intro m
          exact hno m m.isLt
      · refine MeasurableSpace.measurableSet_comap.2 ⟨∅, MeasurableSet.empty, ?_⟩
        ext omega
        have hle := firstHitCapped_le hit cap omega
        have hgt : cap < n := lt_of_le_of_ne (Nat.le_of_not_gt hlt) (Ne.symm heq)
        simp only [Set.mem_preimage, Set.mem_empty_iff_false]
        constructor
        · exact False.elim
        · intro hindex
          have hnle : n ≤ cap := by
            rw [hindex] at hle
            exact hle
          exact False.elim ((Nat.not_le_of_gt hgt) hnle)

/-- Before `n`, a capped first-hit index continues exactly when no coordinate
before `n` hit; after the cap it cannot continue. -/
theorem mem_continuationEvent_firstHitCappedStoppingIndex_iff
    (hit : Set α) (hhit : MeasurableSet hit) (cap n : ℕ) (omega : ℕ → α) :
    omega ∈ (firstHitCappedStoppingIndex hit hhit cap).continuationEvent n ↔
      n ≤ cap ∧ ∀ m < n, omega m ∉ hit := by
  classical
  constructor
  · intro hstop
    change n ≤ firstHitCapped hit cap omega at hstop
    refine ⟨le_trans hstop (firstHitCapped_le hit cap omega), ?_⟩
    by_contra hno
    push Not at hno
    rcases hno with ⟨m, hmn, hmhit⟩
    let hex : ∃ k, k < n ∧ omega k ∈ hit := ⟨m, hmn, hmhit⟩
    have hk : Nat.find hex < n ∧ omega (Nat.find hex) ∈ hit := Nat.find_spec hex
    have hkcap : Nat.find hex < cap := lt_of_lt_of_le hk.1 (le_trans hstop
      (firstHitCapped_le hit cap omega))
    have hfirst : firstHitCapped hit cap omega = Nat.find hex :=
      (firstHitCapped_eq_iff_of_lt hit hkcap omega).mpr
        ⟨hk.2, fun r hr hrhit => by
          exact (Nat.find_min hex hr) ⟨lt_trans hr hk.1, hrhit⟩⟩
    have hnk : n ≤ Nat.find hex := by simpa [hfirst] using hstop
    exact (Nat.not_le_of_gt hk.1) hnk
  · rintro ⟨hncap, hno⟩
    change n ≤ firstHitCapped hit cap omega
    by_contra hnot
    have hlt : firstHitCapped hit cap omega < n := Nat.lt_of_not_ge hnot
    have hfirstlt : firstHitCapped hit cap omega < cap :=
      lt_of_lt_of_le hlt hncap
    have hchar := (firstHitCapped_eq_iff_of_lt hit hfirstlt omega).mp rfl
    exact hno (firstHitCapped hit cap omega) hlt hchar.1

/-- The continuation probability of a capped IID first hit is the geometric
no-hit probability through the inspected prefix. -/
theorem measure_continuationEvent_firstHitCappedStoppingIndex
    (mu : Measure α) [IsProbabilityMeasure mu]
    (hit : Set α) (hhit : MeasurableSet hit) (cap n : ℕ) :
    measure mu ((firstHitCappedStoppingIndex hit hhit cap).continuationEvent n) =
      if n ≤ cap then (mu hitᶜ) ^ n else 0 := by
  by_cases hncap : n ≤ cap
  · rw [if_pos hncap]
    have hevent :
        (firstHitCappedStoppingIndex hit hhit cap).continuationEvent n =
          {omega | ∀ m : Fin n, omega m ∈ hitᶜ} := by
      ext omega
      rw [mem_continuationEvent_firstHitCappedStoppingIndex_iff]
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff]
      constructor
      · rintro ⟨_, hno⟩ m
        exact hno m m.isLt
      · intro hno
        exact ⟨hncap, fun m hm => hno ⟨m, hm⟩⟩
    rw [hevent]
    have hblock : {omega : ℕ → α | ∀ m : Fin n, omega m ∈ hitᶜ} =
        {omega | ∀ m : Fin n, block (α := α) 0 n omega m ∈ hitᶜ} := by
      ext omega
      simp [block, coordinate]
    rw [hblock, measure_block_mem_eq mu 0 n (fun _ => hitᶜ)
      (fun _ => hhit.compl)]
    simp
  · rw [if_neg hncap]
    have hevent :
        (firstHitCappedStoppingIndex hit hhit cap).continuationEvent n = ∅ := by
      ext omega
      rw [mem_continuationEvent_firstHitCappedStoppingIndex_iff]
      simp only [Set.mem_empty_iff_false, iff_false]
      intro h
      exact hncap h.1
    rw [hevent]
    exact measure_empty

/-- The real no-hit probability is strictly below one when the IID hit event
has positive probability. -/
theorem measureReal_compl_lt_one_of_pos
    (mu : Measure α) [IsProbabilityMeasure mu]
    (hit : Set α) (hhit : MeasurableSet hit) (hpos : 0 < mu hit) :
    (mu hitᶜ).toReal < 1 := by
  rw [← ENNReal.toReal_one]
  apply (ENNReal.toReal_lt_toReal (measure_ne_top mu hitᶜ) ENNReal.one_ne_top).mpr
  have hcompl : mu hitᶜ = 1 - mu hit := by
    rw [measure_compl hhit (measure_ne_top mu hit), measure_univ]
  rw [hcompl]
  exact ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hpos.ne'

end

end AppliedModelingLib.Probability.IIDStream
