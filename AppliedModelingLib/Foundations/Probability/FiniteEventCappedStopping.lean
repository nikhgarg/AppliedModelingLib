import AppliedModelingLib.Foundations.Probability.FiniteEventIIDBridge

/-!
# Bounded regeneration indices for IID finite-event trajectories

This module turns the first occurrence of a state predicate in a finite-event
IID trajectory into a total, bounded prefix stopping index.  The deterministic
cap makes the index total without pretending that an unbounded hitting time is
finite on every path.  It is therefore suitable for finite regeneration and
restart calculations; passing to an all-time renewal statement requires a
separate tail argument.
-/

namespace AppliedModelingLib.Probability.IIDStream

open MeasureTheory ProbabilityTheory

noncomputable section

variable {State Event : Type*}

/-- The first time before `cap` at which an IID finite-event trajectory meets
`hit`, with `cap` as a total fallback when no such hit occurs. -/
noncomputable def finiteEventFirstHitCapped
    (initial : State) (step : State → Event → State) (hit : State → Prop)
    (cap : ℕ) : (ℕ → Event) → ℕ := fun omega => by
  classical
  exact if h : ∃ n, n < cap ∧ hit (finiteEventTrajectory initial step n
      (block 0 n omega)) then Nat.find h else cap

/-- The capped first-hit index never exceeds its prescribed horizon. -/
theorem finiteEventFirstHitCapped_le
    (initial : State) (step : State → Event → State) (hit : State → Prop)
    (cap : ℕ) (omega : ℕ → Event) :
    finiteEventFirstHitCapped initial step hit cap omega ≤ cap := by
  classical
  unfold finiteEventFirstHitCapped
  split_ifs with h
  · exact (Nat.find_spec h).1.le
  · exact le_rfl

/-- Before the cap, the capped first-hit index is exactly characterized by a
hit at its reported time and no earlier hit. -/
theorem finiteEventFirstHitCapped_eq_iff_of_lt
    (initial : State) (step : State → Event → State) (hit : State → Prop)
    {cap n : ℕ} (hn : n < cap) (omega : ℕ → Event) :
    finiteEventFirstHitCapped initial step hit cap omega = n ↔
      hit (finiteEventTrajectory initial step n (block 0 n omega)) ∧
        ∀ m < n, ¬ hit (finiteEventTrajectory initial step m (block 0 m omega)) := by
  classical
  constructor
  · intro heq
    unfold finiteEventFirstHitCapped at heq
    by_cases hex : ∃ m, m < cap ∧ hit (finiteEventTrajectory initial step m
        (block 0 m omega))
    · have hspec : Nat.find hex < cap ∧ hit
        (finiteEventTrajectory initial step (Nat.find hex) (block 0 (Nat.find hex) omega)) :=
        Nat.find_spec hex
      rw [dif_pos hex] at heq
      refine ⟨?_, ?_⟩
      · subst n
        exact hspec.2
      · intro m hm hhit
        have hlt : m < Nat.find hex := by simpa [heq] using hm
        exact (Nat.find_min hex hlt) ⟨lt_trans hm hn, hhit⟩
    · rw [dif_neg hex] at heq
      exact False.elim ((ne_of_lt hn) heq.symm)
  · rintro ⟨hhit, hprevious⟩
    let hex : ∃ m, m < cap ∧ hit (finiteEventTrajectory initial step m
        (block 0 m omega)) := ⟨n, hn, hhit⟩
    rw [finiteEventFirstHitCapped, dif_pos hex]
    apply Nat.le_antisymm
    · exact Nat.find_min' hex (m := n) ⟨hn, hhit⟩
    · apply le_of_not_gt
      intro hlt
      exact hprevious (Nat.find hex) hlt (Nat.find_spec hex).2

/-- The fallback value of the capped first-hit index says that no hit occurred
strictly before its prescribed horizon. -/
theorem finiteEventFirstHitCapped_eq_cap_iff
    (initial : State) (step : State → Event → State) (hit : State → Prop)
    (cap : ℕ) (omega : ℕ → Event) :
    finiteEventFirstHitCapped initial step hit cap omega = cap ↔
      ∀ m < cap, ¬ hit (finiteEventTrajectory initial step m (block 0 m omega)) := by
  classical
  constructor
  · intro heq
    unfold finiteEventFirstHitCapped at heq
    by_cases hex : ∃ m, m < cap ∧ hit (finiteEventTrajectory initial step m
        (block 0 m omega))
    · have hlt : Nat.find hex < cap := (Nat.find_spec hex).1
      rw [dif_pos hex] at heq
      exact False.elim ((ne_of_lt hlt) heq)
    · rw [dif_neg hex] at heq
      intro m hm hhit
      exact hex ⟨m, hm, hhit⟩
  · intro hprevious
    have hnone : ¬ ∃ m, m < cap ∧ hit (finiteEventTrajectory initial step m
        (block 0 m omega)) := by
      rintro ⟨m, hm, hhit⟩
      exact hprevious m hm hhit
    simp [finiteEventFirstHitCapped, hnone]

variable [MeasurableSpace Event]

private theorem finiteEventTrajectory_prefix_eq
    (initial : State) (step : State → Event → State)
    {m n : ℕ} (hmn : m ≤ n) (omega : ℕ → Event) :
    finiteEventTrajectory initial step m (block 0 m omega) =
      finiteEventTrajectory initial step m (fun i =>
        streamPrefix (α := Event) n omega
          ⟨i, Finset.mem_range.mpr
            (Nat.lt_succ_of_le (Nat.le_of_lt (lt_of_lt_of_le i.isLt hmn)))⟩) := by
  congr 2
  funext i
  simp [block, coordinate, streamPrefix]

variable [Fintype Event] [DecidableEq Event] [MeasurableSingletonClass Event]

/-- The bounded first-hit time of an IID finite-event trajectory is a total
prefix stopping index.  It is intentionally bounded: no almost-sure hitting
claim is encoded in this definition. -/
noncomputable def finiteEventFirstHitCappedStoppingIndex
    (initial : State) (step : State → Event → State) (hit : State → Prop)
    (cap : ℕ) : PrefixStoppingIndex (α := Event) where
  toFun := finiteEventFirstHitCapped initial step hit cap
  event_prefix_measurable := by
    intro n
    by_cases hlt : n < cap
    · let hitNow : Set (Finset.range (n + 1) → Event) := {x |
        hit (finiteEventTrajectory initial step n (fun i =>
          x ⟨i, Finset.mem_range.mpr (Nat.lt_succ_of_le i.isLt.le)⟩))}
      let noEarlierHit : Set (Finset.range (n + 1) → Event) := {x |
        ∀ m : Fin n, ¬ hit (finiteEventTrajectory initial step m (fun i =>
          x ⟨i, Finset.mem_range.mpr
            (Nat.lt_succ_of_le (Nat.le_of_lt (lt_trans i.isLt m.isLt)))⟩))}
      refine MeasurableSpace.measurableSet_comap.2
        ⟨hitNow ∩ noEarlierHit, (Set.toFinite _).measurableSet, ?_⟩
      ext omega
      simp only [Set.preimage_inter, Set.mem_inter_iff, Set.mem_preimage,
        Set.mem_setOf_eq]
      constructor
      · rintro ⟨hnow, hprevious⟩
        apply (finiteEventFirstHitCapped_eq_iff_of_lt initial step hit hlt omega).mpr
        constructor
        · have hprefixNow :=
            finiteEventTrajectory_prefix_eq initial step (Nat.le_refl n) omega
          simpa [hitNow, hprefixNow] using hnow
        · intro m hm
          have hmle : m ≤ n := Nat.le_of_lt hm
          have hprefix := finiteEventTrajectory_prefix_eq initial step hmle omega
          simpa [noEarlierHit, hprefix] using hprevious ⟨m, hm⟩
      · intro hstop
        have hcharacter :=
          (finiteEventFirstHitCapped_eq_iff_of_lt initial step hit hlt omega).mp hstop
        refine ⟨?_, ?_⟩
        · have hprefixNow :=
            finiteEventTrajectory_prefix_eq initial step (Nat.le_refl n) omega
          simpa [hitNow, hprefixNow] using hcharacter.1
        · intro m
          have hmle : (m : ℕ) ≤ n := Nat.le_of_lt m.isLt
          have hprefix := finiteEventTrajectory_prefix_eq initial step hmle omega
          simpa [noEarlierHit, hprefix] using hcharacter.2 m m.isLt
    · by_cases heq : n = cap
      · subst n
        let noEarlierHit : Set (Finset.range (cap + 1) → Event) := {x |
          ∀ m : Fin cap, ¬ hit (finiteEventTrajectory initial step m (fun i =>
            x ⟨i, Finset.mem_range.mpr
              (Nat.lt_succ_of_le (Nat.le_of_lt (lt_trans i.isLt m.isLt)))⟩))}
        refine MeasurableSpace.measurableSet_comap.2
          ⟨noEarlierHit, (Set.toFinite _).measurableSet, ?_⟩
        ext omega
        simp only [Set.mem_preimage, Set.mem_setOf_eq]
        constructor
        · intro hprevious
          apply (finiteEventFirstHitCapped_eq_cap_iff initial step hit cap omega).mpr
          intro m hm
          have hmle : m ≤ cap := Nat.le_of_lt hm
          have hprefix := finiteEventTrajectory_prefix_eq initial step hmle omega
          simpa [noEarlierHit, hprefix] using hprevious ⟨m, hm⟩
        · intro hstop
          have hcharacter :=
            (finiteEventFirstHitCapped_eq_cap_iff initial step hit cap omega).mp hstop
          intro m
          have hmle : (m : ℕ) ≤ cap := Nat.le_of_lt m.isLt
          have hprefix := finiteEventTrajectory_prefix_eq initial step hmle omega
          simpa [noEarlierHit, hprefix] using hcharacter m m.isLt
      · have hgt : cap < n := lt_of_le_of_ne (Nat.le_of_not_gt hlt) (Ne.symm heq)
        classical
        refine MeasurableSpace.measurableSet_comap.2 ⟨∅, MeasurableSet.empty, ?_⟩
        ext omega
        have hle := finiteEventFirstHitCapped_le initial step hit cap omega
        have hne : finiteEventFirstHitCapped initial step hit cap omega ≠ n := by omega
        simp [hne]

end

end AppliedModelingLib.Probability.IIDStream
