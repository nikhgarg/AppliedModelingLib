import AppliedModelingLib.Foundations.Probability.FiniteExpectation
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic

/-!
# Occupancy Processes

Finite balls-into-bins primitives for probabilistic counting arguments.

## Main declarations

- `occupancyUsedBins`: bins hit by an assignment of balls to bins.
- `occupancyEmptyBins`: bins not hit by an assignment.
- `occupancyEmptyBins_card_eq`: exact deterministic empty-bin count.
- `occupancyEmptyBins_card_lower_bound`: at least `#bins - #balls` bins are
  empty.
- `occupancyPMF`: the uniform occupancy law over all ball-to-bin assignments.
-/

open scoped BigOperators

namespace AppliedModelingLib

/-- Bins hit by a deterministic balls-to-bins assignment. -/
noncomputable def occupancyUsedBins {Ball Bin : Type*}
    [Fintype Ball] [DecidableEq Bin]
    (assignment : Ball → Bin) : Finset Bin :=
  (Finset.univ : Finset Ball).image assignment

/-- Empty bins under a deterministic balls-to-bins assignment. -/
noncomputable def occupancyEmptyBins {Ball Bin : Type*}
    [Fintype Ball] [Fintype Bin] [DecidableEq Bin]
    (assignment : Ball → Bin) : Finset Bin :=
  (Finset.univ : Finset Bin) \ occupancyUsedBins assignment

/-- The used bins are a subset of all bins. -/
theorem occupancyUsedBins_subset_univ {Ball Bin : Type*}
    [Fintype Ball] [Fintype Bin] [DecidableEq Bin]
    (assignment : Ball → Bin) :
    occupancyUsedBins assignment ⊆ (Finset.univ : Finset Bin) := by
  intro b _hb
  simp

/-- The exact number of empty bins is `#bins - #usedBins`. -/
theorem occupancyEmptyBins_card_eq {Ball Bin : Type*}
    [Fintype Ball] [Fintype Bin] [DecidableEq Bin]
    (assignment : Ball → Bin) :
    (occupancyEmptyBins assignment).card =
      Fintype.card Bin - (occupancyUsedBins assignment).card := by
  classical
  unfold occupancyEmptyBins
  simpa using
    (Finset.card_sdiff_of_subset
      (occupancyUsedBins_subset_univ assignment))

/-- A deterministic assignment uses no more bins than there are balls. -/
theorem occupancyUsedBins_card_le {Ball Bin : Type*}
    [Fintype Ball] [DecidableEq Bin]
    (assignment : Ball → Bin) :
    (occupancyUsedBins assignment).card ≤ Fintype.card Ball := by
  classical
  unfold occupancyUsedBins
  simpa using
    (Finset.card_image_le :
      ((Finset.univ : Finset Ball).image assignment).card ≤
        (Finset.univ : Finset Ball).card)

/--
For an ordered ball type, `ball` is a first hit if no earlier ball was assigned
to the same bin.
-/
def occupancyFirstHit {Ball Bin : Type*} [LT Ball]
    (assignment : Ball → Bin) (ball : Ball) : Prop :=
  ∀ earlier : Ball, earlier < ball → assignment earlier ≠ assignment ball

/-- The finite set of first-hit balls in an ordered assignment. -/
noncomputable def occupancyFirstHitBalls {Ball Bin : Type*}
    [Fintype Ball] [LinearOrder Ball] [DecidableEq Bin]
    (assignment : Ball → Bin) : Finset Ball := by
  classical
  exact (Finset.univ : Finset Ball).filter fun ball =>
    occupancyFirstHit assignment ball

/--
The image of first-hit balls is exactly the set of used bins.
-/
theorem occupancyFirstHitBalls_image_eq_usedBins
    {Ball Bin : Type*} [Fintype Ball] [LinearOrder Ball] [DecidableEq Bin]
    (assignment : Ball → Bin) :
    (occupancyFirstHitBalls assignment).image assignment =
      occupancyUsedBins assignment := by
  classical
  ext bin
  constructor
  · intro hbin
    rcases Finset.mem_image.mp hbin with ⟨ball, _hball, rfl⟩
    exact Finset.mem_image.mpr ⟨ball, Finset.mem_univ _, rfl⟩
  · intro hbin
    rcases Finset.mem_image.mp hbin with ⟨ball, _hball, hball⟩
    let hits : Finset Ball :=
      (Finset.univ : Finset Ball).filter fun b => assignment b = bin
    have hhits_nonempty : hits.Nonempty := by
      refine ⟨ball, ?_⟩
      simp [hits, hball]
    let first : Ball := hits.min' hhits_nonempty
    have hfirst_mem : first ∈ hits := Finset.min'_mem hits hhits_nonempty
    have hfirst_assignment : assignment first = bin := by
      simpa [hits] using hfirst_mem
    have hfirst_hit : occupancyFirstHit assignment first := by
      intro earlier hearlier hsame
      have hearlier_mem : earlier ∈ hits := by
        simp [hits, hsame, hfirst_assignment]
      have hfirst_le : first ≤ earlier := Finset.min'_le hits earlier hearlier_mem
      exact (not_lt_of_ge hfirst_le) hearlier
    refine Finset.mem_image.mpr ⟨first, ?_, hfirst_assignment⟩
    simp [occupancyFirstHitBalls, hfirst_hit]

/--
The number of used bins is exactly the number of first-hit balls.
-/
theorem occupancyFirstHitBalls_card_eq_usedBins
    {Ball Bin : Type*} [Fintype Ball] [LinearOrder Ball] [DecidableEq Bin]
    (assignment : Ball → Bin) :
    (occupancyFirstHitBalls assignment).card =
      (occupancyUsedBins assignment).card := by
  classical
  have hinj :
      Set.InjOn assignment (↑(occupancyFirstHitBalls assignment) : Set Ball) := by
    intro a ha b hb hsame
    by_cases hab : a = b
    · exact hab
    · rcases lt_or_gt_of_ne hab with hlt | hgt
      · have hb_first : occupancyFirstHit assignment b := by
          simpa [occupancyFirstHitBalls] using hb
        exact False.elim (hb_first a hlt hsame)
      · have ha_first : occupancyFirstHit assignment a := by
          simpa [occupancyFirstHitBalls] using ha
        exact False.elim (ha_first b hgt hsame.symm)
  have hcard :=
    Finset.card_image_of_injOn
      (s := occupancyFirstHitBalls assignment) (f := assignment) hinj
  rw [occupancyFirstHitBalls_image_eq_usedBins assignment] at hcard
  exact hcard.symm

/-- At least `#bins - #balls` bins are empty in any deterministic assignment. -/
theorem occupancyEmptyBins_card_lower_bound {Ball Bin : Type*}
    [Fintype Ball] [Fintype Bin] [DecidableEq Bin]
    (assignment : Ball → Bin) :
    Fintype.card Bin - Fintype.card Ball ≤
      (occupancyEmptyBins assignment).card := by
  classical
  calc
    Fintype.card Bin - Fintype.card Ball
        ≤ Fintype.card Bin - (occupancyUsedBins assignment).card :=
          Nat.sub_le_sub_left (occupancyUsedBins_card_le assignment) _
    _ = (occupancyEmptyBins assignment).card := by
          rw [occupancyEmptyBins_card_eq]

/-- If there are strictly more bins than balls, some bin is empty. -/
theorem occupancyEmptyBins_card_pos_of_card_lt {Ball Bin : Type*}
    [Fintype Ball] [Fintype Bin] [DecidableEq Bin]
    (assignment : Ball → Bin)
    (hcard : Fintype.card Ball < Fintype.card Bin) :
    0 < (occupancyEmptyBins assignment).card := by
  have hpos : 0 < Fintype.card Bin - Fintype.card Ball :=
    Nat.sub_pos_of_lt hcard
  exact lt_of_lt_of_le hpos (occupancyEmptyBins_card_lower_bound assignment)

/-- If one assignment uses a subset of the bins used by another, its empty-bin
set contains the other's empty-bin set. -/
theorem occupancyEmptyBins_subset_of_usedBins_subset {Ball₁ Ball₂ Bin : Type*}
    [Fintype Ball₁] [Fintype Ball₂] [Fintype Bin] [DecidableEq Bin]
    (assignment₁ : Ball₁ → Bin) (assignment₂ : Ball₂ → Bin)
    (hused : occupancyUsedBins assignment₁ ⊆ occupancyUsedBins assignment₂) :
    occupancyEmptyBins assignment₂ ⊆ occupancyEmptyBins assignment₁ := by
  classical
  intro bin hbin
  simp [occupancyEmptyBins] at hbin ⊢
  exact fun h => hbin (hused h)

/-- More named bins means weakly fewer empty bins. -/
theorem occupancyEmptyBins_card_le_of_usedBins_subset
    {Ball₁ Ball₂ Bin : Type*}
    [Fintype Ball₁] [Fintype Ball₂] [Fintype Bin] [DecidableEq Bin]
    (assignment₁ : Ball₁ → Bin) (assignment₂ : Ball₂ → Bin)
    (hused : occupancyUsedBins assignment₁ ⊆ occupancyUsedBins assignment₂) :
    (occupancyEmptyBins assignment₂).card ≤
      (occupancyEmptyBins assignment₁).card :=
  Finset.card_le_card
    (occupancyEmptyBins_subset_of_usedBins_subset
      assignment₁ assignment₂ hused)

/-- Assignments using exactly the same bins have the same number of empty bins. -/
theorem occupancyEmptyBins_card_eq_of_usedBins_eq
    {Ball₁ Ball₂ Bin : Type*}
    [Fintype Ball₁] [Fintype Ball₂] [Fintype Bin] [DecidableEq Bin]
    (assignment₁ : Ball₁ → Bin) (assignment₂ : Ball₂ → Bin)
    (hused : occupancyUsedBins assignment₁ = occupancyUsedBins assignment₂) :
    (occupancyEmptyBins assignment₁).card =
      (occupancyEmptyBins assignment₂).card := by
  simp [occupancyEmptyBins, hused]

/-- The uniform occupancy law over all assignments of balls to bins. -/
noncomputable def occupancyPMF (Ball Bin : Type*)
    [Fintype Ball] [DecidableEq Ball] [Fintype Bin] [Nonempty Bin] :
    PMF (Ball → Bin) := by
  classical
  exact uniformPMF (Ball → Bin)

/-- The reciprocal empty-bin statistic used in matching-market occupancy. -/
noncomputable def occupancyReciprocalEmptyBins {Ball Bin : Type*}
    [Fintype Ball] [Fintype Bin] [DecidableEq Bin]
    (assignment : Ball → Bin) : ℝ :=
  (((occupancyEmptyBins assignment).card + 1 : ℕ) : ℝ)⁻¹

/-- Uniform expectation of the reciprocal empty-bin statistic. -/
noncomputable def occupancyReciprocalExpectation (Ball Bin : Type*)
    [Fintype Ball] [DecidableEq Ball]
    [Fintype Bin] [DecidableEq Bin] [Nonempty Bin] : ℝ := by
  classical
  exact pmfExp (occupancyPMF Ball Bin)
    (fun assignment : Ball → Bin => occupancyReciprocalEmptyBins assignment)

/-! ## Relabeling and one-ball extensions -/

/-- Relabeling balls by an equivalence preserves the set of used bins. -/
theorem occupancyUsedBins_comp_equiv {Ball₁ Ball₂ Bin : Type*}
    [Fintype Ball₁] [Fintype Ball₂] [DecidableEq Bin]
    (e : Ball₁ ≃ Ball₂) (assignment : Ball₂ → Bin) :
    occupancyUsedBins (fun ball₁ => assignment (e ball₁)) =
      occupancyUsedBins assignment := by
  classical
  ext bin
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨ball₁, _hball₁, hbin⟩
    exact Finset.mem_image.mpr ⟨e ball₁, Finset.mem_univ _, hbin⟩
  · intro h
    rcases Finset.mem_image.mp h with ⟨ball₂, _hball₂, hbin⟩
    refine Finset.mem_image.mpr ⟨e.symm ball₂, Finset.mem_univ _, ?_⟩
    simpa using hbin

/--
If one assignment is obtained by restricting another assignment to a set of
slots via a map, then every used bin in the restricted assignment is used in
the original assignment.
-/
theorem occupancyUsedBins_comp_subset {Ball₁ Ball₂ Bin : Type*}
    [Fintype Ball₁] [Fintype Ball₂] [DecidableEq Bin]
    (slot : Ball₁ → Ball₂) (assignment : Ball₂ → Bin) :
    occupancyUsedBins (fun ball₁ => assignment (slot ball₁)) ⊆
      occupancyUsedBins assignment := by
  classical
  intro bin hbin
  rcases Finset.mem_image.mp hbin with ⟨ball₁, _hball₁, hhit⟩
  exact Finset.mem_image.mpr ⟨slot ball₁, Finset.mem_univ _, hhit⟩

/-- Relabeling balls by an equivalence preserves the set of empty bins. -/
theorem occupancyEmptyBins_comp_equiv {Ball₁ Ball₂ Bin : Type*}
    [Fintype Ball₁] [Fintype Ball₂] [Fintype Bin] [DecidableEq Bin]
    (e : Ball₁ ≃ Ball₂) (assignment : Ball₂ → Bin) :
    occupancyEmptyBins (fun ball₁ => assignment (e ball₁)) =
      occupancyEmptyBins assignment := by
  classical
  unfold occupancyEmptyBins
  rw [occupancyUsedBins_comp_equiv e assignment]

/-- Relabeling balls by an equivalence preserves the reciprocal empty-bin statistic. -/
theorem occupancyReciprocalEmptyBins_comp_equiv {Ball₁ Ball₂ Bin : Type*}
    [Fintype Ball₁] [Fintype Ball₂] [Fintype Bin] [DecidableEq Bin]
    (e : Ball₁ ≃ Ball₂) (assignment : Ball₂ → Bin) :
    occupancyReciprocalEmptyBins (fun ball₁ => assignment (e ball₁)) =
      occupancyReciprocalEmptyBins assignment := by
  simp [occupancyReciprocalEmptyBins, occupancyEmptyBins_comp_equiv e assignment]

/-- The reciprocal empty-bin expectation is invariant under relabeling balls. -/
theorem occupancyReciprocalExpectation_domain_equiv
    {Ball₁ Ball₂ Bin : Type*}
    [Fintype Ball₁] [DecidableEq Ball₁]
    [Fintype Ball₂] [DecidableEq Ball₂]
    [Fintype Bin] [DecidableEq Bin] [Nonempty Bin]
    (e : Ball₁ ≃ Ball₂) :
    occupancyReciprocalExpectation Ball₁ Bin =
      occupancyReciprocalExpectation Ball₂ Bin := by
  classical
  let assignmentEquiv : (Ball₁ → Bin) ≃ (Ball₂ → Bin) :=
    { toFun := fun assignment ball₂ => assignment (e.symm ball₂)
      invFun := fun assignment ball₁ => assignment (e ball₁)
      left_inv := by
        intro assignment
        funext ball₁
        simp
      right_inv := by
        intro assignment
        funext ball₂
        simp }
  unfold occupancyReciprocalExpectation occupancyPMF
  symm
  calc
    pmfExp (uniformPMF (Ball₂ → Bin))
        (fun assignment : Ball₂ → Bin =>
          occupancyReciprocalEmptyBins assignment) =
        pmfExp (uniformPMF (Ball₁ → Bin))
          (fun assignment : Ball₁ → Bin =>
            occupancyReciprocalEmptyBins (assignmentEquiv assignment)) :=
          pmfExp_uniformPMF_equiv assignmentEquiv
            (fun assignment : Ball₂ → Bin =>
              occupancyReciprocalEmptyBins assignment)
    _ = pmfExp (uniformPMF (Ball₁ → Bin))
          (fun assignment : Ball₁ → Bin =>
            occupancyReciprocalEmptyBins assignment) := by
          refine pmfExp_congr (uniformPMF (Ball₁ → Bin)) ?_
          intro assignment
          exact occupancyReciprocalEmptyBins_comp_equiv
            (e := e.symm) (assignment := assignment)

/-- Relabeling bins by an equivalence maps empty bins to empty bins. -/
theorem occupancyUsedBins_bin_equiv {Ball Bin₁ Bin₂ : Type*}
    [Fintype Ball] [DecidableEq Bin₁] [DecidableEq Bin₂]
    (e : Bin₁ ≃ Bin₂) (assignment : Ball → Bin₁) :
    occupancyUsedBins (fun ball => e (assignment ball)) =
      (occupancyUsedBins assignment).image e := by
  classical
  ext bin₂
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨ball, _hball, hbin⟩
    exact Finset.mem_image.mpr
      ⟨assignment ball,
        Finset.mem_image.mpr ⟨ball, Finset.mem_univ _, rfl⟩,
        hbin⟩
  · intro h
    rcases Finset.mem_image.mp h with ⟨bin₁, hbin₁, rfl⟩
    rcases Finset.mem_image.mp hbin₁ with ⟨ball, _hball, hhit⟩
    exact Finset.mem_image.mpr ⟨ball, Finset.mem_univ _, by simp [hhit]⟩

/-- Relabeling bins by an equivalence preserves the number of used bins. -/
theorem occupancyUsedBins_card_bin_equiv {Ball Bin₁ Bin₂ : Type*}
    [Fintype Ball] [DecidableEq Bin₁] [DecidableEq Bin₂]
    (e : Bin₁ ≃ Bin₂) (assignment : Ball → Bin₁) :
    (occupancyUsedBins (fun ball => e (assignment ball))).card =
      (occupancyUsedBins assignment).card := by
  rw [occupancyUsedBins_bin_equiv e assignment]
  rw [Finset.card_image_of_injective _ e.injective]

/-- Relabeling bins by an equivalence maps empty bins to empty bins. -/
theorem occupancyEmptyBins_bin_equiv {Ball Bin₁ Bin₂ : Type*}
    [Fintype Ball] [Fintype Bin₁] [Fintype Bin₂]
    [DecidableEq Bin₁] [DecidableEq Bin₂]
    (e : Bin₁ ≃ Bin₂) (assignment : Ball → Bin₁) :
    occupancyEmptyBins (fun ball => e (assignment ball)) =
      (occupancyEmptyBins assignment).image e := by
  classical
  ext bin₂
  constructor
  · intro h
    refine Finset.mem_image.mpr ⟨e.symm bin₂, ?_, by simp⟩
    simp [occupancyEmptyBins, occupancyUsedBins] at h ⊢
    intro ball hEq
    exact h ball (by simpa [hEq])
  · intro h
    rcases Finset.mem_image.mp h with ⟨bin₁, hbin₁, rfl⟩
    simp [occupancyEmptyBins, occupancyUsedBins] at hbin₁ ⊢
    intro ball hEq
    exact hbin₁ ball hEq

/-- Relabeling bins preserves the reciprocal empty-bin statistic. -/
theorem occupancyReciprocalEmptyBins_bin_equiv {Ball Bin₁ Bin₂ : Type*}
    [Fintype Ball] [Fintype Bin₁] [Fintype Bin₂]
    [DecidableEq Bin₁] [DecidableEq Bin₂]
    (e : Bin₁ ≃ Bin₂) (assignment : Ball → Bin₁) :
    occupancyReciprocalEmptyBins (fun ball => e (assignment ball)) =
      occupancyReciprocalEmptyBins assignment := by
  unfold occupancyReciprocalEmptyBins
  rw [occupancyEmptyBins_bin_equiv e assignment]
  rw [Finset.card_image_of_injective _ e.injective]

/-- The reciprocal empty-bin expectation is invariant under relabeling bins. -/
theorem occupancyReciprocalExpectation_bin_equiv
    {Ball Bin₁ Bin₂ : Type*}
    [Fintype Ball] [DecidableEq Ball]
    [Fintype Bin₁] [DecidableEq Bin₁] [Nonempty Bin₁]
    [Fintype Bin₂] [DecidableEq Bin₂] [Nonempty Bin₂]
    (e : Bin₁ ≃ Bin₂) :
    occupancyReciprocalExpectation Ball Bin₁ =
      occupancyReciprocalExpectation Ball Bin₂ := by
  classical
  let assignmentEquiv : (Ball → Bin₁) ≃ (Ball → Bin₂) :=
    { toFun := fun assignment ball => e (assignment ball)
      invFun := fun assignment ball => e.symm (assignment ball)
      left_inv := by
        intro assignment
        funext ball
        simp
      right_inv := by
        intro assignment
        funext ball
        simp }
  unfold occupancyReciprocalExpectation occupancyPMF
  symm
  calc
    pmfExp (uniformPMF (Ball → Bin₂))
        (fun assignment : Ball → Bin₂ =>
          occupancyReciprocalEmptyBins assignment) =
        pmfExp (uniformPMF (Ball → Bin₁))
          (fun assignment : Ball → Bin₁ =>
            occupancyReciprocalEmptyBins (assignmentEquiv assignment)) :=
          pmfExp_uniformPMF_equiv assignmentEquiv
            (fun assignment : Ball → Bin₂ =>
              occupancyReciprocalEmptyBins assignment)
    _ = pmfExp (uniformPMF (Ball → Bin₁))
          (fun assignment : Ball → Bin₁ =>
            occupancyReciprocalEmptyBins assignment) := by
          refine pmfExp_congr (uniformPMF (Ball → Bin₁)) ?_
          intro assignment
          exact occupancyReciprocalEmptyBins_bin_equiv e assignment

/-- Extend an occupancy assignment by one additional ball. -/
def occupancyOptionExtend {Ball Bin : Type*}
    (assignment : Ball → Bin) (newBin : Bin) : Option Ball → Bin
  | none => newBin
  | some ball => assignment ball

/-- Used-bin membership after adding one ball. -/
theorem mem_occupancyUsedBins_optionExtend_iff {Ball Bin : Type*}
    [Fintype Ball] [DecidableEq Bin]
    (assignment : Ball → Bin) (newBin bin : Bin) :
    bin ∈ occupancyUsedBins (occupancyOptionExtend assignment newBin) ↔
      bin = newBin ∨ bin ∈ occupancyUsedBins assignment := by
  classical
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨ball?, _hball, hbin⟩
    cases ball? with
    | none =>
        exact Or.inl hbin.symm
    | some ball =>
        exact Or.inr
          (Finset.mem_image.mpr ⟨ball, Finset.mem_univ _, hbin⟩)
  · rintro (rfl | h)
    · exact Finset.mem_image.mpr ⟨none, Finset.mem_univ _, rfl⟩
    · rcases Finset.mem_image.mp h with ⟨ball, _hball, hbin⟩
      exact Finset.mem_image.mpr ⟨some ball, Finset.mem_univ _, hbin⟩

/-- Empty-bin membership after adding one ball. -/
theorem mem_occupancyEmptyBins_optionExtend_iff {Ball Bin : Type*}
    [Fintype Ball] [Fintype Bin] [DecidableEq Bin]
    (assignment : Ball → Bin) (newBin bin : Bin) :
    bin ∈ occupancyEmptyBins (occupancyOptionExtend assignment newBin) ↔
      bin ≠ newBin ∧ bin ∈ occupancyEmptyBins assignment := by
  classical
  simp [occupancyEmptyBins, mem_occupancyUsedBins_optionExtend_iff,
    not_or]

/--
Adding one ball removes its selected bin from the empty-bin set exactly when
that bin was empty.
-/
theorem occupancyEmptyBins_optionExtend {Ball Bin : Type*}
    [Fintype Ball] [Fintype Bin] [DecidableEq Bin]
    (assignment : Ball → Bin) (newBin : Bin) :
    occupancyEmptyBins (occupancyOptionExtend assignment newBin) =
      if newBin ∈ occupancyEmptyBins assignment then
        (occupancyEmptyBins assignment).erase newBin
      else
        occupancyEmptyBins assignment := by
  classical
  ext bin
  rw [mem_occupancyEmptyBins_optionExtend_iff]
  by_cases hempty : newBin ∈ occupancyEmptyBins assignment
  · simp [hempty]
  · simp [hempty]
    intro hbin hEq
    exact hempty (by simpa [hEq] using hbin)

/--
Reciprocal empty-bin statistic after adding one ball, split by whether the
chosen bin was empty before the addition.
-/
theorem occupancyReciprocalEmptyBins_optionExtend_eq_if {Ball Bin : Type*}
    [Fintype Ball] [Fintype Bin] [DecidableEq Bin]
    (assignment : Ball → Bin) (newBin : Bin) :
    occupancyReciprocalEmptyBins (occupancyOptionExtend assignment newBin) =
      if newBin ∈ occupancyEmptyBins assignment then
        (((occupancyEmptyBins assignment).card : ℕ) : ℝ)⁻¹
      else
        occupancyReciprocalEmptyBins assignment := by
  classical
  unfold occupancyReciprocalEmptyBins
  rw [occupancyEmptyBins_optionExtend]
  by_cases hempty : newBin ∈ occupancyEmptyBins assignment
  · simp [hempty]
    have hpos : 0 < (occupancyEmptyBins assignment).card :=
      Finset.card_pos.mpr ⟨newBin, hempty⟩
    have hnat :
        ((occupancyEmptyBins assignment).card - 1) + 1 =
          (occupancyEmptyBins assignment).card :=
      Nat.sub_add_cancel (Nat.succ_le_iff.mpr hpos)
    exact_mod_cast hnat
  · simp [hempty]

/--
One-ball recurrence for the reciprocal empty-bin statistic.  Averaging over a
uniformly chosen bin for the new ball multiplies the old statistic by at most
`(#bins + 1) / #bins`.
-/
theorem occupancyOptionExtend_reciprocal_expectation_le {Ball Bin : Type*}
    [Fintype Ball] [Fintype Bin] [DecidableEq Bin] [Nonempty Bin]
    (assignment : Ball → Bin) :
    pmfExp (uniformPMF Bin)
        (fun newBin : Bin =>
          occupancyReciprocalEmptyBins
            (occupancyOptionExtend assignment newBin)) ≤
      (((Fintype.card Bin : ℕ) : ℝ) + 1) / (Fintype.card Bin : ℝ) *
        occupancyReciprocalEmptyBins assignment := by
  classical
  let s : Finset Bin := occupancyEmptyBins assignment
  let y : ℝ := s.card
  let n : ℝ := Fintype.card Bin
  have hnpos : 0 < n := by
    dsimp [n]
    exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty Bin›)
  have hy_nonneg : 0 ≤ y := by
    dsimp [y]
    exact_mod_cast (Nat.zero_le s.card)
  have hold : occupancyReciprocalEmptyBins assignment = (y + 1)⁻¹ := by
    simp [occupancyReciprocalEmptyBins, s, y]
  have hpoint :
      ∀ newBin : Bin,
        occupancyReciprocalEmptyBins
            (occupancyOptionExtend assignment newBin) =
          if newBin ∈ s then y⁻¹ else occupancyReciprocalEmptyBins assignment := by
    intro newBin
    simpa [s, y] using
      occupancyReciprocalEmptyBins_optionExtend_eq_if assignment newBin
  calc
    pmfExp (uniformPMF Bin)
        (fun newBin : Bin =>
          occupancyReciprocalEmptyBins
            (occupancyOptionExtend assignment newBin)) =
        pmfProb (uniformPMF Bin) (fun newBin => newBin ∈ s) * y⁻¹ +
          (1 - pmfProb (uniformPMF Bin) (fun newBin => newBin ∈ s)) *
            occupancyReciprocalEmptyBins assignment := by
          exact pmfExp_eq_prob_mul_add_one_sub_prob_mul_of_forall_eq_if
            (uniformPMF Bin) (fun newBin => newBin ∈ s)
            (fun newBin : Bin =>
              occupancyReciprocalEmptyBins
                (occupancyOptionExtend assignment newBin))
            y⁻¹ (occupancyReciprocalEmptyBins assignment) hpoint
    _ = (y / n) * y⁻¹ + (1 - y / n) * (y + 1)⁻¹ := by
          rw [pmfProb_uniformPMF_finset s, hold]
    _ ≤ ((n + 1) / n) * (y + 1)⁻¹ := by
          by_cases hyzero : y = 0
          · simp [hyzero]
            rw [le_div_iff₀ hnpos]
            nlinarith [hnpos]
          · have hypos : 0 < y := lt_of_le_of_ne hy_nonneg (Ne.symm hyzero)
            have hy1 : y + 1 ≠ 0 := by nlinarith
            field_simp [hnpos.ne', hypos.ne', hy1]
            linarith
    _ = (((Fintype.card Bin : ℕ) : ℝ) + 1) /
          (Fintype.card Bin : ℝ) *
        occupancyReciprocalEmptyBins assignment := by
          rw [hold]

/-- Adding one uniformly assigned ball multiplies the reciprocal empty-bin
expectation by at most `(#bins + 1) / #bins`. -/
theorem occupancyReciprocalExpectation_option_le {Ball Bin : Type*}
    [Fintype Ball] [DecidableEq Ball]
    [Fintype Bin] [DecidableEq Bin] [Nonempty Bin] :
    occupancyReciprocalExpectation (Option Ball) Bin ≤
      (((Fintype.card Bin : ℕ) : ℝ) + 1) / (Fintype.card Bin : ℝ) *
        occupancyReciprocalExpectation Ball Bin := by
  classical
  let optionAssignmentEquiv : (Option Ball → Bin) ≃ (Ball → Bin) × Bin :=
    { toFun := fun assignment =>
        (fun ball => assignment (some ball), assignment none)
      invFun := fun pair => occupancyOptionExtend pair.1 pair.2
      left_inv := by
        intro assignment
        funext ball?
        cases ball? <;> rfl
      right_inv := by
        intro pair
        cases pair with
        | mk assignment newBin =>
            rfl }
  have hdecomp :
      occupancyReciprocalExpectation (Option Ball) Bin =
        pmfPairExp (uniformPMF (Ball → Bin)) (uniformPMF Bin)
          (fun assignment newBin =>
            occupancyReciprocalEmptyBins
              (occupancyOptionExtend assignment newBin)) := by
    unfold occupancyReciprocalExpectation occupancyPMF
    calc
      pmfExp (uniformPMF (Option Ball → Bin))
          (fun assignment : Option Ball → Bin =>
            occupancyReciprocalEmptyBins assignment) =
          pmfExp (uniformPMF ((Ball → Bin) × Bin))
            (fun pair : (Ball → Bin) × Bin =>
              occupancyReciprocalEmptyBins
                (optionAssignmentEquiv.symm pair)) := by
            exact pmfExp_uniformPMF_equiv optionAssignmentEquiv.symm
              (fun assignment : Option Ball → Bin =>
                occupancyReciprocalEmptyBins assignment)
      _ = pmfPairExp (uniformPMF (Ball → Bin)) (uniformPMF Bin)
            (fun assignment newBin =>
              occupancyReciprocalEmptyBins
                (occupancyOptionExtend assignment newBin)) := by
            rw [pmfExp_uniformPMF_prod]
            rfl
  calc
    occupancyReciprocalExpectation (Option Ball) Bin =
        pmfPairExp (uniformPMF (Ball → Bin)) (uniformPMF Bin)
          (fun assignment newBin =>
            occupancyReciprocalEmptyBins
              (occupancyOptionExtend assignment newBin)) := hdecomp
    _ ≤ pmfExp (uniformPMF (Ball → Bin))
          (fun assignment : Ball → Bin =>
            (((Fintype.card Bin : ℕ) : ℝ) + 1) /
              (Fintype.card Bin : ℝ) *
              occupancyReciprocalEmptyBins assignment) := by
          unfold pmfPairExp
          refine pmfExp_le_pmfExp_of_forall_le
            (uniformPMF (Ball → Bin)) _ _ ?_
          intro assignment
          exact occupancyOptionExtend_reciprocal_expectation_le assignment
    _ = (((Fintype.card Bin : ℕ) : ℝ) + 1) /
          (Fintype.card Bin : ℝ) *
        occupancyReciprocalExpectation Ball Bin := by
          unfold occupancyReciprocalExpectation occupancyPMF
          rw [pmfExp_const_mul]

/-- With no balls, all bins are empty. -/
theorem occupancyReciprocalExpectation_fin_zero (n : ℕ) [NeZero n] :
    occupancyReciprocalExpectation (Fin 0) (Fin n) =
      (((n : ℕ) : ℝ) + 1)⁻¹ := by
  classical
  unfold occupancyReciprocalExpectation occupancyPMF
  calc
    pmfExp (uniformPMF (Fin 0 → Fin n))
        (fun assignment : Fin 0 → Fin n =>
          occupancyReciprocalEmptyBins assignment) =
        pmfExp (uniformPMF (Fin 0 → Fin n))
          (fun _ : Fin 0 → Fin n => (((n : ℕ) : ℝ) + 1)⁻¹) := by
          refine pmfExp_congr (uniformPMF (Fin 0 → Fin n)) ?_
          intro assignment
          unfold occupancyReciprocalEmptyBins occupancyEmptyBins occupancyUsedBins
          simp [Fintype.card_fin]
    _ = (((n : ℕ) : ℝ) + 1)⁻¹ := by
          rw [pmfExp_const]

/--
Geometric recurrence bound for the finite occupancy reciprocal:
`E[1/(Y_{m,n}+1)] <= ((n+1)/n)^m/(n+1)`.
-/
theorem occupancyReciprocalExpectation_fin_le_geometric
    (m n : ℕ) [NeZero n] :
    occupancyReciprocalExpectation (Fin m) (Fin n) ≤
      ((((n : ℕ) : ℝ) + 1) / (n : ℝ)) ^ m *
        ((((n : ℕ) : ℝ) + 1)⁻¹) := by
  classical
  induction m with
  | zero =>
      rw [occupancyReciprocalExpectation_fin_zero n]
      simp
  | succ m ih =>
      let factor : ℝ := (((n : ℕ) : ℝ) + 1) / (n : ℝ)
      have hnpos : 0 < (n : ℝ) := by
        exact_mod_cast (NeZero.pos n)
      have hfactor_nonneg : 0 ≤ factor := by
        dsimp [factor]
        exact div_nonneg (by positivity) (le_of_lt hnpos)
      have hrel :
          occupancyReciprocalExpectation (Fin (m + 1)) (Fin n) =
            occupancyReciprocalExpectation (Option (Fin m)) (Fin n) :=
        occupancyReciprocalExpectation_domain_equiv
          (e := finSuccEquiv m)
      calc
        occupancyReciprocalExpectation (Fin (m + 1)) (Fin n) =
            occupancyReciprocalExpectation (Option (Fin m)) (Fin n) := hrel
        _ ≤ factor * occupancyReciprocalExpectation (Fin m) (Fin n) := by
              simpa [factor, Fintype.card_fin] using
                occupancyReciprocalExpectation_option_le
                  (Ball := Fin m) (Bin := Fin n)
        _ ≤ factor * (factor ^ m * ((((n : ℕ) : ℝ) + 1)⁻¹)) :=
              mul_le_mul_of_nonneg_left ih hfactor_nonneg
        _ = factor ^ (m + 1) * ((((n : ℕ) : ℝ) + 1)⁻¹) := by
              ring
        _ = ((((n : ℕ) : ℝ) + 1) / (n : ℝ)) ^ (m + 1) *
              ((((n : ℕ) : ℝ) + 1)⁻¹) := rfl

/--
Exponential form of the occupancy reciprocal bound:
`E[1/(Y_{m,n}+1)] <= exp(m/n)/n`.
-/
theorem occupancyReciprocalExpectation_fin_le_exp_div
    (m n : ℕ) [NeZero n] :
    occupancyReciprocalExpectation (Fin m) (Fin n) ≤
      Real.exp ((m : ℝ) / (n : ℝ)) / (n : ℝ) := by
  classical
  let factor : ℝ := (((n : ℕ) : ℝ) + 1) / (n : ℝ)
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (NeZero.pos n)
  have hfactor_nonneg : 0 ≤ factor := by
    dsimp [factor]
    exact div_nonneg (by positivity) (le_of_lt hnpos)
  have hfactor_eq : factor = 1 + (n : ℝ)⁻¹ := by
    dsimp [factor]
    have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
    rw [div_eq_mul_inv]
    rw [add_mul, mul_inv_cancel₀ hnne, one_mul]
  have hfactor_le_exp : factor ≤ Real.exp ((n : ℝ)⁻¹) := by
    rw [hfactor_eq]
    simpa [add_comm] using Real.add_one_le_exp ((n : ℝ)⁻¹)
  have hpow :
      factor ^ m ≤ Real.exp ((m : ℝ) / (n : ℝ)) := by
    calc
      factor ^ m ≤ (Real.exp ((n : ℝ)⁻¹)) ^ m :=
        pow_le_pow_left₀ hfactor_nonneg hfactor_le_exp m
      _ = Real.exp ((m : ℝ) * (n : ℝ)⁻¹) :=
        (Real.exp_nat_mul ((n : ℝ)⁻¹) m).symm
      _ = Real.exp ((m : ℝ) / (n : ℝ)) := by
        rw [div_eq_mul_inv]
  have hden :
      ((((n : ℕ) : ℝ) + 1)⁻¹) ≤ (n : ℝ)⁻¹ := by
    have hnp1 : 0 < (((n : ℕ) : ℝ) + 1) := by positivity
    exact (inv_le_inv₀ hnp1 hnpos).mpr (by nlinarith)
  have hden_nonneg : 0 ≤ ((((n : ℕ) : ℝ) + 1)⁻¹) := by
    positivity
  have hexp_nonneg : 0 ≤ Real.exp ((m : ℝ) / (n : ℝ)) :=
    le_of_lt (Real.exp_pos _)
  calc
    occupancyReciprocalExpectation (Fin m) (Fin n) ≤
        factor ^ m * ((((n : ℕ) : ℝ) + 1)⁻¹) := by
          simpa [factor] using
            occupancyReciprocalExpectation_fin_le_geometric m n
    _ ≤ Real.exp ((m : ℝ) / (n : ℝ)) * (n : ℝ)⁻¹ :=
        mul_le_mul hpow hden hden_nonneg hexp_nonneg
    _ = Real.exp ((m : ℝ) / (n : ℝ)) / (n : ℝ) := by
        exact (div_eq_mul_inv (Real.exp ((m : ℝ) / (n : ℝ))) (n : ℝ)).symm

/-- The reciprocal empty-bin statistic is always at most one. -/
theorem occupancyReciprocalEmptyBins_le_one {Ball Bin : Type*}
    [Fintype Ball] [Fintype Bin] [DecidableEq Bin]
    (assignment : Ball → Bin) :
    occupancyReciprocalEmptyBins assignment ≤ 1 := by
  unfold occupancyReciprocalEmptyBins
  have hden : 1 ≤ (((occupancyEmptyBins assignment).card + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
  exact inv_le_one_of_one_le₀ hden
/-- The reciprocal empty-bin expectation is always at most one. -/
theorem occupancyReciprocalExpectation_le_one (Ball Bin : Type*)
    [Fintype Ball] [DecidableEq Ball]
    [Fintype Bin] [DecidableEq Bin] [Nonempty Bin] :
    occupancyReciprocalExpectation Ball Bin ≤ 1 := by
  classical
  unfold occupancyReciprocalExpectation
  exact pmfExp_le_of_forall_le (occupancyPMF Ball Bin)
    (fun assignment : Ball → Bin => occupancyReciprocalEmptyBins assignment)
    1 occupancyReciprocalEmptyBins_le_one

end AppliedModelingLib
