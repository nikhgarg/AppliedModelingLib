import AppliedModelingLib.Foundations.Math.FiniteChoice
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Logic.Relation

/-!
# Linear Assignment Appendix Model

Finite-slot model for the paper's linear-assignment appendix results.  The
model keeps the assignment objective primitive and proves the slot-ordering
lemma from local one-slot optimality.
-/

namespace DGD26AdmissionsPredictability

namespace LAP

variable {α σ : Type*} [DecidableEq α] [DecidableEq σ] [Fintype σ]

/-- A finite-slot assignment. Each slot contains at most one applicant. -/
structure Assignment (α σ : Type*) where
  matchSlot : σ → Option α

namespace Assignment

/-- Applicant `a` is assigned somewhere. -/
def Assigned (A : Assignment α σ) (a : α) : Prop :=
  ∃ s, A.matchSlot s = some a

/-- The set of applicants assigned to at least one slot. -/
def chosenSet (A : Assignment α σ) : Finset α :=
  Finset.univ.biUnion fun s =>
    match A.matchSlot s with
    | none => ∅
    | some a => {a}

omit [DecidableEq σ] in
/-- Membership in `chosenSet` is the same as being assigned to some slot. -/
theorem mem_chosenSet {A : Assignment α σ} {a : α} :
    a ∈ A.chosenSet ↔ A.Assigned a := by
  classical
  constructor
  · intro ha
    rw [chosenSet] at ha
    rcases Finset.mem_biUnion.mp ha with ⟨s, _hs, haslot⟩
    cases hslot : A.matchSlot s with
    | none =>
        simp [hslot] at haslot
    | some b =>
        have hab : a = b := by
          simpa [hslot] using haslot
        exact ⟨s, by simpa [hab] using hslot⟩
  · rintro ⟨s, hslot⟩
    rw [chosenSet]
    exact Finset.mem_biUnion.mpr
      ⟨s, Finset.mem_univ s, by simp [hslot]⟩

/-- Every assigned applicant is drawn from the offered pool `X`. -/
def AssignedFrom (X : Finset α) (A : Assignment α σ) : Prop :=
  ∀ {s a}, A.matchSlot s = some a → a ∈ X

/-- No applicant occupies two distinct slots. -/
def NoDuplicateApplicants (A : Assignment α σ) : Prop :=
  ∀ {s t a}, A.matchSlot s = some a → A.matchSlot t = some a → s = t

/-- Feasibility for the finite assignment model. -/
def Feasible (X : Finset α) (A : Assignment α σ) : Prop :=
  AssignedFrom X A ∧ NoDuplicateApplicants A

/--
Capacity-filling convention for an assignment at pool `X`: below slot capacity,
all applicants are assigned; at or above slot capacity, every slot is occupied.
-/
def CapacityFilling (X : Finset α) (A : Assignment α σ) : Prop :=
  (X.card ≤ Fintype.card σ → X ⊆ A.chosenSet) ∧
    (Fintype.card σ ≤ X.card → ∀ s, ∃ a, A.matchSlot s = some a)

/-- Applicant `a` is in the offered pool but unassigned. -/
def Rejected (X : Finset α) (A : Assignment α σ) (a : α) : Prop :=
  a ∈ X ∧ ¬ Assigned A a

omit [DecidableEq σ] in
/-- A feasible assignment chooses only applicants from the offered pool. -/
theorem chosenSet_subset_of_feasible
    {X : Finset α} {A : Assignment α σ} (hfeas : Feasible X A) :
    A.chosenSet ⊆ X := by
  intro a ha
  rcases mem_chosenSet.mp ha with ⟨s, hslot⟩
  exact hfeas.1 hslot

omit [DecidableEq σ] in
/-- An applicant outside the offered pool cannot be chosen by a feasible assignment. -/
theorem not_mem_chosenSet_of_not_mem_of_feasible
    {X : Finset α} {A : Assignment α σ} {a : α}
    (hfeas : Feasible X A) (haX : a ∉ X) :
    a ∉ A.chosenSet := by
  intro ha
  exact haX (chosenSet_subset_of_feasible hfeas ha)

omit [DecidableEq α] [DecidableEq σ] in
/-- An applicant outside the offered pool cannot occupy any slot of a feasible assignment. -/
theorem matchSlot_ne_some_of_not_mem_of_feasible
    {X : Finset α} {A : Assignment α σ} {a : α} {s : σ}
    (hfeas : Feasible X A) (haX : a ∉ X) :
    A.matchSlot s ≠ some a := by
  intro hslot
  exact haX (hfeas.1 hslot)

omit [DecidableEq σ] in
/-- If an applicant is not chosen, no slot contains that applicant. -/
theorem matchSlot_ne_some_of_not_mem_chosenSet
    {A : Assignment α σ} {a : α} {s : σ}
    (ha : a ∉ A.chosenSet) :
    A.matchSlot s ≠ some a := by
  intro hslot
  exact ha (mem_chosenSet.mpr ⟨s, hslot⟩)

omit [DecidableEq σ] in
/-- A finite-slot assignment chooses no more applicants than there are slots. -/
theorem chosenSet_card_le_slots (A : Assignment α σ) :
    A.chosenSet.card ≤ Fintype.card σ := by
  classical
  let slotOf : A.chosenSet → σ := fun a =>
    Classical.choose (mem_chosenSet.mp a.2)
  have hinj : Function.Injective slotOf := by
    intro a b hslot
    have hslot_a : A.matchSlot (slotOf a) = some a.1 := by
      dsimp [slotOf]
      exact Classical.choose_spec (mem_chosenSet.mp a.2)
    have hslot_b : A.matchSlot (slotOf b) = some b.1 := by
      dsimp [slotOf]
      exact Classical.choose_spec (mem_chosenSet.mp b.2)
    have hsome : some a.1 = some b.1 := by
      rw [← hslot_a, ← hslot_b, hslot]
    exact Subtype.ext (Option.some.inj hsome)
  have hcard := Fintype.card_le_of_injective slotOf hinj
  simpa [Fintype.card_coe] using hcard

omit [DecidableEq σ] in
/-- If every slot is occupied and applicants are not duplicated, slot count is at most chosen count. -/
theorem slots_card_le_chosenSet_card_of_noDuplicate_of_fillsSlots
    {A : Assignment α σ}
    (hdup : NoDuplicateApplicants A)
    (hfill : ∀ s, ∃ a, A.matchSlot s = some a) :
    Fintype.card σ ≤ A.chosenSet.card := by
  classical
  let applicantOf : σ → α := fun s => Classical.choose (hfill s)
  have happ : ∀ s, A.matchSlot s = some (applicantOf s) := by
    intro s
    exact Classical.choose_spec (hfill s)
  let chosenOfSlot : σ → A.chosenSet := fun s =>
    ⟨applicantOf s, mem_chosenSet.mpr ⟨s, happ s⟩⟩
  have hinj : Function.Injective chosenOfSlot := by
    intro s t hst
    have happ_eq : applicantOf s = applicantOf t :=
      congrArg Subtype.val hst
    exact hdup (happ s) (by simpa [happ_eq] using happ t)
  have hcard := Fintype.card_le_of_injective chosenOfSlot hinj
  simpa [Fintype.card_coe] using hcard

omit [DecidableEq σ] in
/-- A no-duplicate assignment that fills every slot chooses exactly slot-many applicants. -/
theorem chosenSet_card_eq_slots_of_noDuplicate_of_fillsSlots
    {A : Assignment α σ}
    (hdup : NoDuplicateApplicants A)
    (hfill : ∀ s, ∃ a, A.matchSlot s = some a) :
    A.chosenSet.card = Fintype.card σ := by
  exact le_antisymm (chosenSet_card_le_slots A)
    (slots_card_le_chosenSet_card_of_noDuplicate_of_fillsSlots hdup hfill)

/-- Choice rule induced by an assignment selector. -/
def choiceRuleOfAssignment (select : Finset α → Assignment α σ) :
    AppliedModelingLib.FiniteChoice.ChoiceRule α :=
  fun X => (select X).chosenSet

omit [DecidableEq σ] in
/--
If each selected assignment is feasible for its input pool, then the induced
assignment choice rule is feasible.
-/
theorem feasible_choiceRuleOfAssignment
    {select : Finset α → Assignment α σ}
    (hfeas : ∀ X, Feasible X (select X)) :
    AppliedModelingLib.FiniteChoice.Feasible (choiceRuleOfAssignment select) := by
  intro X
  exact chosenSet_subset_of_feasible (hfeas X)

omit [DecidableEq σ] in
/--
If selected assignments are feasible and capacity-filling, the induced choice
rule is q-acceptant at capacity equal to the number of slots.
-/
theorem qAcceptant_choiceRuleOfAssignment_of_feasible_of_capacityFilling
    {select : Finset α → Assignment α σ}
    (hfeas : ∀ X, Feasible X (select X))
    (hfill : ∀ X, CapacityFilling X (select X)) :
    AppliedModelingLib.FiniteChoice.QAcceptant
      (Fintype.card σ) (choiceRuleOfAssignment select) := by
  intro X
  by_cases hsmall : X.card ≤ Fintype.card σ
  · have hchosen_eq : (select X).chosenSet = X := by
      apply Finset.Subset.antisymm
      · exact chosenSet_subset_of_feasible (hfeas X)
      · exact (hfill X).1 hsmall
    simp [choiceRuleOfAssignment, hchosen_eq, Nat.min_eq_right hsmall]
  · have hlarge : Fintype.card σ ≤ X.card := by omega
    have hcard :
        (select X).chosenSet.card = Fintype.card σ :=
      chosenSet_card_eq_slots_of_noDuplicate_of_fillsSlots
        (hfeas X).2 ((hfill X).2 hlarge)
    simp [choiceRuleOfAssignment, hcard, Nat.min_eq_left hlarge]

omit [DecidableEq σ] in
/--
For any assignment-induced choice rule, the borderline set at a pool is no
larger than the number of slots.
-/
theorem borderlineSet_choiceRuleOfAssignment_card_le_slots [Fintype α]
    (select : Finset α → Assignment α σ) (X : Finset α) :
    (AppliedModelingLib.FiniteChoice.borderlineSet
      (choiceRuleOfAssignment select) X).card ≤ Fintype.card σ := by
  have hborder :=
    AppliedModelingLib.FiniteChoice.borderlineSet_card_le_choice_card
      (choiceRuleOfAssignment select) X
  have hchoice := chosenSet_card_le_slots (select X)
  exact hborder.trans hchoice

omit [DecidableEq σ] in
/-- Assignment-induced choice rules have variability bounded by the number of slots. -/
theorem variabilityAtMost_choiceRuleOfAssignment_slots [Fintype α]
    (select : Finset α → Assignment α σ) :
    AppliedModelingLib.FiniteChoice.VariabilityAtMost
      (Fintype.card σ) (choiceRuleOfAssignment select) := by
  intro X
  exact borderlineSet_choiceRuleOfAssignment_card_le_slots select X

/--
Two slots induce the same strict applicant order when every pair of applicants
is ordered the same way by their slot weights.
-/
def SameSlotOrder (w : α → σ → ℝ) (s t : σ) : Prop :=
  ∀ a b, w a s < w b s ↔ w a t < w b t

/-- A slot has no applicant weight ties. -/
def SlotNoTies (w : α → σ → ℝ) (s : σ) : Prop :=
  ∀ {a b}, a ≠ b → w a s ≠ w b s

omit [DecidableEq α] [DecidableEq σ] in
theorem sameSlotOrder_refl (w : α → σ → ℝ) (s : σ) :
    SameSlotOrder w s s := by
  intro a b
  rfl

omit [DecidableEq α] in
theorem SameSlotOrder.symm {w : α → σ → ℝ} {s t : σ}
    (h : SameSlotOrder w s t) :
    SameSlotOrder w t s := by
  intro a b
  exact (h a b).symm

omit [DecidableEq α] [DecidableEq σ] [Fintype σ] in
theorem SameSlotOrder.trans {w : α → σ → ℝ} {s t u : σ}
    (hst : SameSlotOrder w s t) (htu : SameSlotOrder w t u) :
    SameSlotOrder w s u := by
  intro a b
  exact (hst a b).trans (htu a b)

/-- Equality of slot-induced applicant orders as a canonical setoid. -/
def sameSlotOrderSetoid (w : α → σ → ℝ) : Setoid σ where
  r := SameSlotOrder w
  iseqv := {
    refl := sameSlotOrder_refl w
    symm := fun h => SameSlotOrder.symm h
    trans := fun hst htu => SameSlotOrder.trans hst htu
  }

/-- The canonical equivalence class of a slot's induced applicant order. -/
def slotOrderClass (w : α → σ → ℝ) (s : σ) :
    Quotient (sameSlotOrderSetoid w) :=
  Quotient.mk _ s

/-- Equal canonical slot-order classes induce the same applicant order. -/
theorem sameSlotOrder_of_slotOrderClass_eq
    {w : α → σ → ℝ} {s t : σ}
    (h : slotOrderClass w s = slotOrderClass w t) :
    SameSlotOrder w s t := by
  exact Quotient.exact h

/-- Number of distinct applicant orders represented by the finite slot set. -/
noncomputable def distinctSlotOrderCount (w : α → σ → ℝ) : ℕ := by
  classical
  exact ((Finset.univ : Finset σ).image (slotOrderClass w)).card

omit [DecidableEq σ] in
/--
Counting bridge for the LAP distinct-ordering theorem: if two borderline
applicants assigned at slots in the same supplied class must be equal, then
the assignment-induced choice rule has variability bounded by the number of
classes used by the finite slot set.
-/
theorem variabilityAtMost_choiceRuleOfAssignment_of_borderline_slot_class_injective
    [Fintype α] {κ : Type*} [DecidableEq κ]
    {select : Finset α → Assignment α σ} {classOf : σ → κ}
    (hinj :
      ∀ {X : Finset α} {y z : α} {sy sz : σ},
        y ∈ AppliedModelingLib.FiniteChoice.borderlineSet
          (choiceRuleOfAssignment select) X →
        z ∈ AppliedModelingLib.FiniteChoice.borderlineSet
          (choiceRuleOfAssignment select) X →
        (select X).matchSlot sy = some y →
        (select X).matchSlot sz = some z →
        classOf sy = classOf sz →
        y = z) :
    AppliedModelingLib.FiniteChoice.VariabilityAtMost
      ((Finset.univ : Finset σ).image classOf).card
      (choiceRuleOfAssignment select) := by
  classical
  intro X
  let B : Finset α :=
    AppliedModelingLib.FiniteChoice.borderlineSet
      (choiceRuleOfAssignment select) X
  have hslot_exists :
      ∀ y : {a // a ∈ B}, ∃ s, (select X).matchSlot s = some y.1 := by
    intro y
    have hyChoice : y.1 ∈ choiceRuleOfAssignment select X :=
      AppliedModelingLib.FiniteChoice.borderlineSet_subset_choice
        (choiceRuleOfAssignment select) X (by simp [B, y.2])
    change y.1 ∈ (select X).chosenSet at hyChoice
    exact mem_chosenSet.mp hyChoice
  let slotOf : {a // a ∈ B} → σ := fun y => Classical.choose (hslot_exists y)
  let classMap :
      {a // a ∈ B} → {k // k ∈ (Finset.univ : Finset σ).image classOf} :=
    fun y =>
      ⟨classOf (slotOf y),
        Finset.mem_image.mpr ⟨slotOf y, Finset.mem_univ _, rfl⟩⟩
  have hclassMap_inj : Function.Injective classMap := by
    intro y z hEq
    apply Subtype.ext
    have hyB : y.1 ∈ AppliedModelingLib.FiniteChoice.borderlineSet
        (choiceRuleOfAssignment select) X := by
      simp [B, y.2]
    have hzB : z.1 ∈ AppliedModelingLib.FiniteChoice.borderlineSet
        (choiceRuleOfAssignment select) X := by
      simp [B, z.2]
    have hySlot : (select X).matchSlot (slotOf y) = some y.1 :=
      Classical.choose_spec (hslot_exists y)
    have hzSlot : (select X).matchSlot (slotOf z) = some z.1 :=
      Classical.choose_spec (hslot_exists z)
    have hclass : classOf (slotOf y) = classOf (slotOf z) :=
      congrArg Subtype.val hEq
    exact hinj hyB hzB hySlot hzSlot hclass
  have hcard :
      B.card ≤ ((Finset.univ : Finset σ).image classOf).card :=
    Finset.card_le_card_of_injective
      (s := B) (t := (Finset.univ : Finset σ).image classOf)
      hclassMap_inj
  simpa [B] using hcard

omit [DecidableEq σ] in
/--
Paper-shaped counting bridge: if the supplied classifier only identifies slots
with the same induced order, and borderline applicants assigned to same-order
old slots are equal, then variability is bounded by the number of supplied
slot-order classes.
-/
theorem variabilityAtMost_choiceRuleOfAssignment_of_same_slot_order_borderline_injective
    [Fintype α] {κ : Type*} [DecidableEq κ]
    {w : α → σ → ℝ} {select : Finset α → Assignment α σ} {classOf : σ → κ}
    (hclass : ∀ {s t : σ}, classOf s = classOf t → SameSlotOrder w s t)
    (hkernel :
      ∀ {X : Finset α} {y z : α} {sy sz : σ},
        y ∈ AppliedModelingLib.FiniteChoice.borderlineSet
          (choiceRuleOfAssignment select) X →
        z ∈ AppliedModelingLib.FiniteChoice.borderlineSet
          (choiceRuleOfAssignment select) X →
        (select X).matchSlot sy = some y →
        (select X).matchSlot sz = some z →
        SameSlotOrder w sy sz →
        y = z) :
    AppliedModelingLib.FiniteChoice.VariabilityAtMost
      ((Finset.univ : Finset σ).image classOf).card
      (choiceRuleOfAssignment select) := by
  exact
    variabilityAtMost_choiceRuleOfAssignment_of_borderline_slot_class_injective
      (select := select) (classOf := classOf)
      (fun hy hz hsy hsz hclassEq =>
        hkernel hy hz hsy hsz (hclass hclassEq))

omit [DecidableEq σ] in
/-- Unpack an assignment-induced borderline applicant into a one-insertion loss witness. -/
theorem exists_loss_witness_of_mem_borderlineSet_choiceRuleOfAssignment
    [Fintype α] {select : Finset α → Assignment α σ}
    {X : Finset α} {y : α}
    (hyB : y ∈ AppliedModelingLib.FiniteChoice.borderlineSet
      (choiceRuleOfAssignment select) X) :
    ∃ x,
      y ∈ choiceRuleOfAssignment select X \
        choiceRuleOfAssignment select (insert x X) := by
  classical
  rw [AppliedModelingLib.FiniteChoice.borderlineSet] at hyB
  rcases Finset.mem_biUnion.mp hyB with ⟨x, _hx, hyLoss⟩
  exact ⟨x, hyLoss⟩

/-- The contribution of one slot to the linear assignment objective. -/
def slotValue (w : α → σ → ℝ) (A : Assignment α σ) (s : σ) : ℝ :=
  match A.matchSlot s with
  | none => 0
  | some a => w a s

/-- Linear objective: sum of assigned applicant-slot weights over all slots. -/
def objective (w : α → σ → ℝ) (A : Assignment α σ) : ℝ :=
  ∑ s : σ, slotValue w A s

/--
Global optimality for the finite linear assignment model, among feasible
capacity-filling assignments for the same applicant pool.
-/
def ObjectiveOptimal
    (X : Finset α) (w : α → σ → ℝ) (A : Assignment α σ) : Prop :=
  ∀ B : Assignment α σ,
    Feasible X B → CapacityFilling X B → objective w B ≤ objective w A

/--
Chosen-set uniqueness among globally optimal finite assignments.  This is the
tie-breaking condition needed to turn existence of a preserving optimum into a
specific deterministic choice rule.
-/
def UniqueChosenSetObjectiveOptimal
    (X : Finset α) (w : α → σ → ℝ) (A : Assignment α σ) : Prop :=
  ObjectiveOptimal X w A ∧
    ∀ B : Assignment α σ,
      Feasible X B → CapacityFilling X B →
        ObjectiveOptimal X w B → B.chosenSet = A.chosenSet

/--
An assignment selector returns, for every applicant pool, a feasible,
capacity-filling assignment whose chosen set is the unique globally optimal
chosen set.
-/
def SelectsUniqueGlobalOptima
    (w : α → σ → ℝ) (select : Finset α → Assignment α σ) : Prop :=
  ∀ X, Feasible X (select X) ∧
    CapacityFilling X (select X) ∧
      UniqueChosenSetObjectiveOptimal X w (select X)

/--
Well-posed **operational** LAP weights: every finite applicant pool has a
feasible, capacity-filling optimum with a unique optimal chosen set. The
argument `w` is already the fixed generic refinement used by the operational
choice rule. Thus this predicate does not assert that the unrepresented raw
primary objective has a unique optimum; its uniqueness is only for the
refined objective that resolves raw-primary ties.
-/
def WellPosedObjective (w : α → σ → ℝ) : Prop :=
  ∀ X : Finset α, ∃ A : Assignment α σ,
    Feasible X A ∧ CapacityFilling X A ∧
      UniqueChosenSetObjectiveOptimal X w A

/-- Canonical selected optimum supplied by a well-posed finite LAP. -/
noncomputable def canonicalOptimalAssignment
    (w : α → σ → ℝ) (hwell : WellPosedObjective w)
    (X : Finset α) : Assignment α σ :=
  Classical.choose (hwell X)

/-- The canonical selected assignment has the complete well-posedness specification. -/
theorem canonicalOptimalAssignment_spec
    {w : α → σ → ℝ} (hwell : WellPosedObjective w) (X : Finset α) :
    Feasible X (canonicalOptimalAssignment w hwell X) ∧
      CapacityFilling X (canonicalOptimalAssignment w hwell X) ∧
        UniqueChosenSetObjectiveOptimal X w
          (canonicalOptimalAssignment w hwell X) := by
  exact Classical.choose_spec (hwell X)

/-- The canonical selector really selects unique global optima at every pool. -/
theorem canonicalOptimalAssignment_selectsUniqueGlobalOptima
    {w : α → σ → ℝ} (hwell : WellPosedObjective w) :
    SelectsUniqueGlobalOptima w (canonicalOptimalAssignment w hwell) := by
  intro X
  exact canonicalOptimalAssignment_spec hwell X

omit [DecidableEq σ] in
/-- A selector of unique global optima returns feasible assignments. -/
theorem feasible_of_selectsUniqueGlobalOptima
    {w : α → σ → ℝ} {select : Finset α → Assignment α σ}
    (hselect : SelectsUniqueGlobalOptima w select) (X : Finset α) :
    Feasible X (select X) :=
  (hselect X).1

omit [DecidableEq σ] in
/-- A selector of unique global optima returns capacity-filling assignments. -/
theorem capacityFilling_of_selectsUniqueGlobalOptima
    {w : α → σ → ℝ} {select : Finset α → Assignment α σ}
    (hselect : SelectsUniqueGlobalOptima w select) (X : Finset α) :
    CapacityFilling X (select X) :=
  (hselect X).2.1

omit [DecidableEq σ] in
/-- A selector of unique global optima returns globally optimal assignments. -/
theorem objectiveOptimal_of_selectsUniqueGlobalOptima
    {w : α → σ → ℝ} {select : Finset α → Assignment α σ}
    (hselect : SelectsUniqueGlobalOptima w select) (X : Finset α) :
    ObjectiveOptimal X w (select X) :=
  (hselect X).2.2.1

omit [DecidableEq σ] in
/--
If a selector returns unique global optima, the induced choice rule is
feasible.
-/
theorem feasible_choiceRuleOfAssignment_of_selectsUniqueGlobalOptima
    {w : α → σ → ℝ} {select : Finset α → Assignment α σ}
    (hselect : SelectsUniqueGlobalOptima w select) :
    AppliedModelingLib.FiniteChoice.Feasible (choiceRuleOfAssignment select) :=
  feasible_choiceRuleOfAssignment
    (feasible_of_selectsUniqueGlobalOptima hselect)

omit [DecidableEq σ] in
/--
If a selector returns unique global optima, the induced choice rule is
q-acceptant at capacity equal to the number of slots.
-/
theorem qAcceptant_choiceRuleOfAssignment_of_selectsUniqueGlobalOptima
    {w : α → σ → ℝ} {select : Finset α → Assignment α σ}
    (hselect : SelectsUniqueGlobalOptima w select) :
    AppliedModelingLib.FiniteChoice.QAcceptant
      (Fintype.card σ) (choiceRuleOfAssignment select) :=
  qAcceptant_choiceRuleOfAssignment_of_feasible_of_capacityFilling
    (feasible_of_selectsUniqueGlobalOptima hselect)
    (capacityFilling_of_selectsUniqueGlobalOptima hselect)

/--
Single-addition exchange certificate needed to turn global LAP optimality into
substitutability: if an old applicant `a` is chosen after adding one fresh
applicant `x`, then there is some optimal assignment for the old pool that
still chooses `a`.
-/
def SingleAddOldChosenPreservation
    (w : α → σ → ℝ) (select : Finset α → Assignment α σ) : Prop :=
  ∀ {X : Finset α} {x a : α},
    x ∉ X →
      a ∈ X →
        a ∈ (select (insert x X)).chosenSet →
          ∃ B : Assignment α σ,
            Feasible X B ∧
              CapacityFilling X B ∧
                ObjectiveOptimal X w B ∧
                  a ∈ B.chosenSet

/--
More primitive exchange-repair target: after one fresh insertion, repair the
larger-pool optimum into an old-pool feasible/capacity-filling assignment that
preserves the old chosen applicant and is at least as good as the selected old
optimum. Since the selected old assignment is globally optimal, this repair is
automatically globally optimal too.
-/
def SingleAddExchangeRepair
    (w : α → σ → ℝ) (select : Finset α → Assignment α σ) : Prop :=
  ∀ {X : Finset α} {x a : α},
    x ∉ X →
      a ∈ X →
        a ∈ (select (insert x X)).chosenSet →
          ∃ B : Assignment α σ,
            Feasible X B ∧
              CapacityFilling X B ∧
                objective w (select X) ≤ objective w B ∧
                  a ∈ B.chosenSet

/--
The only nontrivial branch of `SingleAddExchangeRepair`: the fresh applicant is
selected after insertion, and the old applicant under consideration was not
selected before insertion.  The other branches are closed by direct optimality
arguments below.
-/
def SingleAddNewlyChosenExchangeRepair
    (w : α → σ → ℝ) (select : Finset α → Assignment α σ) : Prop :=
  ∀ {X : Finset α} {x a : α},
    x ∉ X →
      a ∈ X →
        a ∈ (select (insert x X)).chosenSet →
          x ∈ (select (insert x X)).chosenSet →
            a ∉ (select X).chosenSet →
              ∃ B : Assignment α σ,
                Feasible X B ∧
                  CapacityFilling X B ∧
                    objective w (select X) ≤ objective w B ∧
                      a ∈ B.chosenSet

omit [DecidableEq σ] in
/-- An at-least-as-good feasible repair of a global optimum is also optimal. -/
theorem objectiveOptimal_of_objectiveOptimal_of_objective_le
    {X : Finset α} {w : α → σ → ℝ} {A B : Assignment α σ}
    (hAopt : ObjectiveOptimal X w A)
    (hAB : objective w A ≤ objective w B) :
    ObjectiveOptimal X w B := by
  intro C hCfeas hCfill
  exact (hAopt C hCfeas hCfill).trans hAB

omit [DecidableEq σ] in
/--
The exchange-repair target implies the preservation certificate using the
old-pool global optimality supplied by the selector.
-/
theorem singleAddOldChosenPreservation_of_selectsUniqueGlobalOptima_of_singleAddExchangeRepair
    {w : α → σ → ℝ} {select : Finset α → Assignment α σ}
    (hselect : SelectsUniqueGlobalOptima w select)
    (hrepair : SingleAddExchangeRepair w select) :
    SingleAddOldChosenPreservation w select := by
  intro X x a hxX haX haLarge
  rcases hrepair hxX haX haLarge with
    ⟨B, hBfeas, hBfill, hBge, haB⟩
  exact ⟨B, hBfeas, hBfill,
    objectiveOptimal_of_objectiveOptimal_of_objective_le
      (objectiveOptimal_of_selectsUniqueGlobalOptima hselect X) hBge,
    haB⟩

omit [DecidableEq σ] in
/--
Under unique chosen-set selection, the single-addition exchange certificate
rules out every one-step gain of a previously rejected old applicant.
-/
theorem no_single_add_gain_of_selectsUniqueGlobalOptima_of_singleAddOldChosenPreservation
    {w : α → σ → ℝ} {select : Finset α → Assignment α σ}
    (hselect : SelectsUniqueGlobalOptima w select)
    (hpreserve : SingleAddOldChosenPreservation w select) :
    ¬ ∃ X x a,
      x ∉ X ∧
        a ∈ X ∧
          a ∈ choiceRuleOfAssignment select (insert x X) ∧
            a ∉ choiceRuleOfAssignment select X := by
  rintro ⟨X, x, a, hxX, haX, haLarge, haSmall⟩
  rcases hpreserve hxX haX (by simpa [choiceRuleOfAssignment] using haLarge) with
    ⟨B, hBfeas, hBfill, hBopt, haB⟩
  have hchosen :
      B.chosenSet = (select X).chosenSet :=
    (hselect X).2.2.2 B hBfeas hBfill hBopt
  exact haSmall (by simpa [choiceRuleOfAssignment, hchosen] using haB)

omit [DecidableEq σ] in
/--
The exact bridge needed for the source theorem: unique global optima plus the
single-addition exchange certificate imply substitutability of the assignment
choice rule.
-/
theorem substitutable_choiceRuleOfAssignment_of_selectsUniqueGlobalOptima_of_singleAddOldChosenPreservation
    {w : α → σ → ℝ} {select : Finset α → Assignment α σ}
    (hselect : SelectsUniqueGlobalOptima w select)
    (hpreserve : SingleAddOldChosenPreservation w select) :
    AppliedModelingLib.FiniteChoice.Substitutable (choiceRuleOfAssignment select) := by
  exact AppliedModelingLib.FiniteChoice.substitutable_of_no_single_add_gain
    (choiceRuleOfAssignment select)
    (no_single_add_gain_of_selectsUniqueGlobalOptima_of_singleAddOldChosenPreservation
      hselect hpreserve)

omit [DecidableEq σ] in
/--
Consequently, the existing finite-choice theorem closes the paper's
`1`-instability statement once the single-addition LAP exchange certificate is
proved.
-/
theorem dUnstable_one_choiceRuleOfAssignment_of_selectsUniqueGlobalOptima_of_singleAddOldChosenPreservation
    {w : α → σ → ℝ} {select : Finset α → Assignment α σ}
    (hselect : SelectsUniqueGlobalOptima w select)
    (hpreserve : SingleAddOldChosenPreservation w select) :
    AppliedModelingLib.FiniteChoice.DUnstable 1 (choiceRuleOfAssignment select) := by
  exact AppliedModelingLib.FiniteChoice.dUnstable_one_of_feasible_of_qAcceptant_of_substitutable
    (feasible_choiceRuleOfAssignment_of_selectsUniqueGlobalOptima hselect)
    (qAcceptant_choiceRuleOfAssignment_of_selectsUniqueGlobalOptima hselect)
    (substitutable_choiceRuleOfAssignment_of_selectsUniqueGlobalOptima_of_singleAddOldChosenPreservation
      hselect hpreserve)

omit [DecidableEq σ] in
/--
Same source-theorem bridge, stated against the lower-level exchange-repair
lemma that should be proved by an alternating-path/matching argument.
-/
theorem dUnstable_one_choiceRuleOfAssignment_of_selectsUniqueGlobalOptima_of_singleAddExchangeRepair
    {w : α → σ → ℝ} {select : Finset α → Assignment α σ}
    (hselect : SelectsUniqueGlobalOptima w select)
    (hrepair : SingleAddExchangeRepair w select) :
    AppliedModelingLib.FiniteChoice.DUnstable 1 (choiceRuleOfAssignment select) := by
  exact
    dUnstable_one_choiceRuleOfAssignment_of_selectsUniqueGlobalOptima_of_singleAddOldChosenPreservation
      hselect
      (singleAddOldChosenPreservation_of_selectsUniqueGlobalOptima_of_singleAddExchangeRepair
        hselect hrepair)

omit [DecidableEq σ] [Fintype σ] in
/-- Feasibility is monotone when the applicant pool is enlarged by one applicant. -/
theorem feasible_insert_of_feasible
    {X : Finset α} {x : α} {A : Assignment α σ}
    (hfeas : Feasible X A) :
    Feasible (insert x X) A := by
  constructor
  · intro s a hslot
    exact Finset.mem_insert.mpr (Or.inr (hfeas.1 hslot))
  · exact hfeas.2

omit [DecidableEq σ] in
/--
If an assignment feasible for `insert x X` does not actually assign `x`, then
its chosen set is contained in the old pool `X`.
-/
theorem chosenSet_subset_of_feasible_insert_of_not_mem_chosenSet
    {X : Finset α} {x : α} {A : Assignment α σ}
    (hfeas : Feasible (insert x X) A)
    (hx : x ∉ A.chosenSet) :
    A.chosenSet ⊆ X := by
  intro a ha
  have hainsert : a ∈ insert x X := chosenSet_subset_of_feasible hfeas ha
  rcases Finset.mem_insert.mp hainsert with rfl | haX
  · exact (hx ha).elim
  · exact haX

omit [DecidableEq σ] in
/--
If an assignment capacity-fills `insert x X` and does not choose the fresh
applicant, then it also capacity-fills the old pool.
-/
theorem capacityFilling_of_insert_not_mem_chosenSet
    {X : Finset α} {x : α} {A : Assignment α σ}
    (hxX : x ∉ X)
    (hfeas : Feasible (insert x X) A)
    (hfill : CapacityFilling (insert x X) A)
    (hx : x ∉ A.chosenSet) :
    CapacityFilling X A := by
  classical
  constructor
  · intro hsmall
    by_cases hlt : X.card < Fintype.card σ
    · have hinsert_le : (insert x X).card ≤ Fintype.card σ := by
        rw [Finset.card_insert_of_notMem hxX]
        omega
      intro a haX
      exact hfill.1 hinsert_le (Finset.mem_insert.mpr (Or.inr haX))
    · have hq_le_X : Fintype.card σ ≤ X.card := by omega
      have hcardA :
          A.chosenSet.card = Fintype.card σ :=
        chosenSet_card_eq_slots_of_noDuplicate_of_fillsSlots
          hfeas.2 ((hfill.2 (by
            rw [Finset.card_insert_of_notMem hxX]
            omega)))
      have hsubset : A.chosenSet ⊆ X :=
        chosenSet_subset_of_feasible_insert_of_not_mem_chosenSet hfeas hx
      have hX_card : X.card = Fintype.card σ := le_antisymm hsmall hq_le_X
      have hEq : A.chosenSet = X :=
        Finset.eq_of_subset_of_card_le hsubset (by
          rw [hcardA, hX_card])
      intro a haX
      simpa [hEq]
  · intro hlarge s
    exact hfill.2 (by
      rw [Finset.card_insert_of_notMem hxX]
      omega) s

omit [DecidableEq σ] in
/--
At or above slot capacity, capacity filling is also monotone under inserting a
fresh applicant because both old and enlarged pools only require all slots to
be occupied.
-/
theorem capacityFilling_insert_of_capacityFilling_of_large
    {X : Finset α} {x : α} {A : Assignment α σ}
    (hxX : x ∉ X)
    (hlarge : Fintype.card σ ≤ X.card)
    (hfill : CapacityFilling X A) :
    CapacityFilling (insert x X) A := by
  classical
  constructor
  · intro hsmall
    have hcard : (insert x X).card = X.card + 1 :=
      Finset.card_insert_of_notMem hxX
    omega
  · intro _ s
    exact hfill.2 hlarge s

omit [DecidableEq σ] in
/--
Easy branch of the single-addition LAP exchange proof: if the fresh applicant
is not selected after insertion, the enlarged-pool optimum itself is a valid
old-pool repair.
-/
theorem singleAddExchangeRepair_case_new_not_chosen
    {w : α → σ → ℝ} {select : Finset α → Assignment α σ}
    (hselect : SelectsUniqueGlobalOptima w select)
    {X : Finset α} {x a : α}
    (hxX : x ∉ X)
    (_haX : a ∈ X)
    (haLarge : a ∈ (select (insert x X)).chosenSet)
    (hxLarge : x ∉ (select (insert x X)).chosenSet) :
    ∃ B : Assignment α σ,
      Feasible X B ∧
        CapacityFilling X B ∧
          objective w (select X) ≤ objective w B ∧
            a ∈ B.chosenSet := by
  classical
  let B := select (insert x X)
  have hBfeasLarge : Feasible (insert x X) B :=
    feasible_of_selectsUniqueGlobalOptima hselect (insert x X)
  have hBfillLarge : CapacityFilling (insert x X) B :=
    capacityFilling_of_selectsUniqueGlobalOptima hselect (insert x X)
  have hBfeas : Feasible X B := by
    constructor
    · intro s b hslot
      have hbChosen : b ∈ B.chosenSet :=
        mem_chosenSet.mpr ⟨s, hslot⟩
      exact chosenSet_subset_of_feasible_insert_of_not_mem_chosenSet
        hBfeasLarge hxLarge hbChosen
    · exact hBfeasLarge.2
  have hBfill : CapacityFilling X B :=
    capacityFilling_of_insert_not_mem_chosenSet hxX hBfeasLarge hBfillLarge hxLarge
  have hlargeX : Fintype.card σ ≤ X.card := by
    by_contra hnot
    have hlt : X.card < Fintype.card σ := Nat.lt_of_not_ge hnot
    have hinsert_le : (insert x X).card ≤ Fintype.card σ := by
      rw [Finset.card_insert_of_notMem hxX]
      omega
    have hxChosen : x ∈ B.chosenSet :=
      hBfillLarge.1 hinsert_le (Finset.mem_insert_self x X)
    exact hxLarge hxChosen
  have hAfeasLarge : Feasible (insert x X) (select X) :=
    feasible_insert_of_feasible
      (feasible_of_selectsUniqueGlobalOptima hselect X)
  have hAfillLarge : CapacityFilling (insert x X) (select X) :=
    capacityFilling_insert_of_capacityFilling_of_large hxX hlargeX
      (capacityFilling_of_selectsUniqueGlobalOptima hselect X)
  have hle : objective w (select X) ≤ objective w B :=
    objectiveOptimal_of_selectsUniqueGlobalOptima hselect (insert x X)
      (select X) hAfeasLarge hAfillLarge
  exact ⟨B, hBfeas, hBfill, hle, haLarge⟩

omit [DecidableEq σ] in
/--
Trivial branch of the single-addition exchange proof: if the old applicant was
already chosen before insertion, the selected old-pool optimum is itself the
repair.
-/
theorem singleAddExchangeRepair_case_already_chosen
    {w : α → σ → ℝ} {select : Finset α → Assignment α σ}
    (hselect : SelectsUniqueGlobalOptima w select)
    {X : Finset α} {a : α}
    (haSmall : a ∈ (select X).chosenSet) :
    ∃ B : Assignment α σ,
      Feasible X B ∧
        CapacityFilling X B ∧
          objective w (select X) ≤ objective w B ∧
            a ∈ B.chosenSet := by
  exact ⟨select X,
    feasible_of_selectsUniqueGlobalOptima hselect X,
    capacityFilling_of_selectsUniqueGlobalOptima hselect X,
    le_rfl,
    haSmall⟩

omit [DecidableEq σ] in
/--
The selected-new/newly-chosen branch is the only remaining case needed for the
full single-addition exchange-repair certificate.
-/
theorem singleAddExchangeRepair_of_selectsUniqueGlobalOptima_of_newlyChosenExchangeRepair
    {w : α → σ → ℝ} {select : Finset α → Assignment α σ}
    (hselect : SelectsUniqueGlobalOptima w select)
    (hnew : SingleAddNewlyChosenExchangeRepair w select) :
    SingleAddExchangeRepair w select := by
  intro X x a hxX haX haLarge
  by_cases haSmall : a ∈ (select X).chosenSet
  · exact singleAddExchangeRepair_case_already_chosen hselect haSmall
  · by_cases hxLarge : x ∈ (select (insert x X)).chosenSet
    · exact hnew hxX haX haLarge hxLarge haSmall
    · exact singleAddExchangeRepair_case_new_not_chosen
        hselect hxX haX haLarge hxLarge

/--
Slots are linked across two assignments when the applicant occupying one slot
in one assignment occupies the other slot in the other assignment.  This is the
slot-side graph underlying the alternating-path exchange proof.
-/
def slotLinked (A B : Assignment α σ) (s t : σ) : Prop :=
  (∃ a, A.matchSlot s = some a ∧ B.matchSlot t = some a) ∨
    (∃ a, B.matchSlot s = some a ∧ A.matchSlot t = some a)

omit [DecidableEq α] [DecidableEq σ] [Fintype σ] in
/-- The slot-link relation is symmetric. -/
theorem slotLinked_symm (A B : Assignment α σ) :
    Symmetric (slotLinked A B) := by
  intro s t h
  rcases h with ⟨a, hAs, hBt⟩ | ⟨a, hBs, hAt⟩
  · exact Or.inr ⟨a, hBt, hAs⟩
  · exact Or.inl ⟨a, hAt, hBs⟩

/-- The finite connected component of a slot in the slot-link graph. -/
noncomputable def slotComponent (A B : Assignment α σ) (root : σ) : Finset σ := by
  classical
  exact Finset.univ.filter fun s =>
    Relation.ReflTransGen (slotLinked A B) root s

omit [DecidableEq α] [DecidableEq σ] in
/-- The root belongs to its own slot-link component. -/
theorem mem_slotComponent_self (A B : Assignment α σ) (root : σ) :
    root ∈ slotComponent A B root := by
  classical
  rw [slotComponent]
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ root, Relation.ReflTransGen.refl⟩

omit [DecidableEq α] [DecidableEq σ] in
/-- Slot-link components are closed under one slot-link step. -/
theorem mem_slotComponent_of_mem_of_slotLinked
    {A B : Assignment α σ} {root s t : σ}
    (hs : s ∈ slotComponent A B root)
    (hst : slotLinked A B s t) :
    t ∈ slotComponent A B root := by
  classical
  rw [slotComponent] at hs
  rcases Finset.mem_filter.mp hs with ⟨_, hreach⟩
  rw [slotComponent]
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ t, Relation.ReflTransGen.tail hreach hst⟩

omit [DecidableEq α] [DecidableEq σ] in
/-- If an old-assignment occupant of a component slot is assigned by the new assignment, that new slot is in the component. -/
theorem mem_slotComponent_of_old_to_new
    {A B : Assignment α σ} {root s t : σ} {a : α}
    (hs : s ∈ slotComponent A B root)
    (hAs : A.matchSlot s = some a)
    (hBt : B.matchSlot t = some a) :
    t ∈ slotComponent A B root :=
  mem_slotComponent_of_mem_of_slotLinked hs (Or.inl ⟨a, hAs, hBt⟩)

omit [DecidableEq α] [DecidableEq σ] in
/-- If a new-assignment occupant of a component slot is assigned by the old assignment, that old slot is in the component. -/
theorem mem_slotComponent_of_new_to_old
    {A B : Assignment α σ} {root s t : σ} {a : α}
    (hs : s ∈ slotComponent A B root)
    (hBs : B.matchSlot s = some a)
    (hAt : A.matchSlot t = some a) :
    t ∈ slotComponent A B root :=
  mem_slotComponent_of_mem_of_slotLinked hs (Or.inr ⟨a, hBs, hAt⟩)

omit [DecidableEq α] [DecidableEq σ] [Fintype σ] in
/-- Swapping the two assignments does not change the slot-link relation. -/
theorem slotLinked_swap_assignments_iff
    (A B : Assignment α σ) (s t : σ) :
    slotLinked B A s t ↔ slotLinked A B s t := by
  constructor
  · intro h
    rcases h with ⟨a, hBs, hAt⟩ | ⟨a, hAs, hBt⟩
    · exact Or.inr ⟨a, hBs, hAt⟩
    · exact Or.inl ⟨a, hAs, hBt⟩
  · intro h
    rcases h with ⟨a, hAs, hBt⟩ | ⟨a, hBs, hAt⟩
    · exact Or.inr ⟨a, hAs, hBt⟩
    · exact Or.inl ⟨a, hBs, hAt⟩

omit [DecidableEq α] [DecidableEq σ] in
/-- Swapping the two assignments does not change a slot-link component. -/
theorem slotComponent_swap_assignments
    (A B : Assignment α σ) (root : σ) :
    slotComponent B A root = slotComponent A B root := by
  classical
  ext s
  constructor
  · intro hs
    rw [slotComponent] at hs
    rcases Finset.mem_filter.mp hs with ⟨_, hreach⟩
    rw [slotComponent]
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ s,
        Relation.ReflTransGen.mono
          (fun u v huv => (slotLinked_swap_assignments_iff A B u v).mp huv)
          hreach⟩
  · intro hs
    rw [slotComponent] at hs
    rcases Finset.mem_filter.mp hs with ⟨_, hreach⟩
    rw [slotComponent]
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ s,
        Relation.ReflTransGen.mono
          (fun u v huv => (slotLinked_swap_assignments_iff A B u v).mpr huv)
          hreach⟩

/--
Splice two assignments on a finite slot set: use `B` on slots in `R`, and `A`
elsewhere.
-/
def spliceSlots (A B : Assignment α σ) (R : Finset σ) : Assignment α σ where
  matchSlot s := if s ∈ R then B.matchSlot s else A.matchSlot s

omit [DecidableEq α] [Fintype σ] in
theorem spliceSlots_matchSlot_of_mem
    {A B : Assignment α σ} {R : Finset σ} {s : σ}
    (hs : s ∈ R) :
    (spliceSlots A B R).matchSlot s = B.matchSlot s := by
  simp [spliceSlots, hs]

omit [DecidableEq α] [Fintype σ] in
theorem spliceSlots_matchSlot_of_not_mem
    {A B : Assignment α σ} {R : Finset σ} {s : σ}
    (hs : s ∉ R) :
    (spliceSlots A B R).matchSlot s = A.matchSlot s := by
  simp [spliceSlots, hs]

omit [DecidableEq α] in
/--
Splicing on a whole slot-link component preserves the no-duplicate condition:
any cross-boundary duplicate would itself be a slot-link edge, forcing the
outside slot into the component.
-/
theorem noDuplicateApplicants_spliceSlots_slotComponent
    {A B : Assignment α σ}
    (hAdup : NoDuplicateApplicants A)
    (hBdup : NoDuplicateApplicants B)
    (root : σ) :
    NoDuplicateApplicants (spliceSlots A B (slotComponent A B root)) := by
  classical
  intro s t a hs ht
  by_cases hsR : s ∈ slotComponent A B root
  · have hsB : B.matchSlot s = some a := by
      simpa [spliceSlots, hsR] using hs
    by_cases htR : t ∈ slotComponent A B root
    · have htB : B.matchSlot t = some a := by
        simpa [spliceSlots, htR] using ht
      exact hBdup hsB htB
    · have htA : A.matchSlot t = some a := by
        simpa [spliceSlots, htR] using ht
      have htR' : t ∈ slotComponent A B root :=
        mem_slotComponent_of_new_to_old hsR hsB htA
      exact (htR htR').elim
  · have hsA : A.matchSlot s = some a := by
      simpa [spliceSlots, hsR] using hs
    by_cases htR : t ∈ slotComponent A B root
    · have htB : B.matchSlot t = some a := by
        simpa [spliceSlots, htR] using ht
      have hsR' : s ∈ slotComponent A B root :=
        mem_slotComponent_of_new_to_old htR htB hsA
      exact (hsR hsR').elim
    · have htA : A.matchSlot t = some a := by
        simpa [spliceSlots, htR] using ht
      exact hAdup hsA htA

omit [DecidableEq α] in
/-- Assigned-from preservation for a component splice. -/
theorem assignedFrom_spliceSlots_slotComponent
    {X : Finset α} {A B : Assignment α σ} {root : σ}
    (hAfrom : AssignedFrom X A)
    (hBfrom :
      ∀ {s a}, s ∈ slotComponent A B root → B.matchSlot s = some a → a ∈ X) :
    AssignedFrom X (spliceSlots A B (slotComponent A B root)) := by
  classical
  intro s a hslot
  by_cases hsR : s ∈ slotComponent A B root
  · exact hBfrom hsR (by simpa [spliceSlots, hsR] using hslot)
  · exact hAfrom (by simpa [spliceSlots, hsR] using hslot)

omit [DecidableEq α] in
/-- Feasibility preservation for a component splice. -/
theorem feasible_spliceSlots_slotComponent
    {X : Finset α} {A B : Assignment α σ} {root : σ}
    (hAfeas : Feasible X A)
    (hBdup : NoDuplicateApplicants B)
    (hBfrom :
      ∀ {s a}, s ∈ slotComponent A B root → B.matchSlot s = some a → a ∈ X) :
    Feasible X (spliceSlots A B (slotComponent A B root)) :=
  ⟨assignedFrom_spliceSlots_slotComponent hAfeas.1 hBfrom,
    noDuplicateApplicants_spliceSlots_slotComponent hAfeas.2 hBdup root⟩

/--
Forward feasibility for the exchange proof: if the `B`-component being spliced
into the old assignment does not assign the fresh applicant, then every spliced
applicant still belongs to the old pool.
-/
theorem feasible_forward_spliceSlots_slotComponent_of_not_fresh
    {X : Finset α} {x : α} {A B : Assignment α σ} {root : σ}
    (hAfeas : Feasible X A)
    (hBfeas : Feasible (insert x X) B)
    (hxComp :
      ∀ {s}, s ∈ slotComponent A B root → B.matchSlot s ≠ some x) :
    Feasible X (spliceSlots A B (slotComponent A B root)) := by
  classical
  refine feasible_spliceSlots_slotComponent hAfeas hBfeas.2 ?_
  intro s a hs hslot
  have haInsert : a ∈ insert x X := hBfeas.1 hslot
  rcases Finset.mem_insert.mp haInsert with rfl | haX
  · exact (hxComp hs hslot).elim
  · exact haX

/-- Reverse feasibility for the exchange proof, splicing the old component back into the enlarged assignment. -/
theorem feasible_reverse_spliceSlots_slotComponent_insert
    {X : Finset α} {x : α} {A B : Assignment α σ} {root : σ}
    (hAfeas : Feasible X A)
    (hBfeas : Feasible (insert x X) B) :
    Feasible (insert x X) (spliceSlots B A (slotComponent A B root)) := by
  classical
  have h :
      Feasible (insert x X) (spliceSlots B A (slotComponent B A root)) := by
    refine feasible_spliceSlots_slotComponent hBfeas hAfeas.2 ?_
    intro s a _hs hslot
    exact Finset.mem_insert.mpr (Or.inr (hAfeas.1 hslot))
  simpa [slotComponent_swap_assignments] using h

omit [DecidableEq α] [Fintype σ] in
/-- If both assignments fill every slot, their slot splice fills every slot. -/
theorem fillsSlots_spliceSlots
    {A B : Assignment α σ} {R : Finset σ}
    (hAfill : ∀ s, ∃ a, A.matchSlot s = some a)
    (hBfill : ∀ s, ∃ a, B.matchSlot s = some a) :
    ∀ s, ∃ a, (spliceSlots A B R).matchSlot s = some a := by
  intro s
  by_cases hsR : s ∈ R
  · rcases hBfill s with ⟨a, ha⟩
    exact ⟨a, by simpa [spliceSlots, hsR] using ha⟩
  · rcases hAfill s with ⟨a, ha⟩
    exact ⟨a, by simpa [spliceSlots, hsR] using ha⟩

omit [DecidableEq σ] in
/--
A feasible assignment that fills every slot capacity-fills every large enough
pool; the small-pool branch is forced by cardinal equality.
-/
theorem capacityFilling_of_feasible_of_fillsSlots_of_large
    {X : Finset α} {A : Assignment α σ}
    (hfeas : Feasible X A)
    (hfillSlots : ∀ s, ∃ a, A.matchSlot s = some a)
    (hlarge : Fintype.card σ ≤ X.card) :
    CapacityFilling X A := by
  constructor
  · intro hsmall
    have hcardA :
        A.chosenSet.card = Fintype.card σ :=
      chosenSet_card_eq_slots_of_noDuplicate_of_fillsSlots hfeas.2 hfillSlots
    have hX_card : X.card = Fintype.card σ := le_antisymm hsmall hlarge
    have hEq : A.chosenSet = X :=
      Finset.eq_of_subset_of_card_le
        (chosenSet_subset_of_feasible hfeas) (by
          rw [hcardA, hX_card])
    intro a haX
    simpa [hEq]
  · intro _ s
    exact hfillSlots s

/-- Capacity filling preservation for a component splice at or above slot capacity. -/
theorem capacityFilling_spliceSlots_slotComponent_of_large
    {X : Finset α} {A B : Assignment α σ} {root : σ}
    (hspliceFeas : Feasible X (spliceSlots A B (slotComponent A B root)))
    (hAfillSlots : ∀ s, ∃ a, A.matchSlot s = some a)
    (hBfillSlots : ∀ s, ∃ a, B.matchSlot s = some a)
    (hlarge : Fintype.card σ ≤ X.card) :
    CapacityFilling X (spliceSlots A B (slotComponent A B root)) :=
  capacityFilling_of_feasible_of_fillsSlots_of_large hspliceFeas
    (fillsSlots_spliceSlots hAfillSlots hBfillSlots) hlarge

/-- Forward capacity filling for a component splice at or above old-pool capacity. -/
theorem capacityFilling_forward_spliceSlots_slotComponent_of_large
    {X : Finset α} {x : α} {A B : Assignment α σ} {root : σ}
    (hxX : x ∉ X)
    (hspliceFeas : Feasible X (spliceSlots A B (slotComponent A B root)))
    (hAfill : CapacityFilling X A)
    (hBfill : CapacityFilling (insert x X) B)
    (hlarge : Fintype.card σ ≤ X.card) :
    CapacityFilling X (spliceSlots A B (slotComponent A B root)) := by
  classical
  exact capacityFilling_spliceSlots_slotComponent_of_large
    hspliceFeas
    (hAfill.2 hlarge)
    (hBfill.2 (by
      rw [Finset.card_insert_of_notMem hxX]
      omega))
    hlarge

/-- Reverse capacity filling for splicing the old component back into the enlarged assignment. -/
theorem capacityFilling_reverse_spliceSlots_slotComponent_insert_of_large
    {X : Finset α} {x : α} {A B : Assignment α σ} {root : σ}
    (hxX : x ∉ X)
    (hspliceFeas :
      Feasible (insert x X) (spliceSlots B A (slotComponent A B root)))
    (hAfill : CapacityFilling X A)
    (hBfill : CapacityFilling (insert x X) B)
    (hlarge : Fintype.card σ ≤ X.card) :
    CapacityFilling (insert x X) (spliceSlots B A (slotComponent A B root)) := by
  classical
  have h :
      CapacityFilling (insert x X) (spliceSlots B A (slotComponent B A root)) := by
    refine capacityFilling_spliceSlots_slotComponent_of_large
      (by simpa [slotComponent_swap_assignments] using hspliceFeas)
      (hBfill.2 (by
        rw [Finset.card_insert_of_notMem hxX]
        omega))
      (hAfill.2 hlarge)
      ?_
    rw [Finset.card_insert_of_notMem hxX]
    omega
  simpa [slotComponent_swap_assignments] using h

omit [DecidableEq α] [Fintype σ] in
/--
At each slot, the two complementary splices have the same total contribution as
the two original assignments.
-/
theorem slotValue_spliceSlots_add_slotValue_spliceSlots
    {w : α → σ → ℝ} {A B : Assignment α σ} {R : Finset σ} (s : σ) :
    slotValue w (spliceSlots A B R) s +
        slotValue w (spliceSlots B A R) s =
      slotValue w A s + slotValue w B s := by
  by_cases hs : s ∈ R
  · simp [slotValue, spliceSlots, hs, add_comm]
  · simp [slotValue, spliceSlots, hs]

omit [DecidableEq α] in
/--
Objective accounting for complementary slot splices.
-/
theorem objective_spliceSlots_add_objective_spliceSlots
    {w : α → σ → ℝ} {A B : Assignment α σ} {R : Finset σ} :
    objective w (spliceSlots A B R) +
        objective w (spliceSlots B A R) =
      objective w A + objective w B := by
  unfold objective
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun s _ =>
    slotValue_spliceSlots_add_slotValue_spliceSlots (w := w) (A := A) (B := B)
      (R := R) s

omit [DecidableEq α] in
/--
If reverting the same component in `B` back to `A` is no better than `B`, then
the forward splice from `A` to `B` is at least as good as `A`.
-/
theorem objective_le_spliceSlots_of_reverse_splice_le
    {w : α → σ → ℝ} {A B : Assignment α σ} {R : Finset σ}
    (hle :
      objective w (spliceSlots B A R) ≤ objective w B) :
    objective w A ≤ objective w (spliceSlots A B R) := by
  have hsum :=
    objective_spliceSlots_add_objective_spliceSlots
      (w := w) (A := A) (B := B) (R := R)
  have hplus :
      objective w A + objective w B ≤
        objective w (spliceSlots A B R) + objective w B := by
    rw [← hsum]
    simpa [add_comm, add_left_comm, add_assoc] using
      add_le_add_left hle (objective w (spliceSlots A B R))
  exact (add_le_add_iff_right (objective w B)).mp hplus

/--
Core component-exchange repair lemma.  If the slot-link component rooted at a
`B`-slot for old applicant `a` does not contain the fresh applicant, then
splicing that component into the old assignment gives an old-pool feasible
capacity-filling assignment that preserves `a` and is at least as good as the
old assignment.
-/
theorem exchangeRepair_of_component_not_fresh
    {X : Finset α} {x a : α} {w : α → σ → ℝ} {A B : Assignment α σ}
    {root : σ}
    (hxX : x ∉ X)
    (hAfeas : Feasible X A)
    (hAfill : CapacityFilling X A)
    (hBfeas : Feasible (insert x X) B)
    (hBfill : CapacityFilling (insert x X) B)
    (hBopt : ObjectiveOptimal (insert x X) w B)
    (hlarge : Fintype.card σ ≤ X.card)
    (hroot : B.matchSlot root = some a)
    (hxComp :
      ∀ {s}, s ∈ slotComponent A B root → B.matchSlot s ≠ some x) :
    ∃ C : Assignment α σ,
      Feasible X C ∧
        CapacityFilling X C ∧
          objective w A ≤ objective w C ∧
            a ∈ C.chosenSet := by
  classical
  let C := spliceSlots A B (slotComponent A B root)
  let D := spliceSlots B A (slotComponent A B root)
  have hCfeas : Feasible X C :=
    feasible_forward_spliceSlots_slotComponent_of_not_fresh
      hAfeas hBfeas hxComp
  have hCfill : CapacityFilling X C :=
    capacityFilling_forward_spliceSlots_slotComponent_of_large
      hxX hCfeas hAfill hBfill hlarge
  have hDfeas : Feasible (insert x X) D :=
    feasible_reverse_spliceSlots_slotComponent_insert hAfeas hBfeas
  have hDfill : CapacityFilling (insert x X) D :=
    capacityFilling_reverse_spliceSlots_slotComponent_insert_of_large
      hxX hDfeas hAfill hBfill hlarge
  have hDle : objective w D ≤ objective w B :=
    hBopt D hDfeas hDfill
  have hAleC : objective w A ≤ objective w C :=
    objective_le_spliceSlots_of_reverse_splice_le
      (w := w) (A := A) (B := B) (R := slotComponent A B root) hDle
  have hrootMem : root ∈ slotComponent A B root :=
    mem_slotComponent_self A B root
  have haC : a ∈ C.chosenSet := by
    rw [mem_chosenSet]
    exact ⟨root, by
      simpa [C, spliceSlots, hrootMem] using hroot⟩
  exact ⟨C, hCfeas, hCfill, hAleC, haC⟩

/--
Directed alternating slot edge: follow the applicant in slot `s` of `A` to the
slot where the same applicant appears in `B`.
-/
def forwardSlotLinked (A B : Assignment α σ) (s t : σ) : Prop :=
  ∃ y, A.matchSlot s = some y ∧ B.matchSlot t = some y

omit [DecidableEq α] [DecidableEq σ] [Fintype σ] in
/--
The directed alternating slot edge is right-unique when the target assignment
has no duplicate applicants.
-/
theorem forwardSlotLinked_rightUnique_of_noDuplicate
    {A B : Assignment α σ}
    (hBdup : NoDuplicateApplicants B) :
    Relator.RightUnique (forwardSlotLinked A B) := by
  intro s t u hst hsu
  rcases hst with ⟨a, hAs, hBt⟩
  rcases hsu with ⟨b, hAs', hBu⟩
  have hab : a = b := Option.some.inj (hAs.symm.trans hAs')
  exact hBdup (by simpa [hab] using hBt) hBu

omit [DecidableEq α] [DecidableEq σ] [Fintype σ] in
/--
The directed alternating slot edge is left-unique when the source assignment
has no duplicate applicants.
-/
theorem forwardSlotLinked_leftUnique_of_noDuplicate
    {A B : Assignment α σ}
    (hAdup : NoDuplicateApplicants A) :
    Relator.LeftUnique (forwardSlotLinked A B) := by
  intro s t u hsu htu
  rcases hsu with ⟨a, hAs, hBu⟩
  rcases htu with ⟨b, hAt, hBu'⟩
  have hab : a = b := Option.some.inj (hBu.symm.trans hBu')
  exact hAdup (by simpa [hab] using hAs) hAt

omit [DecidableEq α] [DecidableEq σ] [Fintype σ] in
/--
In a directed alternating graph with unique predecessors and no incoming edge
to the root, a reachable slot's successor cannot reach back to that slot.
-/
theorem not_forward_reaches_back_of_reachable_of_root_no_incoming
    {A B : Assignment α σ} {root s t : σ}
    (hAdup : NoDuplicateApplicants A)
    (hrootNoIn : ¬ ∃ p, forwardSlotLinked A B p root)
    (hroot_s :
      Relation.ReflTransGen (forwardSlotLinked A B) root s)
    (hst : forwardSlotLinked A B s t) :
    ¬ Relation.ReflTransGen (forwardSlotLinked A B) t s := by
  revert t
  induction hroot_s with
  | refl =>
      intro t hroot_t ht_root
      rcases Relation.ReflTransGen.cases_tail ht_root with ht_eq | ⟨p, _htp, hp_root⟩
      · subst ht_eq
        exact hrootNoIn ⟨root, hroot_t⟩
      · exact hrootNoIn ⟨p, hp_root⟩
  | @tail p s hroot_p hp_s ih =>
      intro t hs_t ht_s
      have hleft := forwardSlotLinked_leftUnique_of_noDuplicate (A := A) (B := B) hAdup
      have hs_p : Relation.ReflTransGen (forwardSlotLinked A B) s p := by
        rcases Relation.ReflTransGen.cases_tail ht_s with ht_eq | ⟨q, htq, hq_s⟩
        · subst ht_eq
          have hp_eq_s : p = s := hleft (a := p) (b := s) (c := s) hp_s hs_t
          rw [hp_eq_s]
        · have hq_eq_p : q = p := (hleft (a := p) (b := q) (c := s) hp_s hq_s).symm
          exact Relation.ReflTransGen.head hs_t (by simpa [hq_eq_p] using htq)
      exact ih hp_s hs_p

/-- Directed alternating reachability from a root slot. -/
noncomputable def forwardSlotReachSet (A B : Assignment α σ) (root : σ) : Finset σ := by
  classical
  exact Finset.univ.filter fun s =>
    Relation.ReflTransGen (forwardSlotLinked A B) root s

omit [DecidableEq α] [DecidableEq σ] in
/-- The root belongs to its directed alternating reachability set. -/
theorem mem_forwardSlotReachSet_self (A B : Assignment α σ) (root : σ) :
    root ∈ forwardSlotReachSet A B root := by
  classical
  rw [forwardSlotReachSet]
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ root, Relation.ReflTransGen.refl⟩

omit [DecidableEq α] [DecidableEq σ] in
/-- Directed alternating reachability is closed under one forward edge. -/
theorem mem_forwardSlotReachSet_of_mem_of_forwardSlotLinked
    {A B : Assignment α σ} {root s t : σ}
    (hs : s ∈ forwardSlotReachSet A B root)
    (hst : forwardSlotLinked A B s t) :
    t ∈ forwardSlotReachSet A B root := by
  classical
  rw [forwardSlotReachSet] at hs
  rcases Finset.mem_filter.mp hs with ⟨_, hreach⟩
  rw [forwardSlotReachSet]
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ t, Relation.ReflTransGen.tail hreach hst⟩

omit [DecidableEq α] [DecidableEq σ] in
/--
In a right-unique directed alternating graph, any two slots reachable from the
same root are comparable along the directed reachability relation.
-/
theorem forward_reaches_or_reached_by_of_mem_forwardSlotReachSet
    {A B : Assignment α σ} {root s t : σ}
    (hBdup : NoDuplicateApplicants B)
    (hs : s ∈ forwardSlotReachSet A B root)
    (ht : t ∈ forwardSlotReachSet A B root) :
    Relation.ReflTransGen (forwardSlotLinked A B) s t ∨
      Relation.ReflTransGen (forwardSlotLinked A B) t s := by
  classical
  rw [forwardSlotReachSet] at hs ht
  rcases Finset.mem_filter.mp hs with ⟨_, hsreach⟩
  rcases Finset.mem_filter.mp ht with ⟨_, htreach⟩
  exact Relation.ReflTransGen.total_of_right_unique
    (forwardSlotLinked_rightUnique_of_noDuplicate hBdup)
    hsreach htreach

omit [DecidableEq α] in
/--
If a reachable target has no outgoing directed alternating edge, then every
slot reachable from the same root reaches that terminal target.
-/
theorem forward_reaches_terminal_of_mem_forwardSlotReachSet
    {A B : Assignment α σ} {root s terminal : σ}
    (hBdup : NoDuplicateApplicants B)
    (hs : s ∈ forwardSlotReachSet A B root)
    (hterminal : terminal ∈ forwardSlotReachSet A B root)
    (hterminal_no_edge :
      ¬ ∃ t, forwardSlotLinked A B terminal t) :
    Relation.ReflTransGen (forwardSlotLinked A B) s terminal := by
  rcases forward_reaches_or_reached_by_of_mem_forwardSlotReachSet
      hBdup hs hterminal with hst | hts
  · exact hst
  · rcases Relation.ReflTransGen.cases_head hts with hsame | ⟨u, hedge, _hrest⟩
    · subst hsame
      exact Relation.ReflTransGen.refl
    · exact False.elim (hterminal_no_edge ⟨u, hedge⟩)

omit [DecidableEq α] [DecidableEq σ] in
/--
Every non-root slot in the directed alternating reachability set has an
incoming forward edge from another reachable slot.
-/
theorem exists_forward_predecessor_of_mem_forwardSlotReachSet_of_ne
    {A B : Assignment α σ} {root s : σ}
    (hs : s ∈ forwardSlotReachSet A B root)
    (hne : s ≠ root) :
    ∃ p y,
      p ∈ forwardSlotReachSet A B root ∧
        A.matchSlot p = some y ∧
          B.matchSlot s = some y := by
  classical
  rw [forwardSlotReachSet] at hs
  rcases Finset.mem_filter.mp hs with ⟨_, hreach⟩
  rcases Relation.ReflTransGen.cases_tail hreach with hroot | ⟨p, hpReach, hpStep⟩
  · exact (hne hroot).elim
  · rcases hpStep with ⟨y, hAp, hBs⟩
    refine ⟨p, y, ?_, hAp, hBs⟩
    rw [forwardSlotReachSet]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ p, hpReach⟩

omit [DecidableEq α] [DecidableEq σ] in
/--
Along a directed alternating reachability set rooted at a `B`-slot containing an
old applicant `a`, every `B`-assigned applicant is in the old pool.  At the root
this is `a`; away from the root it is copied from an `A` slot.
-/
theorem mem_X_of_mem_forwardSlotReachSet_of_B_slot
    {X : Finset α} {A B : Assignment α σ} {root s : σ} {a y : α}
    (hAfeas : Feasible X A)
    (hroot : B.matchSlot root = some a)
    (haX : a ∈ X)
    (hs : s ∈ forwardSlotReachSet A B root)
    (hBs : B.matchSlot s = some y) :
    y ∈ X := by
  classical
  by_cases hsr : s = root
  · subst hsr
    have hya : y = a := Option.some.inj (hBs.symm.trans hroot)
    simpa [hya] using haX
  · rcases exists_forward_predecessor_of_mem_forwardSlotReachSet_of_ne hs hsr with
      ⟨p, z, _hp, hAp, hBs'⟩
    have hyz : y = z := Option.some.inj (hBs.symm.trans hBs')
    simpa [hyz] using hAfeas.1 hAp

omit [DecidableEq α] in
/--
Splicing `B` into `A` on the directed alternating reachability set preserves
no-duplicates when the root's `B` applicant is not assigned by `A`.
-/
theorem noDuplicateApplicants_spliceSlots_forwardSlotReachSet
    {A B : Assignment α σ} {root : σ} {a : α}
    (hAdup : NoDuplicateApplicants A)
    (hBdup : NoDuplicateApplicants B)
    (hroot : B.matchSlot root = some a)
    (haNotA : ¬ Assigned A a) :
    NoDuplicateApplicants (spliceSlots A B (forwardSlotReachSet A B root)) := by
  classical
  intro s t y hs ht
  by_cases hsR : s ∈ forwardSlotReachSet A B root
  · have hsB : B.matchSlot s = some y := by
      simpa [spliceSlots, hsR] using hs
    by_cases htR : t ∈ forwardSlotReachSet A B root
    · have htB : B.matchSlot t = some y := by
        simpa [spliceSlots, htR] using ht
      exact hBdup hsB htB
    · have htA : A.matchSlot t = some y := by
        simpa [spliceSlots, htR] using ht
      by_cases hsr : s = root
      · subst hsr
        have hya : y = a := Option.some.inj (hsB.symm.trans hroot)
        exact (haNotA ⟨t, by simpa [hya] using htA⟩).elim
      · rcases exists_forward_predecessor_of_mem_forwardSlotReachSet_of_ne hsR hsr with
          ⟨p, z, hpR, hAp, hBs'⟩
        have hyz : y = z := Option.some.inj (hsB.symm.trans hBs')
        have hpt : p = t := hAdup hAp (by simpa [hyz] using htA)
        exact (htR (by simpa [hpt] using hpR)).elim
  · have hsA : A.matchSlot s = some y := by
      simpa [spliceSlots, hsR] using hs
    by_cases htR : t ∈ forwardSlotReachSet A B root
    · have htB : B.matchSlot t = some y := by
        simpa [spliceSlots, htR] using ht
      by_cases htr : t = root
      · subst htr
        have hya : y = a := Option.some.inj (htB.symm.trans hroot)
        exact (haNotA ⟨s, by simpa [hya] using hsA⟩).elim
      · rcases exists_forward_predecessor_of_mem_forwardSlotReachSet_of_ne htR htr with
          ⟨p, z, hpR, hAp, hBt'⟩
        have hyz : y = z := Option.some.inj (htB.symm.trans hBt')
        have hps : p = s := hAdup hAp (by simpa [hyz] using hsA)
        exact (hsR (by simpa [hps] using hpR)).elim
    · have htA : A.matchSlot t = some y := by
        simpa [spliceSlots, htR] using ht
      exact hAdup hsA htA

omit [DecidableEq α] in
/-- Feasibility of the directed forward splice. -/
theorem feasible_spliceSlots_forwardSlotReachSet
    {X : Finset α} {A B : Assignment α σ} {root : σ} {a : α}
    (hAfeas : Feasible X A)
    (hBdup : NoDuplicateApplicants B)
    (hroot : B.matchSlot root = some a)
    (haX : a ∈ X)
    (haNotA : ¬ Assigned A a) :
    Feasible X (spliceSlots A B (forwardSlotReachSet A B root)) := by
  classical
  constructor
  · intro s y hslot
    by_cases hsR : s ∈ forwardSlotReachSet A B root
    · exact mem_X_of_mem_forwardSlotReachSet_of_B_slot
        hAfeas hroot haX hsR
        (by simpa [spliceSlots, hsR] using hslot)
    · exact hAfeas.1 (by simpa [spliceSlots, hsR] using hslot)
  · exact noDuplicateApplicants_spliceSlots_forwardSlotReachSet
      hAfeas.2 hBdup hroot haNotA

omit [DecidableEq α] in
/-- Reverse directed splice preserves no-duplicates by forward closure. -/
theorem noDuplicateApplicants_reverse_spliceSlots_forwardSlotReachSet
    {A B : Assignment α σ} {root : σ}
    (hAdup : NoDuplicateApplicants A)
    (hBdup : NoDuplicateApplicants B) :
    NoDuplicateApplicants (spliceSlots B A (forwardSlotReachSet A B root)) := by
  classical
  intro s t y hs ht
  by_cases hsR : s ∈ forwardSlotReachSet A B root
  · have hsA : A.matchSlot s = some y := by
      simpa [spliceSlots, hsR] using hs
    by_cases htR : t ∈ forwardSlotReachSet A B root
    · have htA : A.matchSlot t = some y := by
        simpa [spliceSlots, htR] using ht
      exact hAdup hsA htA
    · have htB : B.matchSlot t = some y := by
        simpa [spliceSlots, htR] using ht
      have htR' : t ∈ forwardSlotReachSet A B root :=
        mem_forwardSlotReachSet_of_mem_of_forwardSlotLinked hsR ⟨y, hsA, htB⟩
      exact (htR htR').elim
  · have hsB : B.matchSlot s = some y := by
      simpa [spliceSlots, hsR] using hs
    by_cases htR : t ∈ forwardSlotReachSet A B root
    · have htA : A.matchSlot t = some y := by
        simpa [spliceSlots, htR] using ht
      have hsR' : s ∈ forwardSlotReachSet A B root :=
        mem_forwardSlotReachSet_of_mem_of_forwardSlotLinked htR ⟨y, htA, hsB⟩
      exact (hsR hsR').elim
    · have htB : B.matchSlot t = some y := by
        simpa [spliceSlots, htR] using ht
      exact hBdup hsB htB

/-- Feasibility of the reverse directed splice for the enlarged pool. -/
theorem feasible_reverse_spliceSlots_forwardSlotReachSet_insert
    {X : Finset α} {x : α} {A B : Assignment α σ} {root : σ}
    (hAfeas : Feasible X A)
    (hBfeas : Feasible (insert x X) B) :
    Feasible (insert x X) (spliceSlots B A (forwardSlotReachSet A B root)) := by
  classical
  constructor
  · intro s y hslot
    by_cases hsR : s ∈ forwardSlotReachSet A B root
    · exact Finset.mem_insert.mpr
        (Or.inr (hAfeas.1 (by simpa [spliceSlots, hsR] using hslot)))
    · exact hBfeas.1 (by simpa [spliceSlots, hsR] using hslot)
  · exact noDuplicateApplicants_reverse_spliceSlots_forwardSlotReachSet
      hAfeas.2 hBfeas.2

/--
Fresh-root forward splice: if the root slot of `B` contains the fresh applicant
`x`, splicing the directed reachability set from `B` into `A` is feasible for
the enlarged pool.
-/
theorem feasible_insert_spliceSlots_forwardSlotReachSet_of_fresh_root
    {X : Finset α} {x : α} {A B : Assignment α σ} {root : σ}
    (hxX : x ∉ X)
    (hAfeas : Feasible X A)
    (hBfeas : Feasible (insert x X) B)
    (hroot : B.matchSlot root = some x) :
    Feasible (insert x X) (spliceSlots A B (forwardSlotReachSet A B root)) := by
  classical
  constructor
  · intro s y hslot
    by_cases hsR : s ∈ forwardSlotReachSet A B root
    · exact hBfeas.1 (by simpa [spliceSlots, hsR] using hslot)
    · exact Finset.mem_insert.mpr
        (Or.inr (hAfeas.1 (by simpa [spliceSlots, hsR] using hslot)))
  · exact noDuplicateApplicants_spliceSlots_forwardSlotReachSet
      hAfeas.2 hBfeas.2 hroot
      (by
        intro hxAssigned
        rcases hxAssigned with ⟨s, hs⟩
        exact hxX (hAfeas.1 hs))

/--
Fresh-root complementary splice: replacing the root reachability set of `B`
by the old assignment `A` removes the fresh applicant and is feasible for the
old pool.
-/
theorem feasible_old_reverse_spliceSlots_forwardSlotReachSet_of_fresh_root
    {X : Finset α} {x : α} {A B : Assignment α σ} {root : σ}
    (hxX : x ∉ X)
    (hAfeas : Feasible X A)
    (hBfeas : Feasible (insert x X) B)
    (hroot : B.matchSlot root = some x) :
    Feasible X (spliceSlots B A (forwardSlotReachSet A B root)) := by
  classical
  have hrootR : root ∈ forwardSlotReachSet A B root :=
    mem_forwardSlotReachSet_self A B root
  constructor
  · intro s y hslot
    by_cases hsR : s ∈ forwardSlotReachSet A B root
    · exact hAfeas.1 (by simpa [spliceSlots, hsR] using hslot)
    · have hBslot : B.matchSlot s = some y := by
        simpa [spliceSlots, hsR] using hslot
      have hyInsert : y ∈ insert x X := hBfeas.1 hBslot
      rcases Finset.mem_insert.mp hyInsert with hxy | hyX
      · subst hxy
        have hsRoot : s = root := hBfeas.2 hBslot hroot
        exact (hsR (by simpa [hsRoot] using hrootR)).elim
      · exact hyX
  · exact noDuplicateApplicants_reverse_spliceSlots_forwardSlotReachSet
      hAfeas.2 hBfeas.2

/-- Capacity filling for the fresh-root forward splice. -/
theorem capacityFilling_insert_spliceSlots_forwardSlotReachSet_of_fresh_root
    {X : Finset α} {x : α} {A B : Assignment α σ} {root : σ}
    (hxX : x ∉ X)
    (hspliceFeas :
      Feasible (insert x X) (spliceSlots A B (forwardSlotReachSet A B root)))
    (hAfill : CapacityFilling X A)
    (hBfill : CapacityFilling (insert x X) B)
    (hlarge : Fintype.card σ ≤ X.card) :
    CapacityFilling (insert x X)
      (spliceSlots A B (forwardSlotReachSet A B root)) := by
  classical
  exact capacityFilling_of_feasible_of_fillsSlots_of_large hspliceFeas
    (fillsSlots_spliceSlots
      (hAfill.2 hlarge)
      (hBfill.2 (by
        rw [Finset.card_insert_of_notMem hxX]
        omega)))
    (by
      rw [Finset.card_insert_of_notMem hxX]
      omega)

/-- Capacity filling for the fresh-root complementary old-pool splice. -/
theorem capacityFilling_old_reverse_spliceSlots_forwardSlotReachSet_of_fresh_root
    {X : Finset α} {A B : Assignment α σ} {root : σ}
    (hspliceFeas :
      Feasible X (spliceSlots B A (forwardSlotReachSet A B root)))
    (hAfill : CapacityFilling X A)
    (hBfillSlots : ∀ s, ∃ a, B.matchSlot s = some a)
    (hlarge : Fintype.card σ ≤ X.card) :
    CapacityFilling X (spliceSlots B A (forwardSlotReachSet A B root)) := by
  classical
  exact capacityFilling_of_feasible_of_fillsSlots_of_large hspliceFeas
    (fillsSlots_spliceSlots hBfillSlots (hAfill.2 hlarge))
    hlarge

/--
Directed alternating exchange repair.  This is the selected-new/newly-chosen
branch of the LAP exchange theorem.
-/
theorem exchangeRepair_forwardSlotReachSet
    {X : Finset α} {x a : α} {w : α → σ → ℝ} {A B : Assignment α σ}
    {root : σ}
    (hxX : x ∉ X)
    (haX : a ∈ X)
    (haNotA : a ∉ A.chosenSet)
    (hAfeas : Feasible X A)
    (hAfill : CapacityFilling X A)
    (hBfeas : Feasible (insert x X) B)
    (hBfill : CapacityFilling (insert x X) B)
    (hBopt : ObjectiveOptimal (insert x X) w B)
    (hlarge : Fintype.card σ ≤ X.card)
    (hroot : B.matchSlot root = some a) :
    ∃ C : Assignment α σ,
      Feasible X C ∧
        CapacityFilling X C ∧
          objective w A ≤ objective w C ∧
            a ∈ C.chosenSet := by
  classical
  let R := forwardSlotReachSet A B root
  let C := spliceSlots A B R
  let D := spliceSlots B A R
  have haNotAssigned : ¬ Assigned A a := by
    intro haAssigned
    exact haNotA (mem_chosenSet.mpr haAssigned)
  have hCfeas : Feasible X C :=
    feasible_spliceSlots_forwardSlotReachSet hAfeas hBfeas.2 hroot haX haNotAssigned
  have hCfill : CapacityFilling X C := by
    exact capacityFilling_of_feasible_of_fillsSlots_of_large hCfeas
      (fillsSlots_spliceSlots
        (hAfill.2 hlarge)
        (hBfill.2 (by
          rw [Finset.card_insert_of_notMem hxX]
          omega)))
      hlarge
  have hDfeas : Feasible (insert x X) D :=
    feasible_reverse_spliceSlots_forwardSlotReachSet_insert hAfeas hBfeas
  have hDfill : CapacityFilling (insert x X) D := by
    exact capacityFilling_of_feasible_of_fillsSlots_of_large hDfeas
      (fillsSlots_spliceSlots
        (hBfill.2 (by
          rw [Finset.card_insert_of_notMem hxX]
          omega))
        (hAfill.2 hlarge))
      (by
        rw [Finset.card_insert_of_notMem hxX]
        omega)
  have hDle : objective w D ≤ objective w B :=
    hBopt D hDfeas hDfill
  have hAleC : objective w A ≤ objective w C :=
    objective_le_spliceSlots_of_reverse_splice_le
      (w := w) (A := A) (B := B) (R := R) hDle
  have hrootMem : root ∈ R := mem_forwardSlotReachSet_self A B root
  have haC : a ∈ C.chosenSet := by
    rw [mem_chosenSet]
    exact ⟨root, by
      simpa [C, R, spliceSlots, hrootMem] using hroot⟩
  exact ⟨C, hCfeas, hCfill, hAleC, haC⟩

omit [DecidableEq σ] in
/--
Unique global LAP optima satisfy the selected-new/newly-chosen exchange-repair
branch by the directed alternating splice argument.
-/
theorem singleAddNewlyChosenExchangeRepair_of_selectsUniqueGlobalOptima
    {w : α → σ → ℝ} {select : Finset α → Assignment α σ}
    (hselect : SelectsUniqueGlobalOptima w select) :
    SingleAddNewlyChosenExchangeRepair w select := by
  classical
  intro X x a hxX haX haLarge _hxLarge haSmall
  rcases mem_chosenSet.mp haLarge with ⟨root, hroot⟩
  have hlarge : Fintype.card σ ≤ X.card := by
    by_contra hnot
    have hsmall : X.card ≤ Fintype.card σ := Nat.le_of_not_ge hnot
    have haChosenSmall : a ∈ (select X).chosenSet :=
      (capacityFilling_of_selectsUniqueGlobalOptima hselect X).1 hsmall haX
    exact haSmall haChosenSmall
  exact exchangeRepair_forwardSlotReachSet
    (A := select X) (B := select (insert x X)) (root := root)
    hxX haX haSmall
    (feasible_of_selectsUniqueGlobalOptima hselect X)
    (capacityFilling_of_selectsUniqueGlobalOptima hselect X)
    (feasible_of_selectsUniqueGlobalOptima hselect (insert x X))
    (capacityFilling_of_selectsUniqueGlobalOptima hselect (insert x X))
    (objectiveOptimal_of_selectsUniqueGlobalOptima hselect (insert x X))
    hlarge hroot

omit [DecidableEq σ] in
/--
Finite globally optimal LAP assignment selectors satisfy the full
single-addition exchange-repair certificate.
-/
theorem singleAddExchangeRepair_of_selectsUniqueGlobalOptima
    {w : α → σ → ℝ} {select : Finset α → Assignment α σ}
    (hselect : SelectsUniqueGlobalOptima w select) :
    SingleAddExchangeRepair w select :=
  singleAddExchangeRepair_of_selectsUniqueGlobalOptima_of_newlyChosenExchangeRepair
    hselect
    (singleAddNewlyChosenExchangeRepair_of_selectsUniqueGlobalOptima hselect)

omit [DecidableEq σ] in
/--
Finite globally optimal LAP assignment choice rules are `1`-unstable; the
exchange-repair certificate is derived above rather than assumed.
-/
theorem dUnstable_one_choiceRuleOfAssignment_of_selectsUniqueGlobalOptima
    {w : α → σ → ℝ} {select : Finset α → Assignment α σ}
    (hselect : SelectsUniqueGlobalOptima w select) :
    AppliedModelingLib.FiniteChoice.DUnstable 1 (choiceRuleOfAssignment select) :=
  dUnstable_one_choiceRuleOfAssignment_of_selectsUniqueGlobalOptima_of_singleAddExchangeRepair
    hselect
    (singleAddExchangeRepair_of_selectsUniqueGlobalOptima hselect)

omit [DecidableEq σ] in
/--
Exact one-for-one exchange for a LAP borderline loss: after adding a fresh
applicant `x`, losing old applicant `y` means the new chosen set is exactly
the old chosen set with `y` replaced by `x`.
-/
theorem choice_insert_eq_insert_erase_choice_of_lap_borderline_loss
    {X : Finset α} {x y : α} {w : α → σ → ℝ}
    {select : Finset α → Assignment α σ}
    (hselect : SelectsUniqueGlobalOptima w select)
    (hxX : x ∉ X)
    (hyLoss :
      y ∈ choiceRuleOfAssignment select X \
        choiceRuleOfAssignment select (insert x X)) :
    x ∈ choiceRuleOfAssignment select (insert x X) ∧
      (choiceRuleOfAssignment select X).card = Fintype.card σ ∧
      choiceRuleOfAssignment select (insert x X) =
        insert x ((choiceRuleOfAssignment select X).erase y) := by
  classical
  let C : AppliedModelingLib.FiniteChoice.ChoiceRule α := choiceRuleOfAssignment select
  have hfeas : AppliedModelingLib.FiniteChoice.Feasible C :=
    feasible_choiceRuleOfAssignment_of_selectsUniqueGlobalOptima hselect
  have haccept : AppliedModelingLib.FiniteChoice.QAcceptant (Fintype.card σ) C :=
    qAcceptant_choiceRuleOfAssignment_of_selectsUniqueGlobalOptima hselect
  have hunstable : AppliedModelingLib.FiniteChoice.DUnstable 1 C :=
    dUnstable_one_choiceRuleOfAssignment_of_selectsUniqueGlobalOptima hselect
  have hsub : AppliedModelingLib.FiniteChoice.Substitutable C :=
    AppliedModelingLib.FiniteChoice.substitutable_of_dUnstable_one_of_feasible_of_qAcceptant
      hfeas haccept hunstable
  simpa [C] using
    AppliedModelingLib.FiniteChoice.choice_insert_eq_insert_erase_choice_of_borderline_witness
      (C := C) hfeas haccept hsub hunstable hxX hyLoss

omit [DecidableEq σ] in
/--
Every LAP borderline applicant has a fresh one-for-one exchange witness.
-/
theorem exists_exact_exchange_witness_of_mem_borderlineSet_choiceRuleOfAssignment
    [Fintype α] {X : Finset α} {y : α} {w : α → σ → ℝ}
    {select : Finset α → Assignment α σ}
    (hselect : SelectsUniqueGlobalOptima w select)
    (hyB : y ∈ AppliedModelingLib.FiniteChoice.borderlineSet
      (choiceRuleOfAssignment select) X) :
    ∃ x,
      x ∉ X ∧
        x ∈ choiceRuleOfAssignment select (insert x X) ∧
          choiceRuleOfAssignment select (insert x X) =
            insert x ((choiceRuleOfAssignment select X).erase y) := by
  classical
  rcases exists_loss_witness_of_mem_borderlineSet_choiceRuleOfAssignment
      (select := select) (X := X) (y := y) hyB with
    ⟨x, hyLoss⟩
  have hyChoice : y ∈ choiceRuleOfAssignment select X :=
    (Finset.mem_sdiff.mp hyLoss).1
  have hxX : x ∉ X := by
    intro hxX
    have hsame :
        choiceRuleOfAssignment select (insert x X) =
          choiceRuleOfAssignment select X := by
      rw [Finset.insert_eq_of_mem hxX]
    exact (Finset.mem_sdiff.mp hyLoss).2 (by simpa [hsame] using hyChoice)
  rcases choice_insert_eq_insert_erase_choice_of_lap_borderline_loss
      hselect hxX hyLoss with
    ⟨hxChosen, _hcard, hchoice⟩
  exact ⟨x, hxX, hxChosen, hchoice⟩

omit [DecidableEq σ] in
/--
In an exact one-for-one LAP insertion, the directed alternating path starting
at the new slot of the fresh applicant reaches the old slot of the lost
applicant.
-/
theorem lost_slot_mem_forwardSlotReachSet_of_lap_borderline_loss
    {X : Finset α} {x y : α} {root lost : σ} {w : α → σ → ℝ}
    {select : Finset α → Assignment α σ}
    (hselect : SelectsUniqueGlobalOptima w select)
    (hxX : x ∉ X)
    (hyLoss :
      y ∈ choiceRuleOfAssignment select X \
        choiceRuleOfAssignment select (insert x X))
    (hroot : (select (insert x X)).matchSlot root = some x)
    (hlost : (select X).matchSlot lost = some y) :
    lost ∈ forwardSlotReachSet (select X) (select (insert x X)) root := by
  classical
  let A : Assignment α σ := select X
  let B : Assignment α σ := select (insert x X)
  let R : Finset σ := forwardSlotReachSet A B root
  by_contra hlostNotR
  rcases choice_insert_eq_insert_erase_choice_of_lap_borderline_loss
      hselect hxX hyLoss with
    ⟨_hxChosen, hcardA, hchoice⟩
  change B.chosenSet = insert x (A.chosenSet.erase y) at hchoice
  change A.chosenSet.card = Fintype.card σ at hcardA
  have hAfeas : Feasible X A :=
    feasible_of_selectsUniqueGlobalOptima hselect X
  have hAfill : CapacityFilling X A :=
    capacityFilling_of_selectsUniqueGlobalOptima hselect X
  have hBfeas : Feasible (insert x X) B :=
    feasible_of_selectsUniqueGlobalOptima hselect (insert x X)
  have hqleX : Fintype.card σ ≤ X.card := by
    have hsub : A.chosenSet ⊆ X := chosenSet_subset_of_feasible hAfeas
    have hcard_le : A.chosenSet.card ≤ X.card := Finset.card_le_card hsub
    omega
  have hAfills : ∀ s, ∃ a, A.matchSlot s = some a := hAfill.2 hqleX
  have hrootR : root ∈ R := mem_forwardSlotReachSet_self A B root
  let oldOf : {s // s ∈ R} → α := fun s => Classical.choose (hAfills s.1)
  have hOldSlot : ∀ s : {s // s ∈ R}, A.matchSlot s.1 = some (oldOf s) := by
    intro s
    exact Classical.choose_spec (hAfills s.1)
  have hOld_ne_lost : ∀ s : {s // s ∈ R}, oldOf s ≠ y := by
    intro s hEq
    have hs_lost : s.1 = lost := by
      exact hAfeas.2 (by simpa [hEq] using hOldSlot s) hlost
    exact hlostNotR (by simpa [R, hs_lost] using s.2)
  have hnext_exists :
      ∀ s : {s // s ∈ R},
        ∃ t : {t // t ∈ R}, B.matchSlot t.1 = some (oldOf s) := by
    intro s
    have holdChosenA : oldOf s ∈ A.chosenSet :=
      mem_chosenSet.mpr ⟨s.1, hOldSlot s⟩
    have holdChosenB : oldOf s ∈ B.chosenSet := by
      rw [hchoice]
      exact Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨hOld_ne_lost s, holdChosenA⟩)
    rcases mem_chosenSet.mp holdChosenB with ⟨t, htB⟩
    have htR : t ∈ R :=
      mem_forwardSlotReachSet_of_mem_of_forwardSlotLinked
        (A := A) (B := B) (root := root) s.2
        ⟨oldOf s, hOldSlot s, htB⟩
    exact ⟨⟨t, htR⟩, htB⟩
  let next : {s // s ∈ R} → {s // s ∈ R} :=
    fun s => Classical.choose (hnext_exists s)
  have hNextSlot :
      ∀ s : {s // s ∈ R}, B.matchSlot (next s).1 = some (oldOf s) := by
    intro s
    exact Classical.choose_spec (hnext_exists s)
  have hnext_inj : Function.Injective next := by
    intro s t hst
    apply Subtype.ext
    have hBt : B.matchSlot (next s).1 = some (oldOf t) := by
      simpa [hst] using hNextSlot t
    have hold_eq : oldOf s = oldOf t :=
      Option.some.inj ((hNextSlot s).symm.trans hBt)
    exact hAfeas.2 (hOldSlot s) (by simpa [hold_eq] using hOldSlot t)
  have hnext_surj : Function.Surjective next :=
    Finite.surjective_of_injective hnext_inj
  rcases hnext_surj ⟨root, hrootR⟩ with ⟨s, hsroot⟩
  have hBroot_old : B.matchSlot root = some (oldOf s) := by
    simpa [hsroot] using hNextSlot s
  have hx_old : x = oldOf s := Option.some.inj (hroot.symm.trans hBroot_old)
  have holdX : oldOf s ∈ X := hAfeas.1 (hOldSlot s)
  exact hxX (by simpa [hx_old] using holdX)

omit [DecidableEq σ] in
/--
In a one-for-one LAP borderline loss, the old slot of the lost applicant has
no outgoing directed alternating edge: the applicant occupying that old slot is
not assigned by the enlarged-pool optimum.
-/
theorem not_exists_forwardSlotLinked_from_lost_of_lap_borderline_loss
    {X : Finset α} {x y : α} {lost : σ}
    {select : Finset α → Assignment α σ}
    (hyLoss :
      y ∈ choiceRuleOfAssignment select X \
        choiceRuleOfAssignment select (insert x X))
    (hlost : (select X).matchSlot lost = some y) :
    ¬ ∃ t,
      forwardSlotLinked (select X) (select (insert x X)) lost t := by
  classical
  rintro ⟨t, a, hAlost, hBt⟩
  have hay : a = y := Option.some.inj (hAlost.symm.trans hlost)
  have hyNotNew : y ∉ (select (insert x X)).chosenSet := by
    change y ∉ choiceRuleOfAssignment select (insert x X)
    exact (Finset.mem_sdiff.mp hyLoss).2
  exact hyNotNew (mem_chosenSet.mpr ⟨t, by simpa [hay] using hBt⟩)

omit [DecidableEq σ] in
/--
When the fresh applicant occupies `root` after insertion, no directed
alternating edge enters `root`, because the fresh applicant was not assigned
by the old-pool assignment.
-/
theorem not_exists_forwardSlotLinked_to_fresh_root
    {X : Finset α} {x : α} {root : σ}
    {A B : Assignment α σ}
    (hxX : x ∉ X)
    (hAfeas : Feasible X A)
    (hroot : B.matchSlot root = some x) :
    ¬ ∃ p, forwardSlotLinked A B p root := by
  rintro ⟨p, a, hAp, hBroot⟩
  have hax : a = x := Option.some.inj (hBroot.symm.trans hroot)
  exact hxX (hAfeas.1 (by simpa [hax] using hAp))

omit [DecidableEq α] in
/--
For a fresh-root directed exchange path, the suffix beginning at a reachable
slot's successor cannot loop back to that reachable slot.
-/
theorem not_mem_forwardSlotReachSet_successor_of_mem_fresh_root_reachSet
    {X : Finset α} {x : α} {A B : Assignment α σ}
    {root oldSlot succ : σ}
    (hxX : x ∉ X)
    (hAfeas : Feasible X A)
    (hroot : B.matchSlot root = some x)
    (hold : oldSlot ∈ forwardSlotReachSet A B root)
    (hstep : forwardSlotLinked A B oldSlot succ) :
    oldSlot ∉ forwardSlotReachSet A B succ := by
  classical
  intro holdSuffix
  have hroot_old :
      Relation.ReflTransGen (forwardSlotLinked A B) root oldSlot := by
    rw [forwardSlotReachSet] at hold
    exact (Finset.mem_filter.mp hold).2
  have hsucc_old :
      Relation.ReflTransGen (forwardSlotLinked A B) succ oldSlot := by
    rw [forwardSlotReachSet] at holdSuffix
    exact (Finset.mem_filter.mp holdSuffix).2
  exact
    not_forward_reaches_back_of_reachable_of_root_no_incoming
      (A := A) (B := B)
      hAfeas.2
      (not_exists_forwardSlotLinked_to_fresh_root hxX hAfeas hroot)
      hroot_old hstep hsucc_old

/--
In an exact LAP insertion that loses `y`, every slot in the fresh-root
reachability set lies on the directed path to the old slot of `y`.
-/
theorem forward_reaches_lost_of_mem_forwardSlotReachSet_of_lap_borderline_loss
    {X : Finset α} {x y : α} {root lost s : σ} {w : α → σ → ℝ}
    {select : Finset α → Assignment α σ}
    (hselect : SelectsUniqueGlobalOptima w select)
    (hxX : x ∉ X)
    (hyLoss :
      y ∈ choiceRuleOfAssignment select X \
        choiceRuleOfAssignment select (insert x X))
    (hroot : (select (insert x X)).matchSlot root = some x)
    (hlost : (select X).matchSlot lost = some y)
    (hs :
      s ∈ forwardSlotReachSet (select X) (select (insert x X)) root) :
    Relation.ReflTransGen
      (forwardSlotLinked (select X) (select (insert x X))) s lost := by
  exact forward_reaches_terminal_of_mem_forwardSlotReachSet
    ((feasible_of_selectsUniqueGlobalOptima hselect (insert x X)).2)
    hs
    (lost_slot_mem_forwardSlotReachSet_of_lap_borderline_loss
      (select := select) hselect hxX hyLoss hroot hlost)
    (not_exists_forwardSlotLinked_from_lost_of_lap_borderline_loss
      (select := select) hyLoss hlost)

/--
Cycle-aligned optimality for an exact LAP insertion: splicing the enlarged
assignment into the old assignment on the fresh-to-lost reachability set
remains globally optimal for the enlarged pool.
-/
theorem objectiveOptimal_spliceSlots_forwardSlotReachSet_of_lap_borderline_loss
    {X : Finset α} {x y : α} {root : σ} {w : α → σ → ℝ}
    {select : Finset α → Assignment α σ}
    (hselect : SelectsUniqueGlobalOptima w select)
    (hxX : x ∉ X)
    (hyLoss :
      y ∈ choiceRuleOfAssignment select X \
        choiceRuleOfAssignment select (insert x X))
    (hroot : (select (insert x X)).matchSlot root = some x) :
    ObjectiveOptimal (insert x X) w
      (spliceSlots (select X) (select (insert x X))
        (forwardSlotReachSet (select X) (select (insert x X)) root)) := by
  classical
  let A : Assignment α σ := select X
  let B : Assignment α σ := select (insert x X)
  let R : Finset σ := forwardSlotReachSet A B root
  let C : Assignment α σ := spliceSlots A B R
  let D : Assignment α σ := spliceSlots B A R
  rcases choice_insert_eq_insert_erase_choice_of_lap_borderline_loss
      hselect hxX hyLoss with
    ⟨_hxChosen, hcardA, _hchoice⟩
  change A.chosenSet.card = Fintype.card σ at hcardA
  have hAfeas : Feasible X A :=
    feasible_of_selectsUniqueGlobalOptima hselect X
  have hAfill : CapacityFilling X A :=
    capacityFilling_of_selectsUniqueGlobalOptima hselect X
  have hAopt : ObjectiveOptimal X w A :=
    objectiveOptimal_of_selectsUniqueGlobalOptima hselect X
  have hBfeas : Feasible (insert x X) B :=
    feasible_of_selectsUniqueGlobalOptima hselect (insert x X)
  have hBfill : CapacityFilling (insert x X) B :=
    capacityFilling_of_selectsUniqueGlobalOptima hselect (insert x X)
  have hBopt : ObjectiveOptimal (insert x X) w B :=
    objectiveOptimal_of_selectsUniqueGlobalOptima hselect (insert x X)
  have hqleX : Fintype.card σ ≤ X.card := by
    have hsub : A.chosenSet ⊆ X := chosenSet_subset_of_feasible hAfeas
    have hcard_le : A.chosenSet.card ≤ X.card := Finset.card_le_card hsub
    omega
  have hCfeas : Feasible (insert x X) C :=
    feasible_insert_spliceSlots_forwardSlotReachSet_of_fresh_root
      (A := A) (B := B) (root := root) hxX hAfeas hBfeas hroot
  have hCfill : CapacityFilling (insert x X) C :=
    capacityFilling_insert_spliceSlots_forwardSlotReachSet_of_fresh_root
      (A := A) (B := B) (root := root) hxX hCfeas hAfill hBfill hqleX
  have hDfeas : Feasible X D :=
    feasible_old_reverse_spliceSlots_forwardSlotReachSet_of_fresh_root
      (A := A) (B := B) (root := root) hxX hAfeas hBfeas hroot
  have hDfill : CapacityFilling X D :=
    capacityFilling_old_reverse_spliceSlots_forwardSlotReachSet_of_fresh_root
      (A := A) (B := B) (root := root) hDfeas hAfill
      (hBfill.2 (by
        rw [Finset.card_insert_of_notMem hxX]
        omega))
      hqleX
  have hDleA : objective w D ≤ objective w A :=
    hAopt D hDfeas hDfill
  have hBleC : objective w B ≤ objective w C := by
    have hsum :
        objective w C + objective w D = objective w A + objective w B :=
      objective_spliceSlots_add_objective_spliceSlots
        (w := w) (A := A) (B := B) (R := R)
    have hplus :
        objective w B + objective w A ≤ objective w C + objective w A := by
      rw [add_comm (objective w B) (objective w A), ← hsum]
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_left hDleA (objective w C)
    exact (add_le_add_iff_right (objective w A)).mp hplus
  have hCleB : objective w C ≤ objective w B :=
    hBopt C hCfeas hCfill
  have hCeqB : objective w C = objective w B :=
    le_antisymm hCleB hBleC
  intro E hEfeas hEfill
  have hEleB : objective w E ≤ objective w B := hBopt E hEfeas hEfill
  change objective w E ≤ objective w C
  rw [hCeqB]
  exact hEleB

omit [DecidableEq σ] in
/--
For a unique-global-optimum LAP selector, once one old chosen applicant is
lost after a fresh insertion, every other old chosen applicant remains chosen.
-/
theorem chosen_after_insert_of_ne_lost_of_selectsUniqueGlobalOptima
    {X : Finset α} {x y z : α} {w : α → σ → ℝ}
    {select : Finset α → Assignment α σ}
    (hselect : SelectsUniqueGlobalOptima w select)
    (hxX : x ∉ X)
    (hyLoss :
      y ∈ choiceRuleOfAssignment select X \
        choiceRuleOfAssignment select (insert x X))
    (hzChoice : z ∈ choiceRuleOfAssignment select X)
    (hz_ne_y : z ≠ y) :
    z ∈ choiceRuleOfAssignment select (insert x X) := by
  classical
  have hdist :=
    dUnstable_one_choiceRuleOfAssignment_of_selectsUniqueGlobalOptima
      (select := select) hselect X x hxX
  have hlossCard :
      (choiceRuleOfAssignment select X \
        choiceRuleOfAssignment select (insert x X)).card ≤ 1 := by
    rw [AppliedModelingLib.FiniteChoice.choiceDistance,
      AppliedModelingLib.FiniteChoice.choiceLossTerm] at hdist
    omega
  exact AppliedModelingLib.FiniteChoice.mem_of_mem_of_ne_lost_of_sdiff_card_le_one
    hyLoss hzChoice hz_ne_y hlossCard

/-- Replace the current occupant of slot `s` by applicant `a`. -/
def replaceSlot (A : Assignment α σ) (s : σ) (a : α) : Assignment α σ where
  matchSlot := Function.update A.matchSlot s (some a)

omit [DecidableEq α] [Fintype σ] in
/-- Replacing one slot by an applicant in `X` preserves the assigned-from condition. -/
theorem assignedFrom_replaceSlot_of_assignedFrom_of_mem
    {X : Finset α} {A : Assignment α σ} {s : σ} {x : α}
    (hfrom : AssignedFrom X A) (hx : x ∈ X) :
    AssignedFrom X (replaceSlot A s x) := by
  intro t a ht
  by_cases hts : t = s
  · subst hts
    have hax : a = x := by
      simpa [replaceSlot] using ht.symm
    simpa [hax] using hx
  · exact hfrom (by
      simpa [replaceSlot, Function.update_of_ne hts] using ht)

omit [DecidableEq α] [Fintype σ] in
/--
Replacing one slot by a previously unassigned applicant preserves the no-duplicate
condition.
-/
theorem noDuplicateApplicants_replaceSlot_of_noDuplicateApplicants_of_not_assigned
    {A : Assignment α σ} {s : σ} {x : α}
    (hdup : NoDuplicateApplicants A) (hx : ¬ Assigned A x) :
    NoDuplicateApplicants (replaceSlot A s x) := by
  intro t u a ht hu
  by_cases hts : t = s
  · subst hts
    have hax : a = x := by
      simpa [replaceSlot] using ht.symm
    subst hax
    by_cases hut : u = t
    · exact hut.symm
    · exfalso
      exact hx ⟨u, by
        simpa [replaceSlot, Function.update_of_ne hut] using hu⟩
  · by_cases hus : u = s
    · subst hus
      have hax : a = x := by
        simpa [replaceSlot] using hu.symm
      subst hax
      exfalso
      exact hx ⟨t, by
        simpa [replaceSlot, Function.update_of_ne hts] using ht⟩
    · exact hdup
        (by simpa [replaceSlot, Function.update_of_ne hts] using ht)
        (by simpa [replaceSlot, Function.update_of_ne hus] using hu)

omit [DecidableEq α] [Fintype σ] in
/-- Replacing one slot by a rejected applicant preserves feasibility. -/
theorem feasible_replaceSlot_of_feasible_of_rejected
    {X : Finset α} {A : Assignment α σ} {s : σ} {x : α}
    (hfeas : Feasible X A) (hrej : Rejected X A x) :
    Feasible X (replaceSlot A s x) :=
  ⟨assignedFrom_replaceSlot_of_assignedFrom_of_mem hfeas.1 hrej.1,
    noDuplicateApplicants_replaceSlot_of_noDuplicateApplicants_of_not_assigned hfeas.2 hrej.2⟩

/--
Replacing an occupied slot by a rejected applicant preserves the
capacity-filling convention.
-/
theorem capacityFilling_replaceSlot_of_capacityFilling_of_rejected
    {X : Finset α} {A : Assignment α σ} {s : σ} {y x : α}
    (hfill : CapacityFilling X A)
    (hslot : A.matchSlot s = some y)
    (hrej : Rejected X A x) :
    CapacityFilling X (replaceSlot A s x) := by
  constructor
  · intro hsmall
    exfalso
    have hxChosen : x ∈ A.chosenSet := hfill.1 hsmall hrej.1
    exact hrej.2 (mem_chosenSet.mp hxChosen)
  · intro hlarge t
    by_cases hts : t = s
    · subst hts
      exact ⟨x, by simp [replaceSlot]⟩
    · rcases hfill.2 hlarge t with ⟨a, ha⟩
      exact ⟨a, by
        simpa [replaceSlot, Function.update_of_ne hts] using ha⟩

/--
Primitive local optimality: no feasible one-slot replacement of an assigned
slot occupant by a rejected applicant strictly improves the linear objective.
-/
def NoProfitableOneSlotSwap
    (X : Finset α) (w : α → σ → ℝ) (A : Assignment α σ) : Prop :=
  ∀ {s y x},
    A.matchSlot s = some y →
      Rejected X A x →
        Feasible X (replaceSlot A s x) →
          ¬ objective w A < objective w (replaceSlot A s x)

/-- Global objective optimality implies no profitable one-slot swap. -/
theorem noProfitableOneSlotSwap_of_objectiveOptimal
    {X : Finset α} {w : α → σ → ℝ} {A : Assignment α σ}
    (hopt : ObjectiveOptimal X w A)
    (hfill : CapacityFilling X A) :
    NoProfitableOneSlotSwap X w A := by
  intro s y x hslot hrej hfeasReplace hlt
  have hfillReplace :
      CapacityFilling X (replaceSlot A s x) :=
    capacityFilling_replaceSlot_of_capacityFilling_of_rejected
      hfill hslot hrej
  have hle :
      objective w (replaceSlot A s x) ≤ objective w A :=
    hopt (replaceSlot A s x) hfeasReplace hfillReplace
  exact not_lt_of_ge hle hlt

/-- Strict slot order induced by the slot's assignment weight. -/
def SlotBelow (w : α → σ → ℝ) (s : σ) (a b : α) : Prop :=
  w a s < w b s

omit [DecidableEq α] [DecidableEq σ] [Fintype σ] in
/-- Strict slot comparison implies distinct applicants. -/
theorem ne_of_slotBelow
    {w : α → σ → ℝ} {s : σ} {a b : α}
    (hbelow : SlotBelow w s a b) :
    a ≠ b := by
  intro hab
  rw [hab] at hbelow
  exact (lt_irrefl (w b s)) hbelow

/-- Weak slot order induced by the slot's assignment weight. -/
def SlotAtLeast (w : α → σ → ℝ) (s : σ) (a b : α) : Prop :=
  w b s ≤ w a s

omit [DecidableEq σ] in
/--
In a no-ties slot order, two distinct applicants are strictly comparable; the
comparison can be transported to any slot with the same induced order.
-/
theorem slotBelow_or_slotBelow_of_sameSlotOrder_of_noTies
    {w : α → σ → ℝ} {s t : σ} {a b : α}
    (hsame : SameSlotOrder w s t)
    (hnoTies : SlotNoTies w s)
    (hab : a ≠ b) :
    SlotBelow w s a b ∨ SlotBelow w t b a := by
  unfold SlotBelow
  have hne : w a s ≠ w b s := hnoTies hab
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact Or.inl hlt
  · exact Or.inr ((hsame b a).mp hgt)

set_option linter.unusedSectionVars false in
/--
Replacing the occupant of one slot by a strictly higher-weight applicant
strictly raises the finite linear objective.
-/
theorem objective_lt_replaceSlot_of_slot_weight_lt
    {w : α → σ → ℝ} {A : Assignment α σ} {s : σ} {y x : α}
    (hslot : A.matchSlot s = some y) (hweight : w y s < w x s) :
    objective w A < objective w (replaceSlot A s x) := by
  let rest : ℝ := (Finset.univ.erase s).sum fun t => slotValue w A t
  have hrest :
      ((Finset.univ.erase s).sum fun t =>
        slotValue w (replaceSlot A s x) t) = rest := by
    dsimp [rest]
    apply Finset.sum_congr rfl
    intro t ht
    have hts : t ≠ s := (Finset.mem_erase.mp ht).1
    simp [slotValue, replaceSlot, Function.update_of_ne hts]
  have hA :
      objective w A = rest + w y s := by
    have hsum :
        objective w A =
          ((Finset.univ.erase s).sum fun t => slotValue w A t) + slotValue w A s := by
      unfold objective
      exact (Finset.sum_erase_add (Finset.univ : Finset σ)
        (fun t => slotValue w A t) (Finset.mem_univ s)).symm
    rw [hsum]
    simp [rest, slotValue, hslot]
  have hSwap :
      objective w (replaceSlot A s x) = rest + w x s := by
    have hsum :
        objective w (replaceSlot A s x) =
          ((Finset.univ.erase s).sum fun t => slotValue w (replaceSlot A s x) t) +
            slotValue w (replaceSlot A s x) s := by
      unfold objective
      exact (Finset.sum_erase_add (Finset.univ : Finset σ)
        (fun t => slotValue w (replaceSlot A s x) t) (Finset.mem_univ s)).symm
    rw [hsum, hrest]
    simp [slotValue, replaceSlot]
  calc
    objective w A = rest + w y s := hA
    _ < rest + w x s := by
      simpa [add_comm] using add_lt_add_left hweight rest
    _ = objective w (replaceSlot A s x) := hSwap.symm

/--
LAP ordering lemma from primitive optimality: if `y` occupies slot `s`, `x` is
rejected from the same applicant pool, and the one-slot replacement is feasible,
then `y` is not below `x` in the slot-weight order.
-/
theorem not_slotBelow_of_noProfitableOneSlotSwap
    {X : Finset α} {w : α → σ → ℝ} {A : Assignment α σ}
    (hopt : NoProfitableOneSlotSwap X w A)
    {s : σ} {y x : α}
    (hslot : A.matchSlot s = some y)
    (hrej : Rejected X A x)
    (hfeas : Feasible X (replaceSlot A s x)) :
    ¬ SlotBelow w s y x := by
  intro hbelow
  exact hopt hslot hrej hfeas
    (objective_lt_replaceSlot_of_slot_weight_lt hslot hbelow)

/--
Equivalent weak-order form: under the same hypotheses, the assigned applicant
is at least as high as the rejected feasible replacement at slot `s`.
-/
theorem slotAtLeast_of_noProfitableOneSlotSwap
    {X : Finset α} {w : α → σ → ℝ} {A : Assignment α σ}
    (hopt : NoProfitableOneSlotSwap X w A)
    {s : σ} {y x : α}
    (hslot : A.matchSlot s = some y)
    (hrej : Rejected X A x)
    (hfeas : Feasible X (replaceSlot A s x)) :
    SlotAtLeast w s y x := by
  exact le_of_not_gt
    (not_slotBelow_of_noProfitableOneSlotSwap hopt hslot hrej hfeas)

/--
Feasible-assignment bridge: if `A` is feasible and locally optimal, then every
occupied slot ranks its occupant at least as high as any rejected applicant.
-/
theorem slotAtLeast_rejected_of_noProfitableOneSlotSwap_of_feasible
    {X : Finset α} {w : α → σ → ℝ} {A : Assignment α σ}
    (hopt : NoProfitableOneSlotSwap X w A)
    (hfeas : Feasible X A)
    {s : σ} {y x : α}
    (hslot : A.matchSlot s = some y)
    (hrej : Rejected X A x) :
    SlotAtLeast w s y x := by
  exact slotAtLeast_of_noProfitableOneSlotSwap hopt hslot hrej
    (feasible_replaceSlot_of_feasible_of_rejected hfeas hrej)

omit [DecidableEq σ] in
/--
Any old slot whose occupant is strictly below the lost applicant in that
slot's order must lie on the fresh-to-lost reachability set. Otherwise the
cycle-aligned enlarged optimum would keep that occupant in the same slot and
contradict the LAP ordering lemma.
-/
theorem old_slot_mem_forwardSlotReachSet_of_slotBelow_lost_of_lap_borderline_loss
    {X : Finset α} {x y z : α} {root lost oldSlot : σ}
    {w : α → σ → ℝ} {select : Finset α → Assignment α σ}
    (hselect : SelectsUniqueGlobalOptima w select)
    (hxX : x ∉ X)
    (hyLoss :
      y ∈ choiceRuleOfAssignment select X \
        choiceRuleOfAssignment select (insert x X))
    (hroot : (select (insert x X)).matchSlot root = some x)
    (hlost : (select X).matchSlot lost = some y)
    (hzOldSlot : (select X).matchSlot oldSlot = some z)
    (hbelow : SlotBelow w oldSlot z y) :
    oldSlot ∈ forwardSlotReachSet (select X) (select (insert x X)) root := by
  classical
  let A : Assignment α σ := select X
  let B : Assignment α σ := select (insert x X)
  let R : Finset σ := forwardSlotReachSet A B root
  by_contra hOldNotR
  let C : Assignment α σ := spliceSlots A B R
  rcases choice_insert_eq_insert_erase_choice_of_lap_borderline_loss
      hselect hxX hyLoss with
    ⟨_hxChosen, hcardA, _hchoice⟩
  change A.chosenSet.card = Fintype.card σ at hcardA
  have hAfeas : Feasible X A :=
    feasible_of_selectsUniqueGlobalOptima hselect X
  have hAfill : CapacityFilling X A :=
    capacityFilling_of_selectsUniqueGlobalOptima hselect X
  have hBfeas : Feasible (insert x X) B :=
    feasible_of_selectsUniqueGlobalOptima hselect (insert x X)
  have hBfill : CapacityFilling (insert x X) B :=
    capacityFilling_of_selectsUniqueGlobalOptima hselect (insert x X)
  have hqleX : Fintype.card σ ≤ X.card := by
    have hsub : A.chosenSet ⊆ X := chosenSet_subset_of_feasible hAfeas
    have hcard_le : A.chosenSet.card ≤ X.card := Finset.card_le_card hsub
    omega
  have hCfeas : Feasible (insert x X) C :=
    feasible_insert_spliceSlots_forwardSlotReachSet_of_fresh_root
      (A := A) (B := B) (root := root) hxX hAfeas hBfeas hroot
  have hCfill : CapacityFilling (insert x X) C :=
    capacityFilling_insert_spliceSlots_forwardSlotReachSet_of_fresh_root
      (A := A) (B := B) (root := root) hxX hCfeas hAfill hBfill hqleX
  have hCopt : ObjectiveOptimal (insert x X) w C :=
    objectiveOptimal_spliceSlots_forwardSlotReachSet_of_lap_borderline_loss
      (select := select) hselect hxX hyLoss hroot
  have hOldNotR' : oldSlot ∉ R := by
    simpa [A, B, R] using hOldNotR
  have hCYslot : C.matchSlot oldSlot = some z := by
    simpa [C, R, spliceSlots, hOldNotR'] using hzOldSlot
  have hyX : y ∈ X := hAfeas.1 hlost
  have hlostR : lost ∈ R :=
    lost_slot_mem_forwardSlotReachSet_of_lap_borderline_loss
      (select := select) hselect hxX hyLoss hroot hlost
  have hyNotC : ¬ Assigned C y := by
    rintro ⟨s, hs⟩
    by_cases hsR : s ∈ R
    · have hBs : B.matchSlot s = some y := by
        simpa [C, R, spliceSlots, hsR] using hs
      have hyNotB : y ∉ B.chosenSet := by
        change y ∉ choiceRuleOfAssignment select (insert x X)
        exact (Finset.mem_sdiff.mp hyLoss).2
      exact hyNotB (mem_chosenSet.mpr ⟨s, hBs⟩)
    · have hAs : A.matchSlot s = some y := by
        simpa [C, R, spliceSlots, hsR] using hs
      have hsLost : s = lost := hAfeas.2 hAs hlost
      exact hsR (by simpa [R, hsLost] using hlostR)
  have hrej : Rejected (insert x X) C y :=
    ⟨Finset.mem_insert.mpr (Or.inr hyX), hyNotC⟩
  have hAtLeast : SlotAtLeast w oldSlot z y :=
    slotAtLeast_rejected_of_noProfitableOneSlotSwap_of_feasible
      (noProfitableOneSlotSwap_of_objectiveOptimal hCopt hCfill)
      hCfeas hCYslot hrej
  exact not_lt_of_ge hAtLeast hbelow

omit [DecidableEq σ] in
/--
If an old applicant is lost after one fresh insertion and another old
applicant survives in a particular new slot, the survivor is at least as high
as the lost applicant in that new slot's order.
-/
theorem slotAtLeast_survivor_of_single_insert_loss
    {X : Finset α} {x y z : α} {s : σ} {w : α → σ → ℝ}
    {select : Finset α → Assignment α σ}
    (hselect : SelectsUniqueGlobalOptima w select)
    (hyLoss :
      y ∈ choiceRuleOfAssignment select X \
        choiceRuleOfAssignment select (insert x X))
    (hslot : (select (insert x X)).matchSlot s = some z) :
    SlotAtLeast w s z y := by
  classical
  have hyOld : y ∈ choiceRuleOfAssignment select X :=
    (Finset.mem_sdiff.mp hyLoss).1
  have hyNotNew : y ∉ choiceRuleOfAssignment select (insert x X) :=
    (Finset.mem_sdiff.mp hyLoss).2
  have hyX : y ∈ X :=
    feasible_choiceRuleOfAssignment_of_selectsUniqueGlobalOptima hselect X hyOld
  have hrej : Rejected (insert x X) (select (insert x X)) y := by
    refine ⟨Finset.mem_insert.mpr (Or.inr hyX), ?_⟩
    intro hyAssigned
    exact hyNotNew (by
      change y ∈ (select (insert x X)).chosenSet
      exact mem_chosenSet.mpr hyAssigned)
  exact slotAtLeast_rejected_of_noProfitableOneSlotSwap_of_feasible
    (noProfitableOneSlotSwap_of_objectiveOptimal
      (objectiveOptimal_of_selectsUniqueGlobalOptima hselect (insert x X))
      (capacityFilling_of_selectsUniqueGlobalOptima hselect (insert x X)))
    (feasible_of_selectsUniqueGlobalOptima hselect (insert x X))
    hslot hrej

omit [DecidableEq σ] in
/--
In the enlarged-pool optimum, the fresh applicant that exactly replaces a
lost old applicant weakly dominates that lost applicant at the fresh
applicant's assigned slot.
-/
theorem slotAtLeast_inserted_witness_vs_lost_of_lap_borderline_loss
    {X : Finset α} {x y : α} {s : σ} {w : α → σ → ℝ}
    {select : Finset α → Assignment α σ}
    (hselect : SelectsUniqueGlobalOptima w select)
    (hyLoss :
      y ∈ choiceRuleOfAssignment select X \
        choiceRuleOfAssignment select (insert x X))
    (hslot : (select (insert x X)).matchSlot s = some x) :
    SlotAtLeast w s x y :=
  slotAtLeast_survivor_of_single_insert_loss hselect hyLoss hslot

omit [DecidableEq σ] in
/--
Existential fresh-witness form: a LAP borderline loss has an inserted applicant
assigned to some slot that weakly dominates the lost applicant in that slot's
order.
-/
theorem exists_slotAtLeast_inserted_witness_vs_lost_of_lap_borderline_loss
    {X : Finset α} {x y : α} {w : α → σ → ℝ}
    {select : Finset α → Assignment α σ}
    (hselect : SelectsUniqueGlobalOptima w select)
    (hxX : x ∉ X)
    (hyLoss :
      y ∈ choiceRuleOfAssignment select X \
        choiceRuleOfAssignment select (insert x X)) :
    ∃ s,
      (select (insert x X)).matchSlot s = some x ∧
        SlotAtLeast w s x y := by
  rcases choice_insert_eq_insert_erase_choice_of_lap_borderline_loss
      hselect hxX hyLoss with
    ⟨hxChosen, _hcard, _hchoice⟩
  change x ∈ (select (insert x X)).chosenSet at hxChosen
  rcases mem_chosenSet.mp hxChosen with ⟨s, hslot⟩
  exact ⟨s, hslot,
    slotAtLeast_inserted_witness_vs_lost_of_lap_borderline_loss
      hselect hyLoss hslot⟩

omit [DecidableEq σ] in
/--
Packaged survivor form: every old chosen applicant distinct from the single
old loss is assigned to some new slot that ranks it at least as high as the
lost applicant.
-/
theorem exists_slotAtLeast_survivor_of_ne_lost_of_selectsUniqueGlobalOptima
    {X : Finset α} {x y z : α} {w : α → σ → ℝ}
    {select : Finset α → Assignment α σ}
    (hselect : SelectsUniqueGlobalOptima w select)
    (hxX : x ∉ X)
    (hyLoss :
      y ∈ choiceRuleOfAssignment select X \
        choiceRuleOfAssignment select (insert x X))
    (hzChoice : z ∈ choiceRuleOfAssignment select X)
    (hz_ne_y : z ≠ y) :
    ∃ s,
      (select (insert x X)).matchSlot s = some z ∧
        SlotAtLeast w s z y := by
  have hzNew :
      z ∈ choiceRuleOfAssignment select (insert x X) :=
    chosen_after_insert_of_ne_lost_of_selectsUniqueGlobalOptima
      hselect hxX hyLoss hzChoice hz_ne_y
  change z ∈ (select (insert x X)).chosenSet at hzNew
  rcases mem_chosenSet.mp hzNew with ⟨s, hslot⟩
  exact ⟨s, hslot,
    slotAtLeast_survivor_of_single_insert_loss hselect hyLoss hslot⟩

omit [DecidableEq σ] in
/--
Local contradiction behind the LAP variability proof: if `y` outranks `z` in
`z`'s old slot order, then `y` cannot be the lost applicant in an insertion
where `z` survives in a new slot with the same order as that old slot.
-/
theorem not_loss_of_survivor_same_slot_order
    {X : Finset α} {x y z : α} {oldSlot newSlot : σ} {w : α → σ → ℝ}
    {select : Finset α → Assignment α σ}
    (hselect : SelectsUniqueGlobalOptima w select)
    (hyLoss :
      y ∈ choiceRuleOfAssignment select X \
        choiceRuleOfAssignment select (insert x X))
    (hnewSlot : (select (insert x X)).matchSlot newSlot = some z)
    (hsame : SameSlotOrder w oldSlot newSlot)
    (hbelow : SlotBelow w oldSlot z y) :
    False := by
  have hnewAtLeast : SlotAtLeast w newSlot z y :=
    slotAtLeast_survivor_of_single_insert_loss hselect hyLoss hnewSlot
  have hnewBelow : SlotBelow w newSlot z y := (hsame z y).mp hbelow
  exact not_lt_of_ge hnewAtLeast hnewBelow

omit [DecidableEq σ] in
/--
Therefore, if a lower old chosen applicant survives an insertion that loses a
higher applicant in some slot order, the survivor is assigned after insertion
to a slot with a different induced order.
-/
theorem exists_survivor_new_slot_not_same_order_of_loss_of_slotBelow
    {X : Finset α} {x y z : α} {oldSlot : σ} {w : α → σ → ℝ}
    {select : Finset α → Assignment α σ}
    (hselect : SelectsUniqueGlobalOptima w select)
    (hxX : x ∉ X)
    (hyLoss :
      y ∈ choiceRuleOfAssignment select X \
        choiceRuleOfAssignment select (insert x X))
    (hzChoice : z ∈ choiceRuleOfAssignment select X)
    (hz_ne_y : z ≠ y)
    (hbelow : SlotBelow w oldSlot z y) :
    ∃ newSlot,
      (select (insert x X)).matchSlot newSlot = some z ∧
        ¬ SameSlotOrder w oldSlot newSlot := by
  rcases exists_slotAtLeast_survivor_of_ne_lost_of_selectsUniqueGlobalOptima
      hselect hxX hyLoss hzChoice hz_ne_y with
    ⟨newSlot, hnewSlot, _hnewAtLeast⟩
  refine ⟨newSlot, hnewSlot, ?_⟩
  intro hsame
  exact not_loss_of_survivor_same_slot_order
    hselect hyLoss hnewSlot hsame hbelow

omit [DecidableEq σ] in
/--
Loss/witness movement form: if `z` occupies `oldSlot` before an insertion and
`oldSlot` ranks `z` strictly below the lost applicant `y`, then in the same
insertion `z` moves across a directed edge to a slot with a different induced
order.
-/
theorem exists_forward_move_not_same_order_of_loss_of_slotBelow
    {X : Finset α} {x y z : α} {oldSlot : σ} {w : α → σ → ℝ}
    {select : Finset α → Assignment α σ}
    (hselect : SelectsUniqueGlobalOptima w select)
    (hxX : x ∉ X)
    (hyLoss :
      y ∈ choiceRuleOfAssignment select X \
        choiceRuleOfAssignment select (insert x X))
    (hzOldSlot : (select X).matchSlot oldSlot = some z)
    (hbelow : SlotBelow w oldSlot z y) :
    ∃ newSlot,
      forwardSlotLinked (select X) (select (insert x X)) oldSlot newSlot ∧
        ¬ SameSlotOrder w oldSlot newSlot := by
  have hzChoice : z ∈ choiceRuleOfAssignment select X := by
    change z ∈ (select X).chosenSet
    exact mem_chosenSet.mpr ⟨oldSlot, hzOldSlot⟩
  have hz_ne_y : z ≠ y := ne_of_slotBelow hbelow
  rcases exists_survivor_new_slot_not_same_order_of_loss_of_slotBelow
      hselect hxX hyLoss hzChoice hz_ne_y hbelow with
    ⟨newSlot, hnewSlot, hnotSame⟩
  exact ⟨newSlot, ⟨z, hzOldSlot, hnewSlot⟩, hnotSame⟩

omit [DecidableEq σ] in
/--
Path-packaged movement form: in a one-for-one LAP borderline loss, any old slot
whose occupant is below the lost applicant has a first directed successor that
leaves the old slot's order class and still reaches the lost slot.
-/
theorem exists_cross_order_successor_reaches_lost_of_slotBelow_lost
    {X : Finset α} {x y z : α} {root lost oldSlot : σ}
    {w : α → σ → ℝ} {select : Finset α → Assignment α σ}
    (hselect : SelectsUniqueGlobalOptima w select)
    (hxX : x ∉ X)
    (hyLoss :
      y ∈ choiceRuleOfAssignment select X \
        choiceRuleOfAssignment select (insert x X))
    (hroot : (select (insert x X)).matchSlot root = some x)
    (hlost : (select X).matchSlot lost = some y)
    (hzOldSlot : (select X).matchSlot oldSlot = some z)
    (hbelow : SlotBelow w oldSlot z y) :
    ∃ newSlot,
      forwardSlotLinked (select X) (select (insert x X)) oldSlot newSlot ∧
        ¬ SameSlotOrder w oldSlot newSlot ∧
          Relation.ReflTransGen
            (forwardSlotLinked (select X) (select (insert x X))) newSlot lost := by
  classical
  have hOldR :
      oldSlot ∈ forwardSlotReachSet (select X) (select (insert x X)) root :=
    old_slot_mem_forwardSlotReachSet_of_slotBelow_lost_of_lap_borderline_loss
      (select := select) hselect hxX hyLoss hroot hlost hzOldSlot hbelow
  have hpath :
      Relation.ReflTransGen
        (forwardSlotLinked (select X) (select (insert x X))) oldSlot lost :=
    forward_reaches_lost_of_mem_forwardSlotReachSet_of_lap_borderline_loss
      (select := select) hselect hxX hyLoss hroot hlost hOldR
  rcases exists_forward_move_not_same_order_of_loss_of_slotBelow
      hselect hxX hyLoss hzOldSlot hbelow with
    ⟨newSlot, hstep, hnotSame⟩
  have hold_ne_lost : oldSlot ≠ lost := by
    intro hold
    subst hold
    have hzy : z = y := Option.some.inj (hzOldSlot.symm.trans hlost)
    exact (ne_of_slotBelow hbelow) hzy
  rcases Relation.ReflTransGen.cases_head hpath with hsame | ⟨u, huStep, huLost⟩
  · exact (hold_ne_lost hsame).elim
  · have hu_eq : u = newSlot :=
      forwardSlotLinked_rightUnique_of_noDuplicate
        ((feasible_of_selectsUniqueGlobalOptima hselect (insert x X)).2)
        huStep hstep
    exact ⟨newSlot, hstep, hnotSame, by simpa [hu_eq] using huLost⟩

omit [DecidableEq α] [DecidableEq σ] [Fintype σ] in
/--
Along a directed path that starts outside an order class and ends inside it,
there is a first edge whose target is back inside the order class.
-/
theorem exists_forward_reentry_sameSlotOrder_of_path
    {A B : Assignment α σ} {w : α → σ → ℝ}
    {base start terminal : σ}
    (hstartNot : ¬ SameSlotOrder w base start)
    (hterminalSame : SameSlotOrder w base terminal)
    (hpath : Relation.ReflTransGen (forwardSlotLinked A B) start terminal) :
    ∃ u v,
      Relation.ReflTransGen (forwardSlotLinked A B) start u ∧
        forwardSlotLinked A B u v ∧
          ¬ SameSlotOrder w base u ∧
            SameSlotOrder w base v := by
  revert hstartNot
  refine Relation.ReflTransGen.head_induction_on hpath ?_ ?_
  · intro hnot
    exact False.elim (hnot hterminalSame)
  · intro a c hac hcb ih hnot
    by_cases hcSame : SameSlotOrder w base c
    · exact ⟨a, c, Relation.ReflTransGen.refl, hac, hnot, hcSame⟩
    · rcases ih hcSame with ⟨u, v, hcu, huv, huNot, hvSame⟩
      exact ⟨u, v, Relation.ReflTransGen.head hac hcu, huv, huNot, hvSame⟩

omit [DecidableEq σ] in
/--
Same-order endpoint form: if the old slot of a lower applicant and the old
slot of the lost applicant have the same induced order, then the fresh-to-lost
path has a concrete edge re-entering that order class.
-/
theorem exists_reentry_edge_sameSlotOrder_of_slotBelow_lost
    {X : Finset α} {x y z : α} {root lost oldSlot : σ}
    {w : α → σ → ℝ} {select : Finset α → Assignment α σ}
    (hselect : SelectsUniqueGlobalOptima w select)
    (hxX : x ∉ X)
    (hyLoss :
      y ∈ choiceRuleOfAssignment select X \
        choiceRuleOfAssignment select (insert x X))
    (hroot : (select (insert x X)).matchSlot root = some x)
    (hlost : (select X).matchSlot lost = some y)
    (hzOldSlot : (select X).matchSlot oldSlot = some z)
    (hbelow : SlotBelow w oldSlot z y)
    (hsameLost : SameSlotOrder w oldSlot lost) :
    ∃ u v,
      Relation.ReflTransGen
        (forwardSlotLinked (select X) (select (insert x X))) oldSlot u ∧
        forwardSlotLinked (select X) (select (insert x X)) u v ∧
          ¬ SameSlotOrder w oldSlot u ∧
            SameSlotOrder w oldSlot v := by
  rcases exists_cross_order_successor_reaches_lost_of_slotBelow_lost
      hselect hxX hyLoss hroot hlost hzOldSlot hbelow with
    ⟨newSlot, hstep, hnewNot, hnewLost⟩
  rcases exists_forward_reentry_sameSlotOrder_of_path
      (A := select X) (B := select (insert x X))
      (w := w) (base := oldSlot)
      hnewNot hsameLost hnewLost with
    ⟨u, v, hnewU, huv, huNot, hvSame⟩
  exact ⟨u, v, Relation.ReflTransGen.head hstep hnewU, huv, huNot, hvSame⟩

omit [DecidableEq α] [DecidableEq σ] in
/-- Repackage a directed path as membership in the finite forward reachability set. -/
theorem mem_forwardSlotReachSet_of_reflTransGen
    {A B : Assignment α σ} {root s : σ}
    (hpath : Relation.ReflTransGen (forwardSlotLinked A B) root s) :
    s ∈ forwardSlotReachSet A B root := by
  classical
  rw [forwardSlotReachSet]
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ s, hpath⟩

/--
Suffix-splice feasibility for the key LAP variability exchange.  If
`oldSlot -> newSlot` is an edge on the fresh-to-lost alternating path, then
splice the suffix starting at `newSlot` from the enlarged assignment into the
old assignment and put the lost applicant `y` into `oldSlot`.  The resulting
assignment is feasible for the old pool.
-/
theorem feasible_replaceSlot_spliceSlots_forwardSlotReachSet_successor
    {X : Finset α} {x y z : α} {A B : Assignment α σ}
    {oldSlot newSlot lost : σ}
    (hAfeas : Feasible X A)
    (hBfeas : Feasible (insert x X) B)
    (hyNotB : ¬ Assigned B y)
    (hlost : A.matchSlot lost = some y)
    (hzOldSlot : A.matchSlot oldSlot = some z)
    (hstep : forwardSlotLinked A B oldSlot newSlot)
    (hnew_lost :
      Relation.ReflTransGen (forwardSlotLinked A B) newSlot lost) :
    Feasible X
      (replaceSlot
        (spliceSlots A B (forwardSlotReachSet A B newSlot)) oldSlot y) := by
  classical
  let S : Finset σ := forwardSlotReachSet A B newSlot
  let C : Assignment α σ := spliceSlots A B S
  let E : Assignment α σ := replaceSlot C oldSlot y
  have hnewB : B.matchSlot newSlot = some z := by
    rcases hstep with ⟨a, hAold, hBnew⟩
    have haz : a = z := Option.some.inj (hAold.symm.trans hzOldSlot)
    simpa [haz] using hBnew
  have hzX : z ∈ X := hAfeas.1 hzOldSlot
  have hyX : y ∈ X := hAfeas.1 hlost
  have hLostS : lost ∈ S := by
    simpa [S] using
      mem_forwardSlotReachSet_of_reflTransGen
        (A := A) (B := B) (root := newSlot) hnew_lost
  have hAssignedFrom : AssignedFrom X E := by
    intro s a hs
    by_cases hsOld : s = oldSlot
    · subst s
      have hay : a = y := by
        simpa [E, replaceSlot] using hs.symm
      simpa [hay] using hyX
    · have hCs : C.matchSlot s = some a := by
        simpa [E, replaceSlot, Function.update_of_ne hsOld] using hs
      by_cases hsS : s ∈ S
      · have hBs : B.matchSlot s = some a := by
          simpa [C, S, spliceSlots, hsS] using hCs
        by_cases hsNew : s = newSlot
        · subst s
          have haz : a = z := Option.some.inj (hBs.symm.trans hnewB)
          simpa [haz] using hzX
        · rcases exists_forward_predecessor_of_mem_forwardSlotReachSet_of_ne
            (A := A) (B := B) (root := newSlot)
            (by simpa [S] using hsS) hsNew with
            ⟨p, b, _hpS, hAp, hBs'⟩
          have hab : a = b := Option.some.inj (hBs.symm.trans hBs')
          exact hAfeas.1 (by simpa [hab] using hAp)
      · have hAs : A.matchSlot s = some a := by
          simpa [C, S, spliceSlots, hsS] using hCs
        exact hAfeas.1 hAs
  have hNoDup : NoDuplicateApplicants E := by
    intro s t a hs ht
    by_cases hsOld : s = oldSlot
    · subst s
      by_cases htOld : t = oldSlot
      · exact htOld.symm
      · have hay : a = y := by
          simpa [E, replaceSlot] using hs.symm
        have hCt : C.matchSlot t = some a := by
          simpa [E, replaceSlot, Function.update_of_ne htOld] using ht
        have hCty : C.matchSlot t = some y := by
          simpa [hay] using hCt
        by_cases htS : t ∈ S
        · have hBty : B.matchSlot t = some y := by
            simpa [C, S, spliceSlots, htS] using hCty
          exact False.elim (hyNotB ⟨t, hBty⟩)
        · have hAty : A.matchSlot t = some y := by
            simpa [C, S, spliceSlots, htS] using hCty
          have htLost : t = lost := hAfeas.2 hAty hlost
          exact False.elim (htS (by simpa [htLost] using hLostS))
    · by_cases htOld : t = oldSlot
      · subst t
        have hay : a = y := by
          simpa [E, replaceSlot] using ht.symm
        have hCs : C.matchSlot s = some a := by
          simpa [E, replaceSlot, Function.update_of_ne hsOld] using hs
        have hCsy : C.matchSlot s = some y := by
          simpa [hay] using hCs
        by_cases hsS : s ∈ S
        · have hBsy : B.matchSlot s = some y := by
            simpa [C, S, spliceSlots, hsS] using hCsy
          exact False.elim (hyNotB ⟨s, hBsy⟩)
        · have hAsy : A.matchSlot s = some y := by
            simpa [C, S, spliceSlots, hsS] using hCsy
          have hsLost : s = lost := hAfeas.2 hAsy hlost
          exact False.elim (hsS (by simpa [hsLost] using hLostS))
      · have hCs : C.matchSlot s = some a := by
          simpa [E, replaceSlot, Function.update_of_ne hsOld] using hs
        have hCt : C.matchSlot t = some a := by
          simpa [E, replaceSlot, Function.update_of_ne htOld] using ht
        by_cases hsS : s ∈ S
        · have hBs : B.matchSlot s = some a := by
            simpa [C, S, spliceSlots, hsS] using hCs
          by_cases htS : t ∈ S
          · have hBt : B.matchSlot t = some a := by
              simpa [C, S, spliceSlots, htS] using hCt
            exact hBfeas.2 hBs hBt
          · have hAt : A.matchSlot t = some a := by
              simpa [C, S, spliceSlots, htS] using hCt
            by_cases hsNew : s = newSlot
            · subst s
              have haz : a = z := Option.some.inj (hBs.symm.trans hnewB)
              have htOld' : t = oldSlot :=
                hAfeas.2 (by simpa [haz] using hAt) hzOldSlot
              exact False.elim (htOld htOld')
            · rcases exists_forward_predecessor_of_mem_forwardSlotReachSet_of_ne
                (A := A) (B := B) (root := newSlot)
                (by simpa [S] using hsS) hsNew with
                ⟨p, b, hpS, hAp, hBs'⟩
              have hab : a = b := Option.some.inj (hBs.symm.trans hBs')
              have hpt : p = t :=
                hAfeas.2 hAp (by simpa [hab] using hAt)
              exact False.elim (htS (by simpa [hpt] using hpS))
        · have hAs : A.matchSlot s = some a := by
            simpa [C, S, spliceSlots, hsS] using hCs
          by_cases htS : t ∈ S
          · have hBt : B.matchSlot t = some a := by
              simpa [C, S, spliceSlots, htS] using hCt
            by_cases htNew : t = newSlot
            · subst t
              have haz : a = z := Option.some.inj (hBt.symm.trans hnewB)
              have hsOld' : s = oldSlot :=
                hAfeas.2 (by simpa [haz] using hAs) hzOldSlot
              exact False.elim (hsOld hsOld')
            · rcases exists_forward_predecessor_of_mem_forwardSlotReachSet_of_ne
                (A := A) (B := B) (root := newSlot)
                (by simpa [S] using htS) htNew with
                ⟨p, b, hpS, hAp, hBt'⟩
              have hab : a = b := Option.some.inj (hBt.symm.trans hBt')
              have hps : p = s :=
                hAfeas.2 hAp (by simpa [hab] using hAs)
              exact False.elim (hsS (by simpa [hps] using hpS))
          · have hAt : A.matchSlot t = some a := by
              simpa [C, S, spliceSlots, htS] using hCt
            exact hAfeas.2 hAs hAt
  exact ⟨hAssignedFrom, hNoDup⟩

/-- The suffix-splice replacement from
`feasible_replaceSlot_spliceSlots_forwardSlotReachSet_successor` fills capacity
whenever the old and enlarged assignments do. -/
theorem capacityFilling_replaceSlot_spliceSlots_forwardSlotReachSet_successor
    {X : Finset α} {x y : α} {A B : Assignment α σ}
    {oldSlot newSlot : σ}
    (hEfeas :
      Feasible X
        (replaceSlot
          (spliceSlots A B (forwardSlotReachSet A B newSlot)) oldSlot y))
    (hxX : x ∉ X)
    (hAfill : CapacityFilling X A)
    (hBfill : CapacityFilling (insert x X) B)
    (hlarge : Fintype.card σ ≤ X.card) :
    CapacityFilling X
      (replaceSlot
        (spliceSlots A B (forwardSlotReachSet A B newSlot)) oldSlot y) := by
  classical
  refine capacityFilling_of_feasible_of_fillsSlots_of_large hEfeas ?_ hlarge
  intro s
  by_cases hsOld : s = oldSlot
  · subst s
    exact ⟨y, by simp [replaceSlot]⟩
  · rcases fillsSlots_spliceSlots
      (A := A) (B := B) (R := forwardSlotReachSet A B newSlot)
      (hAfill.2 hlarge)
      (hBfill.2 (by
        rw [Finset.card_insert_of_notMem hxX]
        omega)) s with
      ⟨a, ha⟩
    exact ⟨a, by
      simpa [replaceSlot, Function.update_of_ne hsOld] using ha⟩

/--
Suffix-exchange contradiction: along a fresh-to-lost directed path, if the old
occupant of `oldSlot` moves to `newSlot` and is strictly below the lost
applicant in `oldSlot`'s weight order, rotating the suffix and putting the lost
applicant into `oldSlot` strictly improves the old optimum.
-/
theorem false_of_forward_suffix_exchange_slotBelow
    {X : Finset α} {x y z : α} {root lost oldSlot newSlot : σ}
    {w : α → σ → ℝ} {select : Finset α → Assignment α σ}
    (hselect : SelectsUniqueGlobalOptima w select)
    (hxX : x ∉ X)
    (hyLoss :
      y ∈ choiceRuleOfAssignment select X \
        choiceRuleOfAssignment select (insert x X))
    (hroot : (select (insert x X)).matchSlot root = some x)
    (hlost : (select X).matchSlot lost = some y)
    (hzOldSlot : (select X).matchSlot oldSlot = some z)
    (holdR :
      oldSlot ∈ forwardSlotReachSet (select X) (select (insert x X)) root)
    (hstep :
      forwardSlotLinked (select X) (select (insert x X)) oldSlot newSlot)
    (hnew_lost :
      Relation.ReflTransGen
        (forwardSlotLinked (select X) (select (insert x X))) newSlot lost)
    (hbelow : SlotBelow w oldSlot z y) :
    False := by
  classical
  let A : Assignment α σ := select X
  let B : Assignment α σ := select (insert x X)
  let S : Finset σ := forwardSlotReachSet A B newSlot
  let C : Assignment α σ := spliceSlots A B S
  let D : Assignment α σ := spliceSlots B A S
  let E : Assignment α σ := replaceSlot C oldSlot y
  have hAfeas : Feasible X A :=
    feasible_of_selectsUniqueGlobalOptima hselect X
  have hAfill : CapacityFilling X A :=
    capacityFilling_of_selectsUniqueGlobalOptima hselect X
  have hAopt : ObjectiveOptimal X w A :=
    objectiveOptimal_of_selectsUniqueGlobalOptima hselect X
  have hBfeas : Feasible (insert x X) B :=
    feasible_of_selectsUniqueGlobalOptima hselect (insert x X)
  have hBfill : CapacityFilling (insert x X) B :=
    capacityFilling_of_selectsUniqueGlobalOptima hselect (insert x X)
  have hBopt : ObjectiveOptimal (insert x X) w B :=
    objectiveOptimal_of_selectsUniqueGlobalOptima hselect (insert x X)
  have hqleX : Fintype.card σ ≤ X.card := by
    rcases choice_insert_eq_insert_erase_choice_of_lap_borderline_loss
        hselect hxX hyLoss with
      ⟨_hxChosen, hcardA, _hchoice⟩
    change A.chosenSet.card = Fintype.card σ at hcardA
    have hsub : A.chosenSet ⊆ X := chosenSet_subset_of_feasible hAfeas
    have hcard_le : A.chosenSet.card ≤ X.card := Finset.card_le_card hsub
    omega
  have hnotOldS : oldSlot ∉ S := by
    simpa [A, B, S] using
      not_mem_forwardSlotReachSet_successor_of_mem_fresh_root_reachSet
        (A := A) (B := B) (root := root) (oldSlot := oldSlot) (succ := newSlot)
        hxX hAfeas hroot (by simpa [A, B] using holdR) (by simpa [A, B] using hstep)
  have hyNotB : ¬ Assigned B y := by
    intro hyAssigned
    have hyNotNew : y ∉ B.chosenSet := by
      change y ∉ choiceRuleOfAssignment select (insert x X)
      exact (Finset.mem_sdiff.mp hyLoss).2
    exact hyNotNew (mem_chosenSet.mpr hyAssigned)
  have hEfeas : Feasible X E :=
    feasible_replaceSlot_spliceSlots_forwardSlotReachSet_successor
      (A := A) (B := B) (X := X) (x := x) (y := y) (z := z)
      (oldSlot := oldSlot) (newSlot := newSlot) (lost := lost)
      hAfeas hBfeas hyNotB
      (by simpa [A] using hlost)
      (by simpa [A] using hzOldSlot)
      (by simpa [A, B] using hstep)
      (by simpa [A, B] using hnew_lost)
  have hEfill : CapacityFilling X E :=
    capacityFilling_replaceSlot_spliceSlots_forwardSlotReachSet_successor
      (A := A) (B := B) (X := X) (x := x) (y := y)
      (oldSlot := oldSlot) (newSlot := newSlot)
      hEfeas hxX hAfill hBfill hqleX
  have hDfeas : Feasible (insert x X) D :=
    by
      simpa [A, B, S, D] using
        feasible_reverse_spliceSlots_forwardSlotReachSet_insert
          (A := A) (B := B) (X := X) (x := x) (root := newSlot)
          hAfeas hBfeas
  have hDfill : CapacityFilling (insert x X) D := by
    refine capacityFilling_of_feasible_of_fillsSlots_of_large hDfeas ?_ ?_
    · intro s
      simpa [A, B, S, D] using
        fillsSlots_spliceSlots
          (A := B) (B := A) (R := S)
          (hBfill.2 (by
            rw [Finset.card_insert_of_notMem hxX]
            omega))
          (hAfill.2 hqleX) s
    · rw [Finset.card_insert_of_notMem hxX]
      omega
  have hDleB : objective w D ≤ objective w B :=
    hBopt D hDfeas hDfill
  have hAleC : objective w A ≤ objective w C :=
    objective_le_spliceSlots_of_reverse_splice_le
      (w := w) (A := A) (B := B) (R := S) hDleB
  have hCslot : C.matchSlot oldSlot = some z := by
    simpa [C, S, spliceSlots, hnotOldS] using (by simpa [A] using hzOldSlot)
  have hCltE : objective w C < objective w E := by
    simpa [E] using
      objective_lt_replaceSlot_of_slot_weight_lt
        (w := w) (A := C) (s := oldSlot) (y := z) (x := y)
        hCslot hbelow
  have hAltE : objective w A < objective w E :=
    lt_of_le_of_lt hAleC hCltE
  have hEleA : objective w E ≤ objective w A :=
    hAopt E hEfeas hEfill
  exact not_lt_of_ge hEleA hAltE

/--
Stronger LAP variability kernel: if `y` is the old applicant lost after a
fresh insertion, then no old chosen occupant in any slot can be strictly below
`y` in that occupant's old slot order.
-/
theorem not_slotBelow_old_occupant_lost_of_lap_borderline_loss
    {X : Finset α} {x y z : α} {root lost oldSlot : σ}
    {w : α → σ → ℝ} {select : Finset α → Assignment α σ}
    (hselect : SelectsUniqueGlobalOptima w select)
    (hxX : x ∉ X)
    (hyLoss :
      y ∈ choiceRuleOfAssignment select X \
        choiceRuleOfAssignment select (insert x X))
    (hroot : (select (insert x X)).matchSlot root = some x)
    (hlost : (select X).matchSlot lost = some y)
    (hzOldSlot : (select X).matchSlot oldSlot = some z) :
    ¬ SlotBelow w oldSlot z y := by
  intro hbelow
  have holdR :
      oldSlot ∈ forwardSlotReachSet (select X) (select (insert x X)) root :=
    old_slot_mem_forwardSlotReachSet_of_slotBelow_lost_of_lap_borderline_loss
      (select := select) hselect hxX hyLoss hroot hlost hzOldSlot hbelow
  have hpath :
      Relation.ReflTransGen
        (forwardSlotLinked (select X) (select (insert x X))) oldSlot lost :=
    forward_reaches_lost_of_mem_forwardSlotReachSet_of_lap_borderline_loss
      (select := select) hselect hxX hyLoss hroot hlost holdR
  have hold_ne_lost : oldSlot ≠ lost := by
    intro hold
    subst hold
    have hzy : z = y := Option.some.inj (hzOldSlot.symm.trans hlost)
    exact (ne_of_slotBelow hbelow) hzy
  rcases Relation.ReflTransGen.cases_head hpath with hsame | ⟨newSlot, hstep, hnew_lost⟩
  · exact hold_ne_lost hsame
  · exact false_of_forward_suffix_exchange_slotBelow
      (select := select) hselect hxX hyLoss hroot hlost hzOldSlot holdR hstep
      hnew_lost hbelow

omit [DecidableEq σ] in
/--
Borderline form of the stronger LAP kernel: a borderline applicant cannot
strictly outrank any other old chosen occupant in that occupant's assigned
slot.
-/
theorem not_slotBelow_old_occupant_of_borderline_lost
    [Fintype α]
    {X : Finset α} {y z : α} {lost oldSlot : σ}
    {w : α → σ → ℝ} {select : Finset α → Assignment α σ}
    (hselect : SelectsUniqueGlobalOptima w select)
    (hyB : y ∈ AppliedModelingLib.FiniteChoice.borderlineSet
      (choiceRuleOfAssignment select) X)
    (hlost : (select X).matchSlot lost = some y)
    (hzOldSlot : (select X).matchSlot oldSlot = some z) :
    ¬ SlotBelow w oldSlot z y := by
  classical
  rcases exists_loss_witness_of_mem_borderlineSet_choiceRuleOfAssignment
      (select := select) (X := X) (y := y) hyB with
    ⟨x, hyLoss⟩
  have hyChoice : y ∈ choiceRuleOfAssignment select X :=
    (Finset.mem_sdiff.mp hyLoss).1
  have hxX : x ∉ X := by
    intro hxX
    have hsame :
        choiceRuleOfAssignment select (insert x X) =
          choiceRuleOfAssignment select X := by
      rw [Finset.insert_eq_of_mem hxX]
    exact (Finset.mem_sdiff.mp hyLoss).2 (by simpa [hsame] using hyChoice)
  rcases choice_insert_eq_insert_erase_choice_of_lap_borderline_loss
      hselect hxX hyLoss with
    ⟨hxChosen, _hcard, _hchoice⟩
  change x ∈ (select (insert x X)).chosenSet at hxChosen
  rcases mem_chosenSet.mp hxChosen with ⟨root, hroot⟩
  exact
    not_slotBelow_old_occupant_lost_of_lap_borderline_loss
      (select := select) hselect hxX hyLoss hroot hlost hzOldSlot

/--
Same-order LAP borderline injectivity.  Under slotwise no ties, two
borderline applicants assigned to slots with the same induced applicant order
must be the same applicant.
-/
theorem same_slot_order_borderline_injective_of_selectsUniqueGlobalOptima_of_slotNoTies
    [Fintype α]
    {X : Finset α} {y z : α} {sy sz : σ}
    {w : α → σ → ℝ} {select : Finset α → Assignment α σ}
    (hselect : SelectsUniqueGlobalOptima w select)
    (hnoTies : ∀ s : σ, SlotNoTies w s)
    (hyB : y ∈ AppliedModelingLib.FiniteChoice.borderlineSet
      (choiceRuleOfAssignment select) X)
    (hzB : z ∈ AppliedModelingLib.FiniteChoice.borderlineSet
      (choiceRuleOfAssignment select) X)
    (hsy : (select X).matchSlot sy = some y)
    (hsz : (select X).matchSlot sz = some z)
    (hsame : SameSlotOrder w sy sz) :
    y = z := by
  by_contra hyz
  have hzy : z ≠ y := by
    intro h
    exact hyz h.symm
  rcases slotBelow_or_slotBelow_of_sameSlotOrder_of_noTies
      (w := w) (s := sz) (t := sy) (a := z) (b := y)
      hsame.symm (hnoTies sz) hzy with hzyBelow | hyzBelow
  · exact
      (not_slotBelow_old_occupant_of_borderline_lost
        (select := select) (X := X) (y := y) (z := z)
        (lost := sy) (oldSlot := sz)
        hselect hyB hsy hsz) hzyBelow
  · exact
      (not_slotBelow_old_occupant_of_borderline_lost
        (select := select) (X := X) (y := z) (z := y)
        (lost := sz) (oldSlot := sy)
        hselect hzB hsz hsy) hyzBelow

/--
Main LAP distinct-order variability theorem.  If `classOf` only groups slots
that induce the same strict applicant order, and every slot order has no ties,
then variability is bounded by the number of represented slot-order classes.
-/
theorem variabilityAtMost_choiceRuleOfAssignment_of_distinct_slot_orders
    [Fintype α] {κ : Type*} [DecidableEq κ]
    {w : α → σ → ℝ} {select : Finset α → Assignment α σ} {classOf : σ → κ}
    (hselect : SelectsUniqueGlobalOptima w select)
    (hnoTies : ∀ s : σ, SlotNoTies w s)
    (hclass : ∀ {s t : σ}, classOf s = classOf t → SameSlotOrder w s t) :
    AppliedModelingLib.FiniteChoice.VariabilityAtMost
      ((Finset.univ : Finset σ).image classOf).card
      (choiceRuleOfAssignment select) := by
  exact
    variabilityAtMost_choiceRuleOfAssignment_of_same_slot_order_borderline_injective
      (select := select) (classOf := classOf) hclass
      (fun hyB hzB hsy hsz hsame =>
        same_slot_order_borderline_injective_of_selectsUniqueGlobalOptima_of_slotNoTies
          (select := select) hselect hnoTies hyB hzB hsy hsz hsame)

omit [DecidableEq σ] in
/--
Borderline/witness form of the cross-order movement lemma: if a borderline
old applicant `y` strictly outranks another old chosen applicant `z` in
`oldSlot`'s order, then the one-insertion witness for losing `y` assigns `z`
to a slot with a different induced order.
-/
theorem exists_survivor_new_slot_not_same_order_of_borderline_slotBelow
    [Fintype α]
    {X : Finset α} {y z : α} {oldSlot : σ} {w : α → σ → ℝ}
    {select : Finset α → Assignment α σ}
    (hselect : SelectsUniqueGlobalOptima w select)
    (hyB : y ∈ AppliedModelingLib.FiniteChoice.borderlineSet
      (choiceRuleOfAssignment select) X)
    (hzChoice : z ∈ choiceRuleOfAssignment select X)
    (hz_ne_y : z ≠ y)
    (hbelow : SlotBelow w oldSlot z y) :
    ∃ x newSlot,
      x ∉ X ∧
        (select (insert x X)).matchSlot newSlot = some z ∧
          ¬ SameSlotOrder w oldSlot newSlot := by
  rcases exists_loss_witness_of_mem_borderlineSet_choiceRuleOfAssignment
      (select := select) (X := X) (y := y) hyB with
    ⟨x, hyLoss⟩
  have hyChoice : y ∈ choiceRuleOfAssignment select X :=
    (Finset.mem_sdiff.mp hyLoss).1
  have hxX : x ∉ X := by
    intro hxX
    have hsame :
        choiceRuleOfAssignment select (insert x X) =
          choiceRuleOfAssignment select X := by
      rw [Finset.insert_eq_of_mem hxX]
    exact (Finset.mem_sdiff.mp hyLoss).2 (by simpa [hsame] using hyChoice)
  rcases exists_survivor_new_slot_not_same_order_of_loss_of_slotBelow
      hselect hxX hyLoss hzChoice hz_ne_y hbelow with
    ⟨newSlot, hnewSlot, hnotSame⟩
  exact ⟨x, newSlot, hxX, hnewSlot, hnotSame⟩

omit [DecidableEq σ] in
/--
Movement form of the previous lemma: if `z` occupied `oldSlot` before the
insertion, then the witness insertion moves `z` along a forward slot edge to a
new slot with a different induced order.
-/
theorem exists_forward_move_not_same_order_of_borderline_slotBelow
    [Fintype α]
    {X : Finset α} {y z : α} {oldSlot : σ} {w : α → σ → ℝ}
    {select : Finset α → Assignment α σ}
    (hselect : SelectsUniqueGlobalOptima w select)
    (hyB : y ∈ AppliedModelingLib.FiniteChoice.borderlineSet
      (choiceRuleOfAssignment select) X)
    (hzOldSlot : (select X).matchSlot oldSlot = some z)
    (hz_ne_y : z ≠ y)
    (hbelow : SlotBelow w oldSlot z y) :
    ∃ x newSlot,
      x ∉ X ∧
        forwardSlotLinked (select X) (select (insert x X)) oldSlot newSlot ∧
          ¬ SameSlotOrder w oldSlot newSlot := by
  have hzChoice : z ∈ choiceRuleOfAssignment select X := by
    change z ∈ (select X).chosenSet
    exact mem_chosenSet.mpr ⟨oldSlot, hzOldSlot⟩
  rcases exists_survivor_new_slot_not_same_order_of_borderline_slotBelow
      hselect hyB hzChoice hz_ne_y hbelow with
    ⟨x, newSlot, hxX, hnewSlot, hnotSame⟩
  exact ⟨x, newSlot, hxX, ⟨z, hzOldSlot, hnewSlot⟩, hnotSame⟩

/--
If an offered applicant strictly outranks the current occupant of a slot, then
that applicant must be assigned somewhere in a feasible locally optimal
assignment.
-/
theorem assigned_of_slotBelow_occupant_of_noProfitableOneSlotSwap_of_feasible
    {X : Finset α} {w : α → σ → ℝ} {A : Assignment α σ}
    (hopt : NoProfitableOneSlotSwap X w A)
    (hfeas : Feasible X A)
    {s : σ} {y x : α}
    (hslot : A.matchSlot s = some y)
    (hxX : x ∈ X)
    (hbelow : SlotBelow w s y x) :
    Assigned A x := by
  by_contra hxAssigned
  exact not_slotBelow_of_noProfitableOneSlotSwap hopt hslot
    ⟨hxX, hxAssigned⟩
    (feasible_replaceSlot_of_feasible_of_rejected hfeas ⟨hxX, hxAssigned⟩)
    hbelow

/--
No rejected applicant is strictly above the current occupant of any assigned
slot in a feasible locally optimal assignment.
-/
theorem not_exists_rejected_slotBelow_of_noProfitableOneSlotSwap_of_feasible
    {X : Finset α} {w : α → σ → ℝ} {A : Assignment α σ}
    (hopt : NoProfitableOneSlotSwap X w A)
    (hfeas : Feasible X A) :
    ¬ ∃ s y x, A.matchSlot s = some y ∧ Rejected X A x ∧ SlotBelow w s y x := by
  rintro ⟨s, y, x, hslot, hrej, hbelow⟩
  exact not_slotBelow_of_noProfitableOneSlotSwap hopt hslot hrej
    (feasible_replaceSlot_of_feasible_of_rejected hfeas hrej) hbelow

omit [DecidableEq σ] in
/--
If all slots induce the same strict applicant ordering, then the
assignment-induced choice rule is exactly top-q selection in that common order.
The order convention is that smaller applicants in the ambient `LinearOrder`
have higher slot weight.
-/
theorem choiceRuleOfAssignment_eq_linearTopQChoice_of_common_slot_order
    [LinearOrder α]
    {w : α → σ → ℝ} {select : Finset α → Assignment α σ}
    (hselect : SelectsUniqueGlobalOptima w select)
    (horder : ∀ s a b, a < b ↔ w b s < w a s) :
    choiceRuleOfAssignment select =
      AppliedModelingLib.FiniteChoice.linearTopQChoice (α := α) (Fintype.card σ) := by
  classical
  funext X
  let C : AppliedModelingLib.FiniteChoice.ChoiceRule α := choiceRuleOfAssignment select
  have hfeasC : AppliedModelingLib.FiniteChoice.Feasible C :=
    feasible_choiceRuleOfAssignment_of_selectsUniqueGlobalOptima hselect
  have hacceptC : AppliedModelingLib.FiniteChoice.QAcceptant (Fintype.card σ) C :=
    qAcceptant_choiceRuleOfAssignment_of_selectsUniqueGlobalOptima hselect
  by_cases hsmall : X.card ≤ Fintype.card σ
  · have hCX : C X = X :=
      AppliedModelingLib.FiniteChoice.QAcceptant.eq_of_card_le hfeasC hacceptC hsmall
    have hTop :
        AppliedModelingLib.FiniteChoice.linearTopQChoice (α := α) (Fintype.card σ) X = X := by
      by_cases hqle : Fintype.card σ ≤ X.card
      · have hcard : X.card = Fintype.card σ := le_antisymm hsmall hqle
        exact AppliedModelingLib.FiniteChoice.linearTopQChoice_eq_of_card_of_forall_lt
          (α := α) (q := Fintype.card σ) (X := X) (S := X)
          (fun _ hx => hx) hcard (by
            intro s hs y hy hyNot
            exact False.elim (hyNot hy))
      · unfold AppliedModelingLib.FiniteChoice.linearTopQChoice
        rw [dif_neg hqle]
    simp [C, hCX, hTop]
  · have hlarge : Fintype.card σ ≤ X.card := by omega
    have hCXcard : (C X).card = Fintype.card σ := by
      simpa [C, Nat.min_eq_left hlarge] using hacceptC X
    have hsub : C X ⊆ X := hfeasC X
    have hbeats :
        ∀ s, s ∈ C X → ∀ y, y ∈ X → y ∉ C X → s < y := by
      intro a haC y hyX hyNotC
      change a ∈ (select X).chosenSet at haC
      change y ∉ (select X).chosenSet at hyNotC
      rcases mem_chosenSet.mp haC with ⟨slot, hslot⟩
      have hrej : Rejected X (select X) y := by
        refine ⟨hyX, ?_⟩
        intro hyAssigned
        exact hyNotC (mem_chosenSet.mpr hyAssigned)
      have hslotAtLeast : SlotAtLeast w slot a y :=
        slotAtLeast_rejected_of_noProfitableOneSlotSwap_of_feasible
          (noProfitableOneSlotSwap_of_objectiveOptimal
            (objectiveOptimal_of_selectsUniqueGlobalOptima hselect X)
            (capacityFilling_of_selectsUniqueGlobalOptima hselect X))
          (feasible_of_selectsUniqueGlobalOptima hselect X)
          hslot hrej
      by_contra hnotlt
      have hy_ne_a : y ≠ a := by
        intro hya
        subst hya
        exact hyNotC haC
      have hya_lt : y < a := lt_of_le_of_ne (le_of_not_gt hnotlt) hy_ne_a
      have hweight : w a slot < w y slot := (horder slot y a).mp hya_lt
      exact not_lt_of_ge hslotAtLeast hweight
    exact (AppliedModelingLib.FiniteChoice.linearTopQChoice_eq_of_card_of_forall_lt
      (α := α) (q := Fintype.card σ) (X := X) (S := C X)
      hsub hCXcard hbeats).symm

omit [DecidableEq σ] in
/-- A unique-global-optimum LAP whose slots share one strict order is q-representative. -/
theorem qRepresentative_choiceRuleOfAssignment_of_selectsUniqueGlobalOptima_of_common_slot_order
    [LinearOrder α]
    {w : α → σ → ℝ} {select : Finset α → Assignment α σ}
    (hselect : SelectsUniqueGlobalOptima w select)
    (horder : ∀ s a b, a < b ↔ w b s < w a s) :
    AppliedModelingLib.FiniteChoice.QRepresentative
      (Fintype.card σ) (choiceRuleOfAssignment select) := by
  rw [choiceRuleOfAssignment_eq_linearTopQChoice_of_common_slot_order
    hselect horder]
  exact AppliedModelingLib.FiniteChoice.linearTopQChoice_qRepresentative
    (α := α) (Fintype.card σ)

omit [DecidableEq σ] in
/--
A unique-global-optimum LAP whose slots all induce one strict order has
variability at most one.
-/
theorem variabilityAtMost_one_choiceRuleOfAssignment_of_selectsUniqueGlobalOptima_of_common_slot_order
    [Fintype α] [LinearOrder α]
    {w : α → σ → ℝ} {select : Finset α → Assignment α σ}
    (hselect : SelectsUniqueGlobalOptima w select)
    (horder : ∀ s a b, a < b ↔ w b s < w a s) :
    AppliedModelingLib.FiniteChoice.VariabilityAtMost 1
      (choiceRuleOfAssignment select) := by
  exact AppliedModelingLib.FiniteChoice.variabilityAtMost_one_of_feasible_of_qRepresentative
    (C := choiceRuleOfAssignment select)
    (feasible_choiceRuleOfAssignment_of_selectsUniqueGlobalOptima hselect)
    (qRepresentative_choiceRuleOfAssignment_of_selectsUniqueGlobalOptima_of_common_slot_order
      hselect horder)

end Assignment

end LAP

end DGD26AdmissionsPredictability
