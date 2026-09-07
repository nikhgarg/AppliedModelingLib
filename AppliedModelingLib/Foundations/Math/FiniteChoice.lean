import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic

/-!
# Finite Choice Functions

Reusable finite-set choice-function primitives for capacity-constrained
admissions and related social-choice models.

The core object is a choice rule `Finset α → Finset α`.  Paper-facing
formalizations should usually pair the structural predicates below with
`Feasible`, which records the choice-function convention that selected
alternatives come from the offered set.
-/

namespace AppliedModelingLib
namespace FiniteChoice

variable {α : Type*} [DecidableEq α]

/-- A finite choice rule maps every finite feasible set to a finite chosen set. -/
abbrev ChoiceRule (α : Type*) [DecidableEq α] := Finset α → Finset α

/-- Feasibility: the chosen set is always contained in the offered set. -/
def Feasible (C : ChoiceRule α) : Prop :=
  ∀ X, C X ⊆ X

/-- `q`-acceptance: choose as many alternatives as possible, up to capacity `q`. -/
def QAcceptant (q : ℕ) (C : ChoiceRule α) : Prop :=
  ∀ X, (C X).card = min q X.card

/-- Substitutability: shrinking the offered set does not hurt retained chosen elements. -/
def Substitutable (C : ChoiceRule α) : Prop :=
  ∀ {X₁ X₂}, X₁ ⊆ X₂ → X₁ ∩ C X₂ ⊆ C X₁

/-- Monotonicity: expanding the offered set preserves every earlier choice. -/
def Monotonic (C : ChoiceRule α) : Prop :=
  ∀ {X₁ X₂}, X₁ ⊆ X₂ → C X₁ ⊆ C X₂

/-- Consistency: removing rejected alternatives does not change the chosen set. -/
def Consistent (C : ChoiceRule α) : Prop :=
  ∀ {X₁ X₂}, C X₂ ⊆ X₁ → X₁ ⊆ X₂ → C X₂ = C X₁

/--
Independence: each alternative is either always chosen whenever available or
always rejected whenever available.
-/
def Independent (C : ChoiceRule α) : Prop :=
  ∀ x, (∀ X, x ∈ X → x ∈ C X) ∨ (∀ X, x ∈ X → x ∉ C X)

/-- The rejection-to-acceptance term in finite choice distance. -/
def choiceGainTerm (C : ChoiceRule α) (X₁ X₂ : Finset α) : ℕ :=
  ((X₁ ∩ C X₂) \ C X₁).card

/-- The acceptance-to-rejection term in finite choice distance. -/
def choiceLossTerm (C : ChoiceRule α) (X₁ X₂ : Finset α) : ℕ :=
  (C X₁ \ C X₂).card

/--
Choice distance: the number of existing decisions whose label changes when the
offered set expands from `X₁` to `X₂`.
-/
def choiceDistance (C : ChoiceRule α) (X₁ X₂ : Finset α) : ℕ :=
  choiceGainTerm C X₁ X₂ + choiceLossTerm C X₁ X₂

/-- `d`-instability for one fresh added alternative. -/
def DUnstable (d : ℕ) (C : ChoiceRule α) : Prop :=
  ∀ X x, x ∉ X → choiceDistance C X (insert x X) ≤ d

/-- Tight `d`-instability: `d` is the least one-step instability bound. -/
def TightlyDUnstable (d : ℕ) (C : ChoiceRule α) : Prop :=
  DUnstable d C ∧ ∀ k, k < d → ¬ DUnstable k C

/-- A `d`-unstable rule with an exact one-step distance-`d` witness is tightly `d`-unstable. -/
theorem tightlyDUnstable_of_dUnstable_of_choiceDistance_witness
    {d : ℕ} {C : ChoiceRule α}
    (hunstable : DUnstable d C)
    (hwitness :
      ∃ X x, x ∉ X ∧ choiceDistance C X (insert x X) = d) :
    TightlyDUnstable d C := by
  constructor
  · exact hunstable
  · intro k hk hsmall
    rcases hwitness with ⟨X, x, hx, hdist⟩
    have hle : d ≤ k := by
      simpa [hdist] using hsmall X x hx
    omega

/-- Zero instability for arbitrary nested offered sets. -/
def ZeroUnstable (C : ChoiceRule α) : Prop :=
  ∀ {X₁ X₂}, X₁ ⊆ X₂ → choiceDistance C X₁ X₂ = 0

/-- A strict total order in the asymmetric/transitive/complete sense. -/
def StrictTotalOrder (r : α → α → Prop) : Prop :=
  (∀ x, ¬ r x x) ∧
    (∀ {x y z}, r x y → r y z → r x z) ∧
      (∀ {x y}, x ≠ y → r x y ∨ r y x)

/--
`C` is represented by a single priority order if it chooses only offered
applicants, is q-acceptant, and every chosen applicant is above every rejected
applicant in each finite pool.
-/
def QRepresentative (q : ℕ) (C : ChoiceRule α) : Prop :=
  ∃ r : α → α → Prop,
    StrictTotalOrder r ∧ Feasible C ∧ QAcceptant q C ∧
      ∀ {X x y}, x ∈ C X → y ∈ X → y ∉ C X → r x y

/--
Sequential composition of choice rules: run the first rule on the current
remaining set, remove its chosen alternatives, then continue with the rest.
-/
def sequentialComposition : List (ChoiceRule α) → ChoiceRule α
  | [] => fun _ => ∅
  | C :: Cs =>
      fun X =>
        let chosen := C X
        chosen ∪ sequentialComposition Cs (X \ chosen)

/-- Borderline admits displaced by some single added applicant. -/
def borderlineSet [Fintype α] (C : ChoiceRule α) (X : Finset α) : Finset α :=
  Finset.univ.biUnion fun x => C X \ C (insert x X)

/-- There is at least one one-step displacement of an existing chosen element. -/
def HasDisplacement (C : ChoiceRule α) : Prop :=
  ∃ X x y, x ∉ X ∧ y ∈ C X ∧ y ∉ C (insert x X)

/-- Waitlisted rejections newly accepted after removing some current applicant. -/
def waitlistedSet [Fintype α] (C : ChoiceRule α) (X : Finset α) : Finset α :=
  X.biUnion fun x => C (X.erase x) \ C X

/-- Main-text variability upper-bound form. -/
def VariabilityAtMost [Fintype α] (m : ℕ) (C : ChoiceRule α) : Prop :=
  ∀ X, (borderlineSet C X).card ≤ m

/-- Main-text exact variability, stated as an upper bound with a witnessing pool. -/
def VariabilityExactly [Fintype α] (m : ℕ) (C : ChoiceRule α) : Prop :=
  VariabilityAtMost m C ∧ ∃ X, (borderlineSet C X).card = m

/-- Appendix general variability upper-bound form. -/
def GeneralVariabilityAtMost [Fintype α] (m : ℕ) (C : ChoiceRule α) : Prop :=
  ∀ X, (borderlineSet C X).card ≤ m ∧ (waitlistedSet C X).card ≤ m

/-- Appendix exact general variability, stated by upper bounds and a witnessing side. -/
def GeneralVariabilityExactly [Fintype α] (m : ℕ) (C : ChoiceRule α) : Prop :=
  GeneralVariabilityAtMost m C ∧
    ((∃ X, (borderlineSet C X).card = m) ∨
      (∃ X, (waitlistedSet C X).card = m))

/-! ## Basic set-containment lemmas -/

/-- Every borderline applicant is selected before the fresh applicant is added. -/
theorem borderlineSet_subset_choice [Fintype α]
    (C : ChoiceRule α) (X : Finset α) :
    borderlineSet C X ⊆ C X := by
  classical
  intro y hy
  rw [borderlineSet] at hy
  rcases Finset.mem_biUnion.mp hy with ⟨x, _hx, hloss⟩
  exact (Finset.mem_sdiff.mp hloss).1

/-- The borderline set is no larger than the original chosen set. -/
theorem borderlineSet_card_le_choice_card [Fintype α]
    (C : ChoiceRule α) (X : Finset α) :
    (borderlineSet C X).card ≤ (C X).card :=
  Finset.card_le_card (borderlineSet_subset_choice C X)

set_option linter.unusedSectionVars false in
/-- The irreflexive projection from a `StrictTotalOrder`. -/
theorem StrictTotalOrder.irrefl {r : α → α → Prop}
    (h : StrictTotalOrder r) (x : α) :
    ¬ r x x :=
  h.1 x

set_option linter.unusedSectionVars false in
/-- The transitive projection from a `StrictTotalOrder`. -/
theorem StrictTotalOrder.trans {r : α → α → Prop}
    (h : StrictTotalOrder r) {x y z : α} :
    r x y → r y z → r x z :=
  h.2.1

set_option linter.unusedSectionVars false in
/-- The complete projection from a `StrictTotalOrder`. -/
theorem StrictTotalOrder.total {r : α → α → Prop}
    (h : StrictTotalOrder r) {x y : α} :
    x ≠ y → r x y ∨ r y x :=
  h.2.2

set_option linter.unusedSectionVars false in
/-- A strict total order is asymmetric. -/
theorem StrictTotalOrder.asymm {r : α → α → Prop}
    (h : StrictTotalOrder r) {x y : α} (hxy : r x y) :
    ¬ r y x := by
  intro hyx
  exact h.irrefl x (h.trans hxy hyx)

set_option linter.unusedSectionVars false in
/-- Related alternatives in a strict total order are distinct. -/
theorem StrictTotalOrder.ne_of_rel {r : α → α → Prop}
    (h : StrictTotalOrder r) {x y : α} (hxy : r x y) :
    x ≠ y := by
  intro hxy_eq
  subst y
  exact h.irrefl x hxy

/-- A q-representative rule is q-acceptant by definition. -/
theorem QRepresentative.qAcceptant {q : ℕ} {C : ChoiceRule α}
    (hrep : QRepresentative q C) :
    QAcceptant q C := by
  rcases hrep with ⟨_, _, _, haccept, _⟩
  exact haccept

/-! ## Priority-order choice rules -/

section LinearTopQChoice

variable [LinearOrder α]

/--
The q-acceptant rule that chooses the first `q` elements of the offered set in
the ambient linear order, or everyone if the pool has size below capacity.
-/
noncomputable def linearTopQChoice (q : ℕ) : ChoiceRule α :=
  fun X =>
    if h : q ≤ X.card then
      Finset.univ.image
        (fun i : Fin q =>
          ((X.orderIsoOfFin (by rfl)
            ⟨i.1, lt_of_lt_of_le i.2 h⟩ : X) : α))
    else
      X

/-- The linear top-q choice rule only chooses offered alternatives. -/
theorem linearTopQChoice_feasible (q : ℕ) :
    Feasible (linearTopQChoice (α := α) q) := by
  classical
  intro X x hx
  unfold linearTopQChoice at hx
  split_ifs at hx with h
  · rcases Finset.mem_image.mp hx with ⟨i, _hi, rfl⟩
    exact ((X.orderIsoOfFin (by rfl)
      ⟨i.1, lt_of_lt_of_le i.2 h⟩ : X)).2
  · exact hx

/-- The linear top-q choice rule chooses exactly `min q X.card` alternatives. -/
theorem linearTopQChoice_qAcceptant (q : ℕ) :
    QAcceptant q (linearTopQChoice (α := α) q) := by
  classical
  intro X
  unfold linearTopQChoice
  by_cases h : q ≤ X.card
  · rw [dif_pos h]
    have hinj : Function.Injective
        (fun i : Fin q =>
          ((X.orderIsoOfFin (by rfl)
            ⟨i.1, lt_of_lt_of_le i.2 h⟩ : X) : α)) := by
      intro i j hij
      have hsub :
          (X.orderIsoOfFin (by rfl)
              ⟨i.1, lt_of_lt_of_le i.2 h⟩ : X) =
            (X.orderIsoOfFin (by rfl)
              ⟨j.1, lt_of_lt_of_le j.2 h⟩ : X) := by
        exact Subtype.ext hij
      have hfin :
          (⟨i.1, lt_of_lt_of_le i.2 h⟩ : Fin X.card) =
            ⟨j.1, lt_of_lt_of_le j.2 h⟩ := by
        exact (X.orderIsoOfFin (by rfl)).injective hsub
      exact Fin.ext (congrArg (fun k : Fin X.card => k.1) hfin)
    rw [Finset.card_image_of_injective _ hinj]
    simp [Nat.min_eq_left h]
  · rw [dif_neg h]
    have hle : X.card ≤ q := Nat.le_of_not_ge h
    rw [Nat.min_eq_right hle]

/--
Concrete priority property for the linear top-q rule: every chosen applicant
precedes every rejected offered applicant in the ambient order.
-/
theorem linearTopQChoice_priority (q : ℕ)
    {X : Finset α} {x y : α}
    (hx : x ∈ linearTopQChoice q X)
    (hyX : y ∈ X)
    (hyNot : y ∉ linearTopQChoice q X) :
    x < y := by
  classical
  unfold linearTopQChoice at hx hyNot
  by_cases h : q ≤ X.card
  · rw [dif_pos h] at hx hyNot
    rcases Finset.mem_image.mp hx with ⟨i, _hi, rfl⟩
    have hySubtype : (⟨y, hyX⟩ : X) ∉
        Finset.univ.image
          (fun i : Fin q =>
            X.orderIsoOfFin (by rfl)
              ⟨i.1, lt_of_lt_of_le i.2 h⟩) := by
      intro hyImage
      apply hyNot
      rcases Finset.mem_image.mp hyImage with ⟨j, hj, hjEq⟩
      exact Finset.mem_image.mpr ⟨j, hj, congrArg Subtype.val hjEq⟩
    have hq_le_yidx :
        q ≤ ((X.orderIsoOfFin (by rfl)).symm ⟨y, hyX⟩).1 := by
      by_contra hlt
      have hlt' : ((X.orderIsoOfFin (by rfl)).symm ⟨y, hyX⟩).1 < q :=
        Nat.lt_of_not_ge hlt
      have hyImage : (⟨y, hyX⟩ : X) ∈
          Finset.univ.image
            (fun i : Fin q =>
              X.orderIsoOfFin (by rfl)
                ⟨i.1, lt_of_lt_of_le i.2 h⟩) := by
        refine Finset.mem_image.mpr ⟨⟨_, hlt'⟩, Finset.mem_univ _, ?_⟩
        simp
      exact hySubtype hyImage
    have hi_lt_yidx :
        (⟨i.1, lt_of_lt_of_le i.2 h⟩ : Fin X.card) <
          (X.orderIsoOfFin (by rfl)).symm ⟨y, hyX⟩ := by
      exact Fin.mk_lt_mk.mpr (lt_of_lt_of_le i.2 hq_le_yidx)
    have hsub_lt :
        (X.orderIsoOfFin (by rfl)
          ⟨i.1, lt_of_lt_of_le i.2 h⟩ : X) < ⟨y, hyX⟩ := by
      simpa using
        (X.orderIsoOfFin (by rfl)).strictMono hi_lt_yidx
    exact hsub_lt
  · rw [dif_neg h] at hyNot
    exact False.elim (hyNot hyX)

/-- The linear top-q choice rule is represented by the ambient linear order. -/
theorem linearTopQChoice_qRepresentative (q : ℕ) :
    QRepresentative q (linearTopQChoice (α := α) q) := by
  classical
  refine ⟨(· < ·), ?_, linearTopQChoice_feasible (α := α) q,
    linearTopQChoice_qAcceptant (α := α) q, ?_⟩
  · constructor
    · intro x
      exact lt_irrefl x
    · constructor
      · intro x y z hxy hyz
        exact lt_trans hxy hyz
      · intro x y hxy
        exact lt_or_gt_of_ne hxy
  · intro X x y hx hyX hyNot
    unfold linearTopQChoice at hx hyNot
    by_cases h : q ≤ X.card
    · rw [dif_pos h] at hx hyNot
      rcases Finset.mem_image.mp hx with ⟨i, _hi, rfl⟩
      have hySubtype : (⟨y, hyX⟩ : X) ∉
          Finset.univ.image
            (fun i : Fin q =>
              X.orderIsoOfFin (by rfl)
                ⟨i.1, lt_of_lt_of_le i.2 h⟩) := by
        intro hyImage
        apply hyNot
        rcases Finset.mem_image.mp hyImage with ⟨j, hj, hjEq⟩
        exact Finset.mem_image.mpr ⟨j, hj, congrArg Subtype.val hjEq⟩
      have hq_le_yidx :
          q ≤ ((X.orderIsoOfFin (by rfl)).symm ⟨y, hyX⟩).1 := by
        by_contra hlt
        have hlt' : ((X.orderIsoOfFin (by rfl)).symm ⟨y, hyX⟩).1 < q :=
          Nat.lt_of_not_ge hlt
        have hyImage : (⟨y, hyX⟩ : X) ∈
            Finset.univ.image
              (fun i : Fin q =>
                X.orderIsoOfFin (by rfl)
                  ⟨i.1, lt_of_lt_of_le i.2 h⟩) := by
          refine Finset.mem_image.mpr ⟨⟨_, hlt'⟩, Finset.mem_univ _, ?_⟩
          simp
        exact hySubtype hyImage
      have hi_lt_yidx :
          (⟨i.1, lt_of_lt_of_le i.2 h⟩ : Fin X.card) <
            (X.orderIsoOfFin (by rfl)).symm ⟨y, hyX⟩ := by
        exact Fin.mk_lt_mk.mpr (lt_of_lt_of_le i.2 hq_le_yidx)
      have hsub_lt :
          (X.orderIsoOfFin (by rfl)
            ⟨i.1, lt_of_lt_of_le i.2 h⟩ : X) < ⟨y, hyX⟩ := by
        simpa using
          (X.orderIsoOfFin (by rfl)).strictMono hi_lt_yidx
      exact hsub_lt
    · rw [dif_neg h] at hyNot
      exact False.elim (hyNot hyX)

end LinearTopQChoice

section RelabeledTopQChoice

variable {β : Type*} [DecidableEq β] [LinearOrder β]

/--
Top-q choice after relabeling applicants through an equivalence into a linearly
ordered priority space.
-/
noncomputable def relabeledTopQChoice (q : ℕ) (e : α ≃ β) : ChoiceRule α :=
  fun X => (linearTopQChoice q (X.image e)).image e.symm

/-- Relabeled top-q choice is feasible. -/
theorem relabeledTopQChoice_feasible (q : ℕ) (e : α ≃ β) :
    Feasible (relabeledTopQChoice (α := α) (β := β) q e) := by
  classical
  intro X x hx
  unfold relabeledTopQChoice at hx
  rcases Finset.mem_image.mp hx with ⟨y, hyChoice, hxy⟩
  subst x
  have hyOffer : y ∈ X.image e :=
    linearTopQChoice_feasible (α := β) q (X.image e) hyChoice
  rcases Finset.mem_image.mp hyOffer with ⟨x, hxX, rfl⟩
  simpa using hxX

/-- Relabeled top-q choice is q-acceptant. -/
theorem relabeledTopQChoice_qAcceptant (q : ℕ) (e : α ≃ β) :
    QAcceptant q (relabeledTopQChoice (α := α) (β := β) q e) := by
  classical
  intro X
  unfold relabeledTopQChoice
  rw [Finset.card_image_of_injective _ e.symm.injective]
  rw [linearTopQChoice_qAcceptant (α := β) q]
  rw [Finset.card_image_of_injective _ e.injective]

/-- Relabeled top-q choice is represented by the transported priority order. -/
theorem relabeledTopQChoice_qRepresentative (q : ℕ) (e : α ≃ β) :
    QRepresentative q (relabeledTopQChoice (α := α) (β := β) q e) := by
  classical
  refine ⟨(fun x y => e x < e y), ?_,
    relabeledTopQChoice_feasible (α := α) (β := β) q e,
    relabeledTopQChoice_qAcceptant (α := α) (β := β) q e, ?_⟩
  · constructor
    · intro x
      exact lt_irrefl (e x)
    · constructor
      · intro x y z hxy hyz
        exact lt_trans hxy hyz
      · intro x y hxy
        have he_ne : e x ≠ e y := by
          intro heq
          exact hxy (e.injective heq)
        exact lt_or_gt_of_ne he_ne
  · intro X x y hx hyX hyNot
    unfold relabeledTopQChoice at hx hyNot
    have hex : e x ∈ linearTopQChoice q (X.image e) := by
      rcases Finset.mem_image.mp hx with ⟨b, hb, hbx⟩
      have hb_eq : b = e x := by
        rw [← hbx]
        simp
      simpa [hb_eq] using hb
    have heyOffer : e y ∈ X.image e :=
      Finset.mem_image.mpr ⟨y, hyX, rfl⟩
    have heyNot : e y ∉ linearTopQChoice q (X.image e) := by
      intro hey
      apply hyNot
      exact Finset.mem_image.mpr ⟨e y, hey, by simp⟩
    exact linearTopQChoice_priority (α := β) q hex heyOffer heyNot

end RelabeledTopQChoice

section LinearTopQChoiceCharacterization

variable [LinearOrder α]

/--
Extensional characterization of the top-q rule.  If `S` is a q-sized subset of
the pool and every member of `S` precedes every offered applicant outside `S`,
then top-q selection is exactly `S`.
-/
theorem linearTopQChoice_eq_of_card_of_forall_lt
    {q : ℕ} {X S : Finset α}
    (hSsubX : S ⊆ X)
    (hScard : S.card = q)
    (hbeats : ∀ s, s ∈ S → ∀ y, y ∈ X → y ∉ S → s < y) :
    linearTopQChoice (α := α) q X = S := by
  classical
  have hqle : q ≤ X.card := by
    rw [← hScard]
    exact Finset.card_le_card hSsubX
  have hCcard : (linearTopQChoice (α := α) q X).card = q := by
    rw [linearTopQChoice_qAcceptant (α := α) q X]
    exact Nat.min_eq_left hqle
  have hcard_eq : S.card = (linearTopQChoice (α := α) q X).card := by
    rw [hScard, hCcard]
  have hsubset : linearTopQChoice (α := α) q X ⊆ S := by
    intro y hyC
    by_contra hyNotS
    have hnotSubset : ¬ S ⊆ linearTopQChoice (α := α) q X := by
      intro hSsubC
      have hEq : S = linearTopQChoice (α := α) q X :=
        Finset.eq_of_subset_of_card_le hSsubC (by
          rw [hCcard, hScard])
      exact hyNotS (by simpa [hEq] using hyC)
    have hs_exists :
        ∃ s, s ∈ S ∧ s ∉ linearTopQChoice (α := α) q X := by
      by_contra hnone
      apply hnotSubset
      intro s hsS
      by_contra hsNotC
      exact hnone ⟨s, hsS, hsNotC⟩
    rcases hs_exists with ⟨s, hsS, hsNotC⟩
    have hyX : y ∈ X :=
      linearTopQChoice_feasible (α := α) q X hyC
    have hsX : s ∈ X := hSsubX hsS
    have hys : y < s :=
      linearTopQChoice_priority (α := α) q hyC hsX hsNotC
    have hsy : s < y := hbeats s hsS y hyX hyNotS
    exact (not_lt_of_gt hys) hsy
  exact Finset.eq_of_subset_of_card_le hsubset (by
    rw [hScard, hCcard])

end LinearTopQChoiceCharacterization

section RankedTopQChoice

variable [LinearOrder α]

/--
The linear order that first compares a numeric rank and then breaks ties by the
ambient order.  Lower rank is higher priority.
-/
@[reducible] noncomputable def orderByRank (rank : α → ℕ) : LinearOrder α :=
  LinearOrder.lift' (α := α) (β := Lex (ℕ × α))
    (fun a : α => (toLex (rank a, a) : Lex (ℕ × α)))
    (by
      intro a b h
      exact congrArg (fun p : ℕ × α => p.2) (congrArg ofLex h))

/-- Top-q choice under a numeric rank function, with ambient-order tie breaks. -/
noncomputable def rankedTopQChoice (q : ℕ) (rank : α → ℕ) : ChoiceRule α :=
  letI : LinearOrder α := orderByRank rank
  linearTopQChoice q

/-- Ranked top-q choice is feasible. -/
theorem rankedTopQChoice_feasible (q : ℕ) (rank : α → ℕ) :
    Feasible (rankedTopQChoice (α := α) q rank) := by
  classical
  unfold rankedTopQChoice
  letI : LinearOrder α := orderByRank rank
  exact linearTopQChoice_feasible (α := α) q

/-- Ranked top-q choice is q-acceptant. -/
theorem rankedTopQChoice_qAcceptant (q : ℕ) (rank : α → ℕ) :
    QAcceptant q (rankedTopQChoice (α := α) q rank) := by
  classical
  unfold rankedTopQChoice
  letI : LinearOrder α := orderByRank rank
  exact linearTopQChoice_qAcceptant (α := α) q

/-- Ranked top-q choice is q-representative. -/
theorem rankedTopQChoice_qRepresentative (q : ℕ) (rank : α → ℕ) :
    QRepresentative q (rankedTopQChoice (α := α) q rank) := by
  classical
  unfold rankedTopQChoice
  letI : LinearOrder α := orderByRank rank
  exact linearTopQChoice_qRepresentative (α := α) q

/--
Concrete priority property for ranked top-q choice: chosen applicants precede
rejected offered applicants in the rank order.
-/
theorem rankedTopQChoice_priority (q : ℕ) (rank : α → ℕ)
    {X : Finset α} {x y : α}
    (hx : x ∈ rankedTopQChoice q rank X)
    (hyX : y ∈ X)
    (hyNot : y ∉ rankedTopQChoice q rank X) :
    letI : LinearOrder α := orderByRank rank
    x < y := by
  classical
  unfold rankedTopQChoice at hx hyNot
  letI : LinearOrder α := orderByRank rank
  exact linearTopQChoice_priority (α := α) q hx hyX hyNot

omit [DecidableEq α] in
/-- Lower rank implies higher priority in `orderByRank`. -/
theorem lt_orderByRank_of_rank_lt (rank : α → ℕ) {a b : α}
    (h : rank a < rank b) :
    letI : LinearOrder α := orderByRank rank
    a < b := by
  classical
  change toLex (rank a, a) < (toLex (rank b, b) : Lex (ℕ × α))
  exact Prod.Lex.left _ _ h

end RankedTopQChoice

/--
If two finite sets have the same cardinality and `B` has an element missing
from `A`, then `A` has a compensating element missing from `B`.
-/
theorem exists_mem_sdiff_of_card_eq_of_mem_sdiff
    {A B : Finset α} (hcard : A.card = B.card) {x : α}
    (hx : x ∈ B \ A) :
    ∃ y, y ∈ A \ B := by
  rcases Finset.mem_sdiff.mp hx with ⟨hxB, hxnotA⟩
  by_contra hnone
  have hsubset : A ⊆ B := by
    intro y hyA
    by_contra hyB
    exact hnone ⟨y, Finset.mem_sdiff.mpr ⟨hyA, hyB⟩⟩
  have hAB : A = B :=
    Finset.eq_of_subset_of_card_le hsubset (by omega)
  exact hxnotA (by simpa [hAB] using hxB)

/--
If at most one element of `A` is lost when moving to `B`, then every element
of `A` distinct from a witnessed lost element remains in `B`.
-/
theorem mem_of_mem_of_ne_lost_of_sdiff_card_le_one
    {A B : Finset α} {lost z : α}
    (hlost : lost ∈ A \ B) (hzA : z ∈ A) (hz_ne_lost : z ≠ lost)
    (hcard : (A \ B).card ≤ 1) :
    z ∈ B := by
  by_contra hzB
  have hpair_subset : insert z ({lost} : Finset α) ⊆ A \ B := by
    intro w hw
    rw [Finset.mem_insert] at hw
    rcases hw with rfl | hw
    · exact Finset.mem_sdiff.mpr ⟨hzA, hzB⟩
    · have hw_lost : w = lost := by simpa using hw
      simpa [hw_lost] using hlost
  have hpair_card : (insert z ({lost} : Finset α)).card = 2 := by
    rw [Finset.card_insert_of_notMem]
    · simp
    · simpa using hz_ne_lost
  have htwo_le : 2 ≤ (A \ B).card := by
    rw [← hpair_card]
    exact Finset.card_le_card hpair_subset
  omega

/-- A finite set difference has cardinality zero exactly when the first set is a subset. -/
theorem card_sdiff_eq_zero_iff_subset (A B : Finset α) :
    (A \ B).card = 0 ↔ A ⊆ B := by
  rw [Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset]

/-- The first choice-distance term is zero for all nested sets iff `C` is substitutable. -/
theorem substitutable_iff_choiceGainTerm_eq_zero (C : ChoiceRule α) :
    Substitutable C ↔
      ∀ {X₁ X₂}, X₁ ⊆ X₂ → choiceGainTerm C X₁ X₂ = 0 := by
  constructor
  · intro hC X₁ X₂ hsubset
    rw [choiceGainTerm, card_sdiff_eq_zero_iff_subset]
    exact hC hsubset
  · intro hC X₁ X₂ hsubset
    rw [← card_sdiff_eq_zero_iff_subset]
    exact hC hsubset

/-- The second choice-distance term is zero for all nested sets iff `C` is monotonic. -/
theorem monotonic_iff_choiceLossTerm_eq_zero (C : ChoiceRule α) :
    Monotonic C ↔
      ∀ {X₁ X₂}, X₁ ⊆ X₂ → choiceLossTerm C X₁ X₂ = 0 := by
  constructor
  · intro hC X₁ X₂ hsubset
    rw [choiceLossTerm, card_sdiff_eq_zero_iff_subset]
    exact hC hsubset
  · intro hC X₁ X₂ hsubset
    rw [← card_sdiff_eq_zero_iff_subset]
    exact hC hsubset

/-- Zero instability over nested sets is equivalent to substitutability and monotonicity. -/
theorem zeroUnstable_iff_substitutable_and_monotonic (C : ChoiceRule α) :
    ZeroUnstable C ↔ Substitutable C ∧ Monotonic C := by
  constructor
  · intro hzero
    constructor
    · rw [substitutable_iff_choiceGainTerm_eq_zero]
      intro X₁ X₂ hsubset
      have hdist := hzero hsubset
      rw [choiceDistance] at hdist
      exact (Nat.add_eq_zero_iff.mp hdist).1
    · rw [monotonic_iff_choiceLossTerm_eq_zero]
      intro X₁ X₂ hsubset
      have hdist := hzero hsubset
      rw [choiceDistance] at hdist
      exact (Nat.add_eq_zero_iff.mp hdist).2
  · rintro ⟨hsub, hmono⟩ X₁ X₂ hsubset
    have hgain :
        choiceGainTerm C X₁ X₂ = 0 :=
      (substitutable_iff_choiceGainTerm_eq_zero C).mp hsub hsubset
    have hloss :
        choiceLossTerm C X₁ X₂ = 0 :=
      (monotonic_iff_choiceLossTerm_eq_zero C).mp hmono hsubset
    simp [choiceDistance, hgain, hloss]

/--
Under feasibility, independence is equivalent to substitutability plus
monotonicity.
-/
theorem independent_iff_substitutable_and_monotonic_of_feasible
    (C : ChoiceRule α) (hfeasible : Feasible C) :
    Independent C ↔ Substitutable C ∧ Monotonic C := by
  constructor
  · intro hind
    constructor
    · intro X₁ X₂ hsubset x hx
      rcases Finset.mem_inter.mp hx with ⟨hxX₁, hxCX₂⟩
      rcases hind x with h | h
      · exact h X₁ hxX₁
      · exact False.elim (h X₂ (hsubset hxX₁) hxCX₂)
    · intro X₁ X₂ hsubset x hxCX₁
      have hxX₁ : x ∈ X₁ := hfeasible X₁ hxCX₁
      rcases hind x with h | h
      · exact h X₂ (hsubset hxX₁)
      · exact False.elim (h X₁ hxX₁ hxCX₁)
  · rintro ⟨hsub, hmono⟩ x
    classical
    by_cases hsome : ∃ X, x ∈ X ∧ x ∈ C X
    · left
      rcases hsome with ⟨X₀, hxX₀, hxCX₀⟩
      intro Y hxY
      let U := X₀ ∪ Y
      have hxCU : x ∈ C U := by
        exact hmono (show X₀ ⊆ U by intro z hz; simp [U, hz]) hxCX₀
      have hxInter : x ∈ Y ∩ C U := by
        exact Finset.mem_inter.mpr ⟨hxY, hxCU⟩
      exact hsub (show Y ⊆ U by intro z hz; simp [U, hz]) hxInter
    · right
      intro X hxX hxCX
      exact hsome ⟨X, hxX, hxCX⟩

/-- Independence is equivalent to zero instability under feasibility. -/
theorem independent_iff_zeroUnstable_of_feasible
    (C : ChoiceRule α) (hfeasible : Feasible C) :
    Independent C ↔ ZeroUnstable C := by
  rw [independent_iff_substitutable_and_monotonic_of_feasible C hfeasible,
    zeroUnstable_iff_substitutable_and_monotonic]

/-- A `q`-acceptant rule always chooses at most `q` alternatives. -/
theorem QAcceptant.card_le {q : ℕ} {C : ChoiceRule α}
    (haccept : QAcceptant q C) (X : Finset α) :
    (C X).card ≤ q := by
  rw [haccept X]
  exact min_le_left q X.card

/-- Every q-acceptant rule is `2q`-unstable by the crude two-sided cardinality bound. -/
theorem dUnstable_two_mul_of_qAcceptant {q : ℕ} {C : ChoiceRule α}
    (haccept : QAcceptant q C) :
    DUnstable (2 * q) C := by
  intro X x _hx
  have hgain : choiceGainTerm C X (insert x X) ≤ q := by
    unfold choiceGainTerm
    have hsubset : (X ∩ C (insert x X)) \ C X ⊆ C (insert x X) := by
      intro y hy
      exact (Finset.mem_inter.mp (Finset.mem_sdiff.mp hy).1).2
    exact (Finset.card_le_card hsubset).trans (QAcceptant.card_le haccept _)
  have hloss : choiceLossTerm C X (insert x X) ≤ q := by
    unfold choiceLossTerm
    have hsubset : C X \ C (insert x X) ⊆ C X := by
      intro y hy
      exact (Finset.mem_sdiff.mp hy).1
    exact (Finset.card_le_card hsubset).trans (QAcceptant.card_le haccept _)
  rw [choiceDistance]
  omega

/-- On any input of size at most `q`, a `q`-acceptant rule chooses equally many elements. -/
theorem QAcceptant.card_eq_of_card_le {q : ℕ} {C : ChoiceRule α}
    (haccept : QAcceptant q C) {X : Finset α} (hcard : X.card ≤ q) :
    (C X).card = X.card := by
  rw [haccept X, Nat.min_eq_right hcard]

/-- A feasible `q`-acceptant rule chooses every element of an input of size at most `q`. -/
theorem QAcceptant.eq_of_card_le {q : ℕ} {C : ChoiceRule α}
    (hfeasible : Feasible C) (haccept : QAcceptant q C)
    {X : Finset α} (hcard : X.card ≤ q) :
    C X = X := by
  exact Finset.eq_of_subset_of_card_le (hfeasible X)
    (by rw [QAcceptant.card_eq_of_card_le haccept hcard])

/--
If some offered set has more than `q` alternatives and `q > 0`, no feasible
choice rule can be both monotonic and `q`-acceptant.
-/
theorem false_of_feasible_of_monotonic_of_qAcceptant_of_card_gt
    {q : ℕ} {C : ChoiceRule α} (hfeasible : Feasible C)
    (hmono : Monotonic C) (haccept : QAcceptant q C)
    (hqpos : 0 < q) {U : Finset α} (hUcard : q < U.card) :
    False := by
  obtain ⟨X, hXU, hXcard⟩ := Finset.exists_subset_card_eq (Nat.le_of_lt hUcard)
  have hnotUsubX : ¬ U ⊆ X := by
    intro hUsubX
    have hcard_le : U.card ≤ X.card := Finset.card_le_card hUsubX
    omega
  have hy_exists : ∃ y, y ∈ U ∧ y ∉ X := by
    by_contra h
    apply hnotUsubX
    intro y hyU
    by_contra hyX
    exact h ⟨y, hyU, hyX⟩
  rcases hy_exists with ⟨y, hyU, hyX⟩
  have hXpos : 0 < X.card := by omega
  rcases Finset.card_pos.mp hXpos with ⟨z, hzX⟩
  let Xswap : Finset α := insert y (X.erase z)
  have hy_not_erase : y ∉ X.erase z := by
    intro hy
    exact hyX (Finset.mem_of_mem_erase hy)
  have hXswap_card : Xswap.card = q := by
    change (insert y (X.erase z)).card = q
    rw [Finset.card_insert_of_notMem hy_not_erase]
    rw [Finset.card_erase_add_one hzX]
    exact hXcard
  have hCX : C X = X := by
    exact QAcceptant.eq_of_card_le hfeasible haccept (by omega)
  have hCXswap : C Xswap = Xswap := by
    exact QAcceptant.eq_of_card_le hfeasible haccept (by omega)
  let U₀ : Finset α := insert y X
  have hX_subset_U₀ : X ⊆ U₀ := by
    intro a ha
    exact Finset.mem_insert_of_mem ha
  have hXswap_subset_U₀ : Xswap ⊆ U₀ := by
    intro a ha
    change a ∈ insert y (X.erase z) at ha
    rcases Finset.mem_insert.mp ha with rfl | haerase
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_of_mem_erase haerase)
  have hX_subset_CU₀ : X ⊆ C U₀ := by
    intro a ha
    have : a ∈ C X := by simpa [hCX] using ha
    exact hmono hX_subset_U₀ this
  have hXswap_subset_CU₀ : Xswap ⊆ C U₀ := by
    intro a ha
    have : a ∈ C Xswap := by simpa [hCXswap] using ha
    exact hmono hXswap_subset_U₀ this
  have hinsert_subset_CU₀ : insert y X ⊆ C U₀ := by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | haX
    · apply hXswap_subset_CU₀
      exact Finset.mem_insert_self _ _
    · exact hX_subset_CU₀ haX
  have hq_succ_le : q + 1 ≤ (C U₀).card := by
    have hcard_insert : (insert y X).card = q + 1 := by
      rw [Finset.card_insert_of_notMem hyX, hXcard]
    rw [← hcard_insert]
    exact Finset.card_le_card hinsert_subset_CU₀
  have hCU₀_le_q : (C U₀).card ≤ q := QAcceptant.card_le haccept U₀
  omega

/-- Choice distance satisfies the triangle inequality along nested offered sets. -/
theorem choiceDistance_triangle (C : ChoiceRule α)
    {X₁ X₂ X₃ : Finset α} (h₁₂ : X₁ ⊆ X₂) (_h₂₃ : X₂ ⊆ X₃) :
    choiceDistance C X₁ X₃ ≤ choiceDistance C X₁ X₂ + choiceDistance C X₂ X₃ := by
  let G₁₃ := (X₁ ∩ C X₃) \ C X₁
  let G₁₂ := (X₁ ∩ C X₂) \ C X₁
  let G₂₃ := (X₂ ∩ C X₃) \ C X₂
  let L₁₃ := C X₁ \ C X₃
  let L₁₂ := C X₁ \ C X₂
  let L₂₃ := C X₂ \ C X₃
  have hG_subset : G₁₃ ⊆ G₁₂ ∪ G₂₃ := by
    intro x hx
    rcases Finset.mem_sdiff.mp hx with ⟨hxinter, hxnotC₁⟩
    rcases Finset.mem_inter.mp hxinter with ⟨hxX₁, hxC₃⟩
    by_cases hxC₂ : x ∈ C X₂
    · apply Finset.mem_union_left
      exact Finset.mem_sdiff.mpr
        ⟨Finset.mem_inter.mpr ⟨hxX₁, hxC₂⟩, hxnotC₁⟩
    · apply Finset.mem_union_right
      exact Finset.mem_sdiff.mpr
        ⟨Finset.mem_inter.mpr ⟨h₁₂ hxX₁, hxC₃⟩, hxC₂⟩
  have hL_subset : L₁₃ ⊆ L₁₂ ∪ L₂₃ := by
    intro x hx
    rcases Finset.mem_sdiff.mp hx with ⟨hxC₁, hxnotC₃⟩
    by_cases hxC₂ : x ∈ C X₂
    · apply Finset.mem_union_right
      exact Finset.mem_sdiff.mpr ⟨hxC₂, hxnotC₃⟩
    · apply Finset.mem_union_left
      exact Finset.mem_sdiff.mpr ⟨hxC₁, hxC₂⟩
  have hG_card : G₁₃.card ≤ G₁₂.card + G₂₃.card :=
    (Finset.card_le_card hG_subset).trans (Finset.card_union_le G₁₂ G₂₃)
  have hL_card : L₁₃.card ≤ L₁₂.card + L₂₃.card :=
    (Finset.card_le_card hL_subset).trans (Finset.card_union_le L₁₂ L₂₃)
  change G₁₃.card + L₁₃.card ≤
    (G₁₂.card + L₁₂.card) + (G₂₃.card + L₂₃.card)
  omega

/--
If every gain and every loss lies in a controlled finite set `S`, then choice
distance is at most twice the size of `S`.
-/
theorem choiceDistance_le_two_mul_card_of_gain_loss_subset
    {C : ChoiceRule α} {X₁ X₂ S : Finset α}
    (hgain : (X₁ ∩ C X₂) \ C X₁ ⊆ S)
    (hloss : C X₁ \ C X₂ ⊆ S) :
    choiceDistance C X₁ X₂ ≤ 2 * S.card := by
  have hgain_card :
      ((X₁ ∩ C X₂) \ C X₁).card ≤ S.card :=
    Finset.card_le_card hgain
  have hloss_card :
      (C X₁ \ C X₂).card ≤ S.card :=
    Finset.card_le_card hloss
  rw [choiceDistance, choiceGainTerm, choiceLossTerm]
  omega

/--
One-step instability follows if every one-step gain and loss is confined to a
controlled finite set.
-/
theorem dUnstable_two_mul_card_of_one_step_gain_loss_subset
    {C : ChoiceRule α} {S : Finset α}
    (hcontrolled :
      ∀ X x, x ∉ X →
        ((X ∩ C (insert x X)) \ C X ⊆ S) ∧
          (C X \ C (insert x X) ⊆ S)) :
    DUnstable (2 * S.card) C := by
  intro X x hx
  exact choiceDistance_le_two_mul_card_of_gain_loss_subset
    (C := C) (X₁ := X) (X₂ := insert x X) (S := S)
    (hcontrolled X x hx).1 (hcontrolled X x hx).2

/--
If a choice rule is `d`-unstable for one fresh addition, then adding a finite
set `T` disjoint from `X` changes at most `d * |T|` existing decisions.
-/
theorem choiceDistance_union_le_card_mul_of_dUnstable_of_disjoint
    {d : ℕ} {C : ChoiceRule α} (hunstable : DUnstable d C)
    (X T : Finset α) (hdisjoint : ∀ a ∈ T, a ∉ X) :
    choiceDistance C X (X ∪ T) ≤ d * T.card := by
  induction T using Finset.induction_on with
  | empty =>
      simp [choiceDistance, choiceGainTerm, choiceLossTerm]
  | @insert a T ha ih =>
      have haX : a ∉ X := hdisjoint a (Finset.mem_insert_self _ _)
      have hTdisjoint : ∀ b ∈ T, b ∉ X := by
        intro b hb
        exact hdisjoint b (Finset.mem_insert_of_mem hb)
      have haUnion : a ∉ X ∪ T := by
        intro haXT
        rcases Finset.mem_union.mp haXT with haX' | haT
        · exact haX haX'
        · exact ha haT
      have hstep : choiceDistance C (X ∪ T) (insert a (X ∪ T)) ≤ d :=
        hunstable (X ∪ T) a haUnion
      have htriangle :
          choiceDistance C X (insert a (X ∪ T)) ≤
            choiceDistance C X (X ∪ T) +
              choiceDistance C (X ∪ T) (insert a (X ∪ T)) := by
        exact choiceDistance_triangle C
          (by intro x hx; exact Finset.mem_union_left T hx)
          (by intro x hx; exact Finset.mem_insert_of_mem hx)
      have hih := ih hTdisjoint
      have htarget :
          choiceDistance C X (insert a (X ∪ T)) ≤ d * (insert a T).card := by
        rw [Finset.card_insert_of_notMem ha]
        rw [Nat.mul_succ]
        exact htriangle.trans (Nat.add_le_add hih hstep)
      simpa [Finset.union_insert, Finset.insert_union] using htarget

/--
If a choice rule is `d`-unstable for one fresh addition, then expanding from
`X` to `X ∪ S` changes at most `d` times the number of newly added elements.
-/
theorem choiceDistance_union_le_card_sdiff_mul_of_dUnstable
    {d : ℕ} {C : ChoiceRule α} (hunstable : DUnstable d C)
    (X S : Finset α) :
    choiceDistance C X (X ∪ S) ≤ d * (S \ X).card := by
  have hdisjoint : ∀ a ∈ S \ X, a ∉ X := by
    intro a ha
    exact (Finset.mem_sdiff.mp ha).2
  have hbase :=
    choiceDistance_union_le_card_mul_of_dUnstable_of_disjoint
      (C := C) hunstable X (S \ X) hdisjoint
  have hUnion : X ∪ (S \ X) = X ∪ S := by
    ext a
    constructor
    · intro ha
      rcases Finset.mem_union.mp ha with haX | haSdiff
      · exact Finset.mem_union_left _ haX
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mp haSdiff).1
    · intro ha
      rcases Finset.mem_union.mp ha with haX | haS
      · exact Finset.mem_union_left _ haX
      · by_cases haX : a ∈ X
        · exact Finset.mem_union_left _ haX
        · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨haS, haX⟩)
  simpa [hUnion] using hbase

/-- A q-acceptant substitutable finite choice rule is consistent. -/
theorem consistent_of_qAcceptant_of_substitutable
    {q : ℕ} {C : ChoiceRule α}
    (haccept : QAcceptant q C) (hsub : Substitutable C) :
    Consistent C := by
  intro X₁ X₂ hchosen_subset hsubset
  have hCX₂_subset_CX₁ : C X₂ ⊆ C X₁ := by
    intro x hx
    exact hsub hsubset (Finset.mem_inter.mpr ⟨hchosen_subset hx, hx⟩)
  have hcard_le : (C X₁).card ≤ (C X₂).card := by
    rw [haccept X₁, haccept X₂]
    exact min_le_min_left q (Finset.card_le_card hsubset)
  exact Finset.eq_of_subset_of_card_le hCX₂_subset_CX₁ hcard_le

/--
For a feasible consistent rule, if a fresh applicant is not chosen after being
added, then adding that applicant does not change the chosen set.
-/
theorem choice_insert_eq_self_of_consistent_of_fresh_not_chosen
    {C : ChoiceRule α} (hfeasible : Feasible C) (hcons : Consistent C)
    {X : Finset α} {x : α} (hxNotChosen : x ∉ C (insert x X)) :
    C (insert x X) = C X := by
  have hchosen_subset : C (insert x X) ⊆ X := by
    intro y hy
    have hyOffer : y ∈ insert x X := hfeasible (insert x X) hy
    rw [Finset.mem_insert] at hyOffer
    rcases hyOffer with rfl | hyX
    · exact False.elim (hxNotChosen hy)
    · exact hyX
  have hsubset : X ⊆ insert x X := by
    intro y hy
    exact Finset.mem_insert_of_mem hy
  exact hcons hchosen_subset hsubset

/--
For a feasible q-acceptant substitutable rule, choosing after adding one
applicant only depends on the old chosen set.
-/
theorem choice_insert_eq_choice_insert_choice_of_substitutable
    {q : ℕ} {C : ChoiceRule α}
    (hfeasible : Feasible C) (haccept : QAcceptant q C)
    (hsub : Substitutable C) (X : Finset α) (a : α) :
    C (insert a X) = C (insert a (C X)) := by
  have hconsistent : Consistent C :=
    consistent_of_qAcceptant_of_substitutable haccept hsub
  have hX_subset : X ⊆ insert a X := by
    intro z hz
    exact Finset.mem_insert_of_mem hz
  have hchosen_subset : C (insert a X) ⊆ insert a (C X) := by
    intro z hz
    have hzOffered : z ∈ insert a X := hfeasible (insert a X) hz
    rw [Finset.mem_insert] at hzOffered
    rcases hzOffered with rfl | hzX
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem
        (hsub hX_subset (Finset.mem_inter.mpr ⟨hzX, hz⟩))
  have hinsert_subset : insert a (C X) ⊆ insert a X := by
    intro z hz
    rw [Finset.mem_insert] at hz ⊢
    rcases hz with rfl | hzCX
    · exact Or.inl rfl
    · exact Or.inr (hfeasible X hzCX)
  exact hconsistent hchosen_subset hinsert_subset

/--
A waitlisted witness is an exact one-for-one exchange: if removing `x` makes
`y` newly chosen, then `x` was chosen before removal and the new chosen set is
obtained by replacing `x` by `y`.
-/
theorem choice_erase_eq_insert_erase_choice_of_waitlisted_witness
    {q : ℕ} {C : ChoiceRule α}
    (hfeasible : Feasible C) (haccept : QAcceptant q C)
    (hsub : Substitutable C)
    {X : Finset α} {x y : α} (hxX : x ∈ X)
    (hy : y ∈ C (X.erase x) \ C X) :
    x ∈ C X ∧ (C X).card = q ∧
      C (X.erase x) = insert y ((C X).erase x) := by
  classical
  rcases Finset.mem_sdiff.mp hy with ⟨hyCErase, hyNotCX⟩
  have hcons : Consistent C :=
    consistent_of_qAcceptant_of_substitutable haccept hsub
  have hxCX : x ∈ C X := by
    by_contra hxNotCX
    have hchosen_subset : C X ⊆ X.erase x := by
      intro z hz
      exact Finset.mem_erase.mpr
        ⟨by
          intro hzx
          subst z
          exact hxNotCX hz,
          hfeasible X hz⟩
    have hsame : C X = C (X.erase x) :=
      hcons hchosen_subset (Finset.erase_subset x X)
    exact hyNotCX (by simpa [hsame] using hyCErase)
  have hyX : y ∈ X := by
    exact Finset.mem_of_mem_erase (hfeasible (X.erase x) hyCErase)
  have hq_lt_X : q < X.card := by
    by_contra hnot
    have hcard : X.card ≤ q := Nat.le_of_not_gt hnot
    have hCX : C X = X :=
      QAcceptant.eq_of_card_le hfeasible haccept hcard
    exact hyNotCX (by simpa [hCX] using hyX)
  have hcardCX : (C X).card = q := by
    rw [haccept X, Nat.min_eq_left (le_of_lt hq_lt_X)]
  have hcardErase : q ≤ (X.erase x).card := by
    rw [Finset.card_erase_of_mem hxX]
    omega
  have hcardCErase : (C (X.erase x)).card = q := by
    rw [haccept (X.erase x), Nat.min_eq_left hcardErase]
  have herased_subset : (C X).erase x ⊆ C (X.erase x) := by
    intro z hz
    have hz_ne_x : z ≠ x := (Finset.mem_erase.mp hz).1
    have hzCX : z ∈ C X := (Finset.mem_erase.mp hz).2
    exact hsub (Finset.erase_subset x X)
      (Finset.mem_inter.mpr
        ⟨Finset.mem_erase.mpr ⟨hz_ne_x, hfeasible X hzCX⟩, hzCX⟩)
  have hinsert_subset : insert y ((C X).erase x) ⊆ C (X.erase x) := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hzErase
    · exact hyCErase
    · exact herased_subset hzErase
  have hyNotErase : y ∉ (C X).erase x := by
    intro hyErase
    exact hyNotCX (Finset.mem_of_mem_erase hyErase)
  have hqpos : 0 < q := by
    rw [← hcardCX]
    exact Finset.card_pos.mpr ⟨x, hxCX⟩
  have hcard_insert : (insert y ((C X).erase x)).card = q := by
    rw [Finset.card_insert_of_notMem hyNotErase]
    rw [Finset.card_erase_of_mem hxCX, hcardCX]
    omega
  exact
    ⟨hxCX, hcardCX,
      (Finset.eq_of_subset_of_card_le hinsert_subset (by
        rw [hcard_insert, hcardCErase])).symm⟩

/--
Batch append/remove exchange step.  If every member of `W` is a rejected
applicant matched injectively to a chosen applicant whose individual removal
admits that member, then after all matched chosen applicants are removed, every
member of `W` is borderline.
-/
theorem waitlisted_family_subset_borderlineSet_of_exchange_matching
    [Fintype α] {q : ℕ} {C : ChoiceRule α}
    (hfeasible : Feasible C) (haccept : QAcceptant q C)
    (hsub : Substitutable C)
    {X W : Finset α} {mate : α → α}
    (hcardCX : (C X).card = q)
    (hWsubset : W ⊆ X \ C X)
    (hmate_chosen : ∀ y, y ∈ W → mate y ∈ C X)
    (hmate_inj : ∀ {y z}, y ∈ W → z ∈ W → mate y = mate z → y = z)
    (hmatch :
      ∀ y, y ∈ W →
        C (X.erase (mate y)) = insert y ((C X).erase (mate y))) :
    W ⊆ borderlineSet C (X \ W.image mate) := by
  classical
  intro y hyW
  let M : Finset α := W.image mate
  let R : Finset α := X \ M
  let x : α := mate y
  have hyX : y ∈ X := (Finset.mem_sdiff.mp (hWsubset hyW)).1
  have hyNotCX : y ∉ C X := (Finset.mem_sdiff.mp (hWsubset hyW)).2
  have hxCX : x ∈ C X := hmate_chosen y hyW
  have hxX : x ∈ X := hfeasible X hxCX
  have hxM : x ∈ M := by
    exact Finset.mem_image.mpr ⟨y, hyW, rfl⟩
  have hM_subset_CX : M ⊆ C X := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨w, hwW, rfl⟩
    exact hmate_chosen w hwW
  have hyNotM : y ∉ M := by
    intro hyM
    exact hyNotCX (hM_subset_CX hyM)
  have hyR : y ∈ R := Finset.mem_sdiff.mpr ⟨hyX, hyNotM⟩
  have hR_subset_erase : R ⊆ X.erase x := by
    intro z hz
    rcases Finset.mem_sdiff.mp hz with ⟨hzX, hzNotM⟩
    exact Finset.mem_erase.mpr
      ⟨by
        intro hzx
        subst z
        exact hzNotM hxM,
        hzX⟩
  have hyCErase : y ∈ C (X.erase x) := by
    have hchoice := hmatch y hyW
    rw [hchoice]
    exact Finset.mem_insert_self _ _
  have hyCR : y ∈ C R := by
    exact hsub hR_subset_erase (Finset.mem_inter.mpr ⟨hyR, hyCErase⟩)
  have hyNotCS : y ∉ C (insert x R) := by
    intro hyCS
    let S : Finset α := insert x R
    let lower : Finset α := (C X \ M.erase x) ∪ W
    have hS_subset_X : S ⊆ X := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hzR
      · exact hxX
      · exact (Finset.mem_sdiff.mp hzR).1
    have hW_not_mem_M : ∀ {z}, z ∈ W → z ∉ M := by
      intro z hzW hzM
      exact (Finset.mem_sdiff.mp (hWsubset hzW)).2 (hM_subset_CX hzM)
    have hlower_subset : lower ⊆ C S := by
      intro z hzLower
      rcases Finset.mem_union.mp hzLower with hzOld | hzW
      · rcases Finset.mem_sdiff.mp hzOld with ⟨hzCX, hzNotMErase⟩
        have hzS : z ∈ S := by
          by_cases hzx : z = x
          · exact Finset.mem_insert.mpr (Or.inl hzx)
          · have hzNotM : z ∉ M := by
              intro hzM
              exact hzNotMErase (Finset.mem_erase.mpr ⟨hzx, hzM⟩)
            exact Finset.mem_insert.mpr
              (Or.inr (Finset.mem_sdiff.mpr ⟨hfeasible X hzCX, hzNotM⟩))
        exact hsub hS_subset_X (Finset.mem_inter.mpr ⟨hzS, hzCX⟩)
      · by_cases hzy : z = y
        · simpa [S, hzy] using hyCS
        · have hmate_ne : mate z ≠ x := by
            intro hzmate
            have hzy' : z = y := hmate_inj hzW hyW hzmate
            exact hzy hzy'
          have hzNotM : z ∉ M := hW_not_mem_M hzW
          have hzS : z ∈ S := by
            exact Finset.mem_insert.mpr
              (Or.inr (Finset.mem_sdiff.mpr
                ⟨(Finset.mem_sdiff.mp (hWsubset hzW)).1, hzNotM⟩))
          have hS_subset_erase : S ⊆ X.erase (mate z) := by
            intro a haS
            rcases Finset.mem_insert.mp haS with hax | haR
            · subst a
              exact Finset.mem_erase.mpr ⟨Ne.symm hmate_ne, hxX⟩
            · rcases Finset.mem_sdiff.mp haR with ⟨haX, haNotM⟩
              exact Finset.mem_erase.mpr
                ⟨by
                  intro haz
                  subst a
                  exact haNotM (Finset.mem_image.mpr ⟨z, hzW, rfl⟩),
                  haX⟩
          have hzCErase : z ∈ C (X.erase (mate z)) := by
            have hchoice := hmatch z hzW
            rw [hchoice]
            exact Finset.mem_insert_self _ _
          exact hsub hS_subset_erase (Finset.mem_inter.mpr ⟨hzS, hzCErase⟩)
    have hinjOn : Set.InjOn mate (↑W : Set α) := by
      intro a ha b hb hab
      exact hmate_inj (by simpa using ha) (by simpa using hb) hab
    have hMcard : M.card = W.card := by
      simpa [M] using Finset.card_image_of_injOn hinjOn
    have hMcard_le_q : M.card ≤ q := by
      have hle : M.card ≤ (C X).card := Finset.card_le_card hM_subset_CX
      rwa [hcardCX] at hle
    have hWpos : 0 < W.card := Finset.card_pos.mpr ⟨y, hyW⟩
    have hdisj_lower : Disjoint (C X \ M.erase x) W := by
      rw [Finset.disjoint_left]
      intro z hzOld hzW
      exact (Finset.mem_sdiff.mp (hWsubset hzW)).2
        (Finset.mem_sdiff.mp hzOld).1
    have hInter : M.erase x ∩ C X = M.erase x := by
      ext z
      constructor
      · intro hz
        exact (Finset.mem_inter.mp hz).1
      · intro hz
        exact Finset.mem_inter.mpr
          ⟨hz, hM_subset_CX ((Finset.erase_subset x M) hz)⟩
    have hOldCard : (C X \ M.erase x).card = q - (M.card - 1) := by
      rw [Finset.card_sdiff, hInter, Finset.card_erase_of_mem hxM, hcardCX]
    have hLowerCard : lower.card = q + 1 := by
      rw [Finset.card_union_of_disjoint hdisj_lower, hOldCard, hMcard]
      have hWleq : W.card ≤ q := by simpa [hMcard] using hMcard_le_q
      omega
    have hCS_le_q : (C S).card ≤ q := by
      rw [haccept S]
      exact Nat.min_le_left q S.card
    have hq1_le_q : q + 1 ≤ q := by
      have hle := (Finset.card_le_card hlower_subset).trans hCS_le_q
      rw [hLowerCard] at hle
      exact hle
    omega
  rw [borderlineSet]
  exact Finset.mem_biUnion.mpr
    ⟨x, Finset.mem_univ x,
      Finset.mem_sdiff.mpr ⟨by simpa [R] using hyCR, by simpa [R, x] using hyNotCS⟩⟩

/-- If two fresh insertions into the same finite set are equal, the fresh elements match. -/
theorem eq_of_insert_eq_insert_of_notMem
    {s : Finset α} {y z : α} (hy : y ∉ s) (_hz : z ∉ s)
    (h : insert y s = insert z s) :
    y = z := by
  have hyMem : y ∈ insert z s := by
    rw [← h]
    exact Finset.mem_insert_self _ _
  rcases Finset.mem_insert.mp hyMem with hyz | hyS
  · exact hyz
  · exact False.elim (hy hyS)

/--
Every waitlisted set has a borderline set at least as large.  This is the
forward, waitlisted-to-borderline half of the appendix append/remove maximum
argument.
-/
theorem waitlistedSet_card_le_some_borderlineSet_card
    [Fintype α] {q : ℕ} {C : ChoiceRule α}
    (hfeasible : Feasible C) (haccept : QAcceptant q C)
    (hsub : Substitutable C) (X : Finset α) :
    ∃ Y : Finset α,
      (waitlistedSet C X).card ≤ (borderlineSet C Y).card := by
  classical
  let W : Finset α := waitlistedSet C X
  by_cases hWempty : W = ∅
  · refine ⟨∅, ?_⟩
    simp [W, hWempty]
  · have hWnonempty : 0 < W.card := Finset.card_pos.mpr
      (Finset.nonempty_iff_ne_empty.mpr hWempty)
    have hwitness :
        ∀ y, y ∈ W → ∃ x, x ∈ X ∧ y ∈ C (X.erase x) \ C X := by
      intro y hy
      change y ∈ waitlistedSet C X at hy
      rw [waitlistedSet] at hy
      rcases Finset.mem_biUnion.mp hy with ⟨x, hxX, hyDiff⟩
      exact ⟨x, hxX, hyDiff⟩
    let mate : α → α := fun y =>
      if hy : y ∈ W then Classical.choose (hwitness y hy) else y
    have hmate_spec :
        ∀ y (hy : y ∈ W),
          mate y ∈ X ∧ y ∈ C (X.erase (mate y)) \ C X := by
      intro y hy
      have hspec := Classical.choose_spec (hwitness y hy)
      simpa [mate, hy] using hspec
    rcases Finset.card_pos.mp hWnonempty with ⟨y0, hy0W⟩
    have hspec0 := hmate_spec y0 hy0W
    have hex0 :=
      choice_erase_eq_insert_erase_choice_of_waitlisted_witness
        (C := C) hfeasible haccept hsub hspec0.1 hspec0.2
    have hcardCX : (C X).card = q := hex0.2.1
    have hWsubset : W ⊆ X \ C X := by
      intro y hy
      have hspec := hmate_spec y hy
      exact Finset.mem_sdiff.mpr
        ⟨Finset.mem_of_mem_erase
            (hfeasible (X.erase (mate y)) (Finset.mem_sdiff.mp hspec.2).1),
          (Finset.mem_sdiff.mp hspec.2).2⟩
    have hmate_chosen : ∀ y, y ∈ W → mate y ∈ C X := by
      intro y hy
      have hspec := hmate_spec y hy
      exact
        (choice_erase_eq_insert_erase_choice_of_waitlisted_witness
          (C := C) hfeasible haccept hsub hspec.1 hspec.2).1
    have hmatch :
      ∀ y, y ∈ W →
        C (X.erase (mate y)) = insert y ((C X).erase (mate y)) := by
      intro y hy
      have hspec := hmate_spec y hy
      exact
        (choice_erase_eq_insert_erase_choice_of_waitlisted_witness
          (C := C) hfeasible haccept hsub hspec.1 hspec.2).2.2
    have hmate_inj :
        ∀ {y z}, y ∈ W → z ∈ W → mate y = mate z → y = z := by
      intro y z hy hz hmateEq
      let s : Finset α := (C X).erase (mate y)
      have hyNotCX : y ∉ C X := (Finset.mem_sdiff.mp (hWsubset hy)).2
      have hzNotCX : z ∉ C X := (Finset.mem_sdiff.mp (hWsubset hz)).2
      have hyNotS : y ∉ s := by
        intro hys
        exact hyNotCX (Finset.mem_of_mem_erase hys)
      have hzNotS : z ∉ s := by
        intro hzs
        exact hzNotCX (Finset.mem_of_mem_erase hzs)
      have hyChoice := hmatch y hy
      have hzChoice := hmatch z hz
      have hinsert :
          insert y s = insert z s := by
        have hyChoice' : C (X.erase (mate y)) = insert y s := by
          simpa [s] using hyChoice
        have hzChoice' : C (X.erase (mate y)) = insert z s := by
          simpa [s, hmateEq] using hzChoice
        rw [← hyChoice', ← hzChoice']
      exact eq_of_insert_eq_insert_of_notMem hyNotS hzNotS hinsert
    let Y : Finset α := X \ W.image mate
    refine ⟨Y, ?_⟩
    have hsubset :
        W ⊆ borderlineSet C Y := by
      simpa [Y] using
        waitlisted_family_subset_borderlineSet_of_exchange_matching
          (C := C) hfeasible haccept hsub hcardCX hWsubset hmate_chosen
          hmate_inj hmatch
    exact Finset.card_le_card hsubset

/-- The borderline-only variability bound follows from the general bound. -/
theorem variabilityAtMost_of_generalVariabilityAtMost
    [Fintype α] {m : ℕ} {C : ChoiceRule α}
    (hgen : GeneralVariabilityAtMost m C) :
    VariabilityAtMost m C := by
  intro X
  exact (hgen X).1

/--
For feasible q-acceptant substitutable rules, bounding the borderline side also
bounds the waitlisted side.
-/
theorem generalVariabilityAtMost_of_variabilityAtMost_of_feasible_of_qAcceptant_of_substitutable
    [Fintype α] {m q : ℕ} {C : ChoiceRule α}
    (hfeasible : Feasible C) (haccept : QAcceptant q C)
    (hsub : Substitutable C) (hvar : VariabilityAtMost m C) :
    GeneralVariabilityAtMost m C := by
  intro X
  constructor
  · exact hvar X
  · rcases waitlistedSet_card_le_some_borderlineSet_card
      (C := C) hfeasible haccept hsub X with ⟨Y, hle⟩
    exact hle.trans (hvar Y)

/--
For feasible q-acceptant substitutable rules, the main-text and appendix
upper-bound formulations of variability are equivalent.
-/
theorem generalVariabilityAtMost_iff_variabilityAtMost_of_feasible_of_qAcceptant_of_substitutable
    [Fintype α] {m q : ℕ} {C : ChoiceRule α}
    (hfeasible : Feasible C) (haccept : QAcceptant q C)
    (hsub : Substitutable C) :
    GeneralVariabilityAtMost m C ↔ VariabilityAtMost m C := by
  constructor
  · exact variabilityAtMost_of_generalVariabilityAtMost
  · exact generalVariabilityAtMost_of_variabilityAtMost_of_feasible_of_qAcceptant_of_substitutable
      (C := C) hfeasible haccept hsub

/--
For feasible q-acceptant substitutable rules, exact main-text variability and
exact appendix variability are equivalent.
-/
theorem generalVariabilityExactly_iff_variabilityExactly_of_feasible_of_qAcceptant_of_substitutable
    [Fintype α] {m q : ℕ} {C : ChoiceRule α}
    (hfeasible : Feasible C) (haccept : QAcceptant q C)
    (hsub : Substitutable C) :
    GeneralVariabilityExactly m C ↔ VariabilityExactly m C := by
  constructor
  · intro hgen
    refine ⟨variabilityAtMost_of_generalVariabilityAtMost hgen.1, ?_⟩
    rcases hgen.2 with hborder | hwait
    · exact hborder
    · rcases hwait with ⟨X, hX⟩
      rcases waitlistedSet_card_le_some_borderlineSet_card
          (C := C) hfeasible haccept hsub X with ⟨Y, hle⟩
      refine ⟨Y, ?_⟩
      have hYle : (borderlineSet C Y).card ≤ m := (hgen.1 Y).1
      have hmle : m ≤ (borderlineSet C Y).card := by
        simpa [hX] using hle
      exact le_antisymm hYle hmle
  · intro hvar
    exact
      ⟨generalVariabilityAtMost_of_variabilityAtMost_of_feasible_of_qAcceptant_of_substitutable
          (C := C) hfeasible haccept hsub hvar.1,
        Or.inl hvar.2⟩

/--
For feasible q-acceptant substitutable rules, the borderline set depends only
on the current chosen set.
-/
theorem borderlineSet_eq_of_choice_eq_of_substitutable
    [Fintype α] {q : ℕ} {C : ChoiceRule α}
    (hfeasible : Feasible C) (haccept : QAcceptant q C)
    (hsub : Substitutable C) {X₁ X₂ : Finset α}
    (hchoice : C X₁ = C X₂) :
    borderlineSet C X₁ = borderlineSet C X₂ := by
  classical
  have hinsert : ∀ a, C (insert a X₁) = C (insert a X₂) := by
    intro a
    rw [choice_insert_eq_choice_insert_choice_of_substitutable
        (C := C) hfeasible haccept hsub X₁ a,
      choice_insert_eq_choice_insert_choice_of_substitutable
        (C := C) hfeasible haccept hsub X₂ a,
      hchoice]
  ext z
  constructor
  · intro hz
    rw [borderlineSet] at hz ⊢
    rcases Finset.mem_biUnion.mp hz with ⟨a, _ha, hzloss⟩
    exact Finset.mem_biUnion.mpr
      ⟨a, Finset.mem_univ a, by
        rcases Finset.mem_sdiff.mp hzloss with ⟨hzCX₁, hzNot⟩
        exact Finset.mem_sdiff.mpr
          ⟨by simpa [← hchoice] using hzCX₁,
            by
              intro hzCX₂a
              exact hzNot (by simpa [hinsert a] using hzCX₂a)⟩⟩
  · intro hz
    rw [borderlineSet] at hz ⊢
    rcases Finset.mem_biUnion.mp hz with ⟨a, _ha, hzloss⟩
    exact Finset.mem_biUnion.mpr
      ⟨a, Finset.mem_univ a, by
        rcases Finset.mem_sdiff.mp hzloss with ⟨hzCX₂, hzNot⟩
        exact Finset.mem_sdiff.mpr
          ⟨by simpa [hchoice] using hzCX₂,
            by
              intro hzCX₁a
              exact hzNot (by simpa [hinsert a] using hzCX₁a)⟩⟩

/--
If there is no single-addition gain, then an element rejected from a feasible
set remains rejected after one fresh insertion.
-/
theorem rejected_persists_insert_of_no_single_add_gain
    {C : ChoiceRule α}
    (hno :
      ¬ ∃ X x xstar,
        x ∉ X ∧ xstar ∈ X ∧ xstar ∈ C (insert x X) ∧ xstar ∉ C X)
    {X : Finset α} {x xstar : α}
    (hx : x ∉ X) (hxstarX : xstar ∈ X) (hrej : xstar ∉ C X) :
    xstar ∉ C (insert x X) := by
  intro hacc
  exact hno ⟨X, x, xstar, hx, hxstarX, hacc, hrej⟩

/--
The same no-single-addition-gain hypothesis propagates rejection across any
finite sequence of insertions.
-/
theorem rejected_persists_union_of_no_single_add_gain
    {C : ChoiceRule α}
    (hno :
      ¬ ∃ X x xstar,
        x ∉ X ∧ xstar ∈ X ∧ xstar ∈ C (insert x X) ∧ xstar ∉ C X)
    {X S : Finset α} {xstar : α}
    (hxstarX : xstar ∈ X) (hrej : xstar ∉ C X) :
    xstar ∉ C (X ∪ S) := by
  induction S using Finset.induction_on with
  | empty =>
      simpa using hrej
  | @insert a S ha ih =>
      have hUnion : X ∪ insert a S = insert a (X ∪ S) := by
        ext y
        simp
      rw [hUnion]
      by_cases haBase : a ∈ X ∪ S
      · simpa [Finset.insert_eq_of_mem haBase] using ih
      · exact rejected_persists_insert_of_no_single_add_gain
          (C := C) hno haBase (Finset.mem_union_left S hxstarX) ih

/--
If no single fresh addition can make a previously rejected existing element
accepted, then the choice rule is substitutable.
-/
theorem substitutable_of_no_single_add_gain
    (C : ChoiceRule α)
    (hno :
      ¬ ∃ X x xstar,
        x ∉ X ∧ xstar ∈ X ∧ xstar ∈ C (insert x X) ∧ xstar ∉ C X) :
    Substitutable C := by
  intro X₁ X₂ hsubset x hx
  rcases Finset.mem_inter.mp hx with ⟨hxX₁, hxCX₂⟩
  by_contra hxnotCX₁
  have hpersist :
      x ∉ C (X₁ ∪ (X₂ \ X₁)) :=
    rejected_persists_union_of_no_single_add_gain
      (C := C) hno hxX₁ hxnotCX₁
  have hdecomp : X₁ ∪ (X₂ \ X₁) = X₂ := by
    ext y
    constructor
    · intro hy
      rcases Finset.mem_union.mp hy with hyX₁ | hysdiff
      · exact hsubset hyX₁
      · exact (Finset.mem_sdiff.mp hysdiff).1
    · intro hyX₂
      by_cases hyX₁ : y ∈ X₁
      · exact Finset.mem_union_left _ hyX₁
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hyX₂, hyX₁⟩)
  exact hpersist (by simpa [hdecomp] using hxCX₂)

/--
Non-substitutability has a one-step witness: adding one fresh alternative can
make an existing rejected alternative become accepted.
-/
theorem exists_single_add_gain_of_not_substitutable
    (C : ChoiceRule α) (hnot : ¬ Substitutable C) :
    ∃ X x xstar,
      x ∉ X ∧ xstar ∈ X ∧ xstar ∈ C (insert x X) ∧ xstar ∉ C X := by
  by_contra hno
  exact hnot (substitutable_of_no_single_add_gain C hno)

/--
A feasible q-acceptant substitutable finite choice rule is 1-unstable for
fresh one-element expansions.
-/
theorem dUnstable_one_of_feasible_of_qAcceptant_of_substitutable
    {q : ℕ} {C : ChoiceRule α}
    (hfeasible : Feasible C) (haccept : QAcceptant q C)
    (hsub : Substitutable C) :
    DUnstable 1 C := by
  intro X x hxnot
  let X' : Finset α := insert x X
  have hX_subset_X' : X ⊆ X' := by
    intro y hy
    exact Finset.mem_insert_of_mem hy
  have hgain_zero : choiceGainTerm C X X' = 0 :=
    (substitutable_iff_choiceGainTerm_eq_zero C).mp hsub hX_subset_X'
  have hloss_le : choiceLossTerm C X X' ≤ 1 := by
    by_cases hsmall : X.card < q
    · have hX_le_q : X.card ≤ q := le_of_lt hsmall
      have hX'_le_q : X'.card ≤ q := by
        change (insert x X).card ≤ q
        rw [Finset.card_insert_of_notMem hxnot]
        omega
      have hCX : C X = X := QAcceptant.eq_of_card_le hfeasible haccept hX_le_q
      have hCX' : C X' = X' := QAcceptant.eq_of_card_le hfeasible haccept hX'_le_q
      rw [choiceLossTerm, hCX, hCX']
      apply le_trans (b := 0)
      · apply le_of_eq
        rw [card_sdiff_eq_zero_iff_subset]
        exact hX_subset_X'
      · omega
    · have hq_le_X : q ≤ X.card := Nat.le_of_not_gt hsmall
      have hq_le_X' : q ≤ X'.card := by
        change q ≤ (insert x X).card
        rw [Finset.card_insert_of_notMem hxnot]
        omega
      have hcard_eq : (C X).card = (C X').card := by
        rw [haccept X, haccept X']
        rw [Nat.min_eq_left hq_le_X, Nat.min_eq_left hq_le_X']
      have hnew_subset_singleton : C X' \ C X ⊆ ({x} : Finset α) := by
        intro y hy
        rcases Finset.mem_sdiff.mp hy with ⟨hyCX', hynotCX⟩
        have hyX' : y ∈ X' := hfeasible X' hyCX'
        change y ∈ insert x X at hyX'
        rcases Finset.mem_insert.mp hyX' with rfl | hyX
        · exact Finset.mem_singleton_self _
        · have hy_inter : y ∈ X ∩ C X' := Finset.mem_inter.mpr ⟨hyX, hyCX'⟩
          have hyCX : y ∈ C X := hsub hX_subset_X' hy_inter
          exact False.elim (hynotCX hyCX)
      have hnew_card_le : (C X' \ C X).card ≤ 1 := by
        have hcard := Finset.card_le_card hnew_subset_singleton
        simpa using hcard
      rw [choiceLossTerm]
      rw [Finset.card_sdiff_comm hcard_eq]
      exact hnew_card_le
  change choiceGainTerm C X X' + choiceLossTerm C X X' ≤ 1
  omega

/--
For feasible q-acceptant choice rules, 1-instability forces
substitutability.
-/
theorem substitutable_of_dUnstable_one_of_feasible_of_qAcceptant
    {q : ℕ} {C : ChoiceRule α}
    (hfeasible : Feasible C) (haccept : QAcceptant q C)
    (hunstable : DUnstable 1 C) :
    Substitutable C := by
  by_contra hnot
  rcases exists_single_add_gain_of_not_substitutable C hnot with
    ⟨X, x, xstar, hxnot, hxstarX, hxstarCX', hxstarNotCX⟩
  let X' : Finset α := insert x X
  have hdist : choiceDistance C X X' ≤ 1 := by
    simpa [X'] using hunstable X x hxnot
  have hgain_pos : 0 < choiceGainTerm C X X' := by
    rw [choiceGainTerm]
    exact Finset.card_pos.mpr
      ⟨xstar, Finset.mem_sdiff.mpr
        ⟨Finset.mem_inter.mpr ⟨hxstarX, by simpa [X'] using hxstarCX'⟩,
          hxstarNotCX⟩⟩
  have hproper : C X ⊂ X := by
    refine ⟨hfeasible X, ?_⟩
    intro hreverse
    exact hxstarNotCX (hreverse hxstarX)
  have hCX_card_lt_X : (C X).card < X.card :=
    Finset.card_lt_card hproper
  have hmin_lt : min q X.card < X.card := by
    simpa [haccept X] using hCX_card_lt_X
  have hq_lt_X : q < X.card := by
    by_cases hcard : X.card ≤ q
    · have hmin_eq : min q X.card = X.card := Nat.min_eq_right hcard
      omega
    · exact Nat.lt_of_not_ge hcard
  have hq_le_X : q ≤ X.card := Nat.le_of_lt hq_lt_X
  have hX'_card : X'.card = X.card + 1 := by
    change (insert x X).card = X.card + 1
    rw [Finset.card_insert_of_notMem hxnot]
  have hq_le_X' : q ≤ X'.card := by
    rw [hX'_card]
    omega
  have hcard_eq : (C X).card = (C X').card := by
    rw [haccept X, haccept X']
    rw [Nat.min_eq_left hq_le_X, Nat.min_eq_left hq_le_X']
  have hnew_pos : 0 < (C X' \ C X).card := by
    exact Finset.card_pos.mpr
      ⟨xstar, Finset.mem_sdiff.mpr ⟨by simpa [X'] using hxstarCX', hxstarNotCX⟩⟩
  have hloss_pos : 0 < choiceLossTerm C X X' := by
    rw [choiceLossTerm]
    rw [Finset.card_sdiff_comm hcard_eq]
    exact hnew_pos
  have htwo_le : 2 ≤ choiceDistance C X X' := by
    have hgain_ge : 1 ≤ choiceGainTerm C X X' := Nat.succ_le_of_lt hgain_pos
    have hloss_ge : 1 ≤ choiceLossTerm C X X' := Nat.succ_le_of_lt hloss_pos
    rw [choiceDistance]
    omega
  omega

/--
Under feasibility and q-acceptance, substitutability is equivalent to
1-instability.
-/
theorem dUnstable_one_iff_substitutable_of_feasible_of_qAcceptant
    {q : ℕ} {C : ChoiceRule α}
    (hfeasible : Feasible C) (haccept : QAcceptant q C) :
    DUnstable 1 C ↔ Substitutable C := by
  constructor
  · exact substitutable_of_dUnstable_one_of_feasible_of_qAcceptant
      (C := C) hfeasible haccept
  · exact dUnstable_one_of_feasible_of_qAcceptant_of_substitutable
      (C := C) hfeasible haccept

/--
For feasible q-acceptant 1-unstable rules, the main-text and appendix
upper-bound formulations of variability are equivalent.
-/
theorem generalVariabilityAtMost_iff_variabilityAtMost_of_feasible_of_qAcceptant_of_dUnstable_one
    [Fintype α] {m q : ℕ} {C : ChoiceRule α}
    (hfeasible : Feasible C) (haccept : QAcceptant q C)
    (hunstable : DUnstable 1 C) :
    GeneralVariabilityAtMost m C ↔ VariabilityAtMost m C := by
  exact
    generalVariabilityAtMost_iff_variabilityAtMost_of_feasible_of_qAcceptant_of_substitutable
      (C := C) hfeasible haccept
      (substitutable_of_dUnstable_one_of_feasible_of_qAcceptant
        (C := C) hfeasible haccept hunstable)

/--
For feasible q-acceptant 1-unstable rules, exact main-text variability and
exact appendix variability are equivalent.
-/
theorem generalVariabilityExactly_iff_variabilityExactly_of_feasible_of_qAcceptant_of_dUnstable_one
    [Fintype α] {m q : ℕ} {C : ChoiceRule α}
    (hfeasible : Feasible C) (haccept : QAcceptant q C)
    (hunstable : DUnstable 1 C) :
    GeneralVariabilityExactly m C ↔ VariabilityExactly m C := by
  exact
    generalVariabilityExactly_iff_variabilityExactly_of_feasible_of_qAcceptant_of_substitutable
      (C := C) hfeasible haccept
      (substitutable_of_dUnstable_one_of_feasible_of_qAcceptant
        (C := C) hfeasible haccept hunstable)

/--
If `B` is feasible for the one-element expansion `insert x X`, and `x` is not
in `B`, then every element of `B` already lies in `X`.
-/
theorem sdiff_eq_inter_sdiff_of_subset_insert_of_not_mem
    {A B X : Finset α} {x : α}
    (hB : B ⊆ insert x X) (hxB : x ∉ B) :
    B \ A = (X ∩ B) \ A := by
  ext y
  constructor
  · intro hy
    rcases Finset.mem_sdiff.mp hy with ⟨hyB, hyA⟩
    have hyInsert : y ∈ insert x X := hB hyB
    rcases Finset.mem_insert.mp hyInsert with rfl | hyX
    · exact False.elim (hxB hyB)
    · exact Finset.mem_sdiff.mpr
        ⟨Finset.mem_inter.mpr ⟨hyX, hyB⟩, hyA⟩
  · intro hy
    rcases Finset.mem_sdiff.mp hy with ⟨hyInter, hyA⟩
    exact Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hyInter).2, hyA⟩

/--
If `A` is feasible for `X`, `B` is feasible for `insert x X`, and the fresh
element `x` is in `B`, then `B \ A` consists of `x` plus the old alternatives
in the gain set.
-/
theorem sdiff_eq_insert_inter_sdiff_of_subset_of_subset_insert_of_mem
    {A B X : Finset α} {x : α}
    (hA : A ⊆ X) (hB : B ⊆ insert x X) (hxX : x ∉ X)
    (hxB : x ∈ B) :
    B \ A = insert x ((X ∩ B) \ A) := by
  ext y
  constructor
  · intro hy
    rcases Finset.mem_sdiff.mp hy with ⟨hyB, hyA⟩
    have hyInsert : y ∈ insert x X := hB hyB
    rcases Finset.mem_insert.mp hyInsert with rfl | hyX
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem
        (Finset.mem_sdiff.mpr
          ⟨Finset.mem_inter.mpr ⟨hyX, hyB⟩, hyA⟩)
  · intro hy
    rcases Finset.mem_insert.mp hy with hyEq | hyGain
    · have hxA : x ∉ A := by
        intro hxA
        exact hxX (hA hxA)
      subst y
      exact Finset.mem_sdiff.mpr ⟨hxB, hxA⟩
    · rcases Finset.mem_sdiff.mp hyGain with ⟨hyInter, hyA⟩
      exact Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hyInter).2, hyA⟩

/--
Cardinality form of
`sdiff_eq_insert_inter_sdiff_of_subset_of_subset_insert_of_mem`.
-/
theorem card_sdiff_eq_card_inter_sdiff_add_one_of_subset_of_subset_insert_of_mem
    {A B X : Finset α} {x : α}
    (hA : A ⊆ X) (hB : B ⊆ insert x X) (hxX : x ∉ X)
    (hxB : x ∈ B) :
    (B \ A).card = ((X ∩ B) \ A).card + 1 := by
  have hxNotGain : x ∉ (X ∩ B) \ A := by
    intro hxGain
    exact hxX ((Finset.mem_inter.mp (Finset.mem_sdiff.mp hxGain).1).1)
  rw [sdiff_eq_insert_inter_sdiff_of_subset_of_subset_insert_of_mem
    hA hB hxX hxB]
  exact Finset.card_insert_of_notMem hxNotGain

/--
When `X` already has at least `q` alternatives, a q-acceptant rule chooses the
same number from `X` and `insert x X`.
-/
theorem qAcceptant_card_choice_insert_eq_of_le_card
    {q : ℕ} {C : ChoiceRule α} (haccept : QAcceptant q C)
    {X : Finset α} {x : α} (hcard : q ≤ X.card) :
    (C X).card = (C (insert x X)).card := by
  have hX_subset : X ⊆ insert x X := by
    intro y hy
    exact Finset.mem_insert_of_mem hy
  have hcard_insert : q ≤ (insert x X).card :=
    hcard.trans (Finset.card_le_card hX_subset)
  rw [haccept X, haccept (insert x X)]
  rw [Nat.min_eq_left hcard, Nat.min_eq_left hcard_insert]

/--
Instability calculation, fresh entrant not chosen: the gain and loss terms have
the same cardinality, so the distance is twice the number of displaced old
choices.
-/
theorem choiceDistance_insert_eq_two_mul_loss_of_not_mem
    {q : ℕ} {C : ChoiceRule α} (hfeasible : Feasible C)
    (haccept : QAcceptant q C)
    {X : Finset α} {x : α} (hcard : q ≤ X.card)
    (hxNotChosen : x ∉ C (insert x X)) :
    choiceDistance C X (insert x X) =
      2 * (C X \ C (insert x X)).card := by
  let X' : Finset α := insert x X
  change choiceDistance C X X' = 2 * choiceLossTerm C X X'
  have hcard_eq : (C X).card = (C X').card := by
    simpa [X'] using
      qAcceptant_card_choice_insert_eq_of_le_card
        (C := C) (x := x) haccept hcard
  have hnew_eq_gain :
      (C X' \ C X).card = ((X ∩ C X') \ C X).card := by
    have hset :
        C X' \ C X = (X ∩ C X') \ C X :=
      sdiff_eq_inter_sdiff_of_subset_insert_of_not_mem
        (A := C X) (B := C X') (X := X) (x := x)
        (by simpa [X'] using hfeasible X')
        (by simpa [X'] using hxNotChosen)
    simp [hset]
  have hloss_eq_gain :
      choiceLossTerm C X X' = choiceGainTerm C X X' := by
    rw [choiceLossTerm, choiceGainTerm]
    rw [Finset.card_sdiff_comm hcard_eq]
    exact hnew_eq_gain
  rw [choiceDistance, hloss_eq_gain]
  omega

/--
Instability calculation, fresh entrant chosen: the gain term is one smaller
than the loss term.
-/
theorem choiceDistance_insert_add_one_eq_two_mul_loss_of_mem
    {q : ℕ} {C : ChoiceRule α} (hfeasible : Feasible C)
    (haccept : QAcceptant q C)
    {X : Finset α} {x : α} (hcard : q ≤ X.card)
    (hxX : x ∉ X) (hxChosen : x ∈ C (insert x X)) :
    choiceDistance C X (insert x X) + 1 =
      2 * (C X \ C (insert x X)).card := by
  let X' : Finset α := insert x X
  change choiceDistance C X X' + 1 = 2 * choiceLossTerm C X X'
  have hcard_eq : (C X).card = (C X').card := by
    simpa [X'] using
      qAcceptant_card_choice_insert_eq_of_le_card
        (C := C) (x := x) haccept hcard
  have hnew_eq_gain_add_one :
      (C X' \ C X).card = ((X ∩ C X') \ C X).card + 1 := by
    exact
      card_sdiff_eq_card_inter_sdiff_add_one_of_subset_of_subset_insert_of_mem
        (A := C X) (B := C X') (X := X) (x := x)
        (hfeasible X) (by simpa [X'] using hfeasible X') hxX
        (by simpa [X'] using hxChosen)
  have hloss_eq_gain_add_one :
      choiceLossTerm C X X' = choiceGainTerm C X X' + 1 := by
    rw [choiceLossTerm, choiceGainTerm]
    rw [Finset.card_sdiff_comm hcard_eq]
    exact hnew_eq_gain_add_one
  rw [choiceDistance, hloss_eq_gain_add_one]
  omega

/--
Combined indicator-style instability calculation.  The chosen-newcomer case is
`2 * n - 1`; the rejected-newcomer case is `2 * n`.
-/
theorem choiceDistance_insert_eq_if_mem
    {q : ℕ} {C : ChoiceRule α} (hfeasible : Feasible C)
    (haccept : QAcceptant q C)
    {X : Finset α} {x : α} (hcard : q ≤ X.card) (hxX : x ∉ X) :
    choiceDistance C X (insert x X) =
      if x ∈ C (insert x X) then
        2 * (C X \ C (insert x X)).card - 1
      else
        2 * (C X \ C (insert x X)).card := by
  by_cases hxChosen : x ∈ C (insert x X)
  · simp [hxChosen]
    have hcalc :=
      choiceDistance_insert_add_one_eq_two_mul_loss_of_mem
        (C := C) (q := q) hfeasible haccept hcard hxX hxChosen
    omega
  · simp [hxChosen]
    exact
      choiceDistance_insert_eq_two_mul_loss_of_not_mem
        (C := C) (q := q) hfeasible haccept hcard hxChosen

/--
If a fresh inserted applicant is not chosen, consistency forces the post-insert
choice set to equal the pre-insert choice set, so the choice distance is zero.
-/
theorem choiceDistance_insert_eq_zero_of_consistent_of_fresh_not_chosen
    {C : ChoiceRule α} (hfeasible : Feasible C) (hcons : Consistent C)
    {X : Finset α} {x : α} (hxNotChosen : x ∉ C (insert x X)) :
    choiceDistance C X (insert x X) = 0 := by
  have hchosen_subset : C (insert x X) ⊆ X := by
    intro y hy
    have hyInsert : y ∈ insert x X := hfeasible (insert x X) hy
    rw [Finset.mem_insert] at hyInsert
    rcases hyInsert with rfl | hyX
    · exact False.elim (hxNotChosen hy)
    · exact hyX
  have hX_subset : X ⊆ insert x X := by
    intro y hy
    exact Finset.mem_insert_of_mem hy
  have hsame : C (insert x X) = C X :=
    hcons hchosen_subset hX_subset
  have hinter : X ∩ C X = C X := by
    exact Finset.inter_eq_right.mpr (hfeasible X)
  simp [choiceDistance, choiceGainTerm, choiceLossTerm, hsame, hinter]

/--
Consequently, if a fresh inserted applicant is not chosen but the choice
distance is positive, the rule is not consistent.
-/
theorem not_consistent_of_choiceDistance_pos_of_fresh_not_chosen
    {C : ChoiceRule α} (hfeasible : Feasible C)
    {X : Finset α} {x : α} (hxNotChosen : x ∉ C (insert x X))
    (hpositive : 0 < choiceDistance C X (insert x X)) :
    ¬ Consistent C := by
  intro hcons
  have hzero :=
    choiceDistance_insert_eq_zero_of_consistent_of_fresh_not_chosen
      (C := C) hfeasible hcons hxNotChosen
  omega

/--
If adding a fresh applicant changes the chosen set and the fresh applicant is
not chosen after being added, then the one-step choice distance is positive.
-/
theorem choiceDistance_insert_pos_of_choice_ne_of_fresh_not_chosen
    {C : ChoiceRule α} (hfeasible : Feasible C)
    {X : Finset α} {x : α}
    (hxNotChosen : x ∉ C (insert x X))
    (hne : C (insert x X) ≠ C X) :
    0 < choiceDistance C X (insert x X) := by
  have hpost_subset_X : C (insert x X) ⊆ X := by
    intro y hy
    have hyOffer : y ∈ insert x X := hfeasible (insert x X) hy
    rw [Finset.mem_insert] at hyOffer
    rcases hyOffer with rfl | hyX
    · exact False.elim (hxNotChosen hy)
    · exact hyX
  by_contra hnot
  have hzero : choiceDistance C X (insert x X) = 0 :=
    Nat.eq_zero_of_not_pos hnot
  rw [choiceDistance] at hzero
  rcases Nat.add_eq_zero_iff.mp hzero with ⟨hgain_zero, hloss_zero⟩
  have hpost_subset_pre : C (insert x X) ⊆ C X := by
    have hsubset :
        X ∩ C (insert x X) ⊆ C X :=
      (card_sdiff_eq_zero_iff_subset
        (X ∩ C (insert x X)) (C X)).mp hgain_zero
    intro y hy
    exact hsubset (Finset.mem_inter.mpr ⟨hpost_subset_X hy, hy⟩)
  have hpre_subset_post : C X ⊆ C (insert x X) :=
    (card_sdiff_eq_zero_iff_subset (C X) (C (insert x X))).mp hloss_zero
  exact hne (Finset.Subset.antisymm hpost_subset_pre hpre_subset_post)

/--
Converse even-instability observation: if a feasible q-acceptant rule is not
consistent, then some single fresh addition has positive even choice distance.
-/
theorem exists_positive_even_choiceDistance_insert_of_not_consistent
    {q : ℕ} {C : ChoiceRule α}
    (hfeasible : Feasible C) (haccept : QAcceptant q C)
    (hnot : ¬ Consistent C) :
    ∃ X x, x ∉ X ∧ 0 < choiceDistance C X (insert x X) ∧
      ∃ k, choiceDistance C X (insert x X) = 2 * k := by
  classical
  let bad : ℕ → Prop := fun n =>
    ∃ X Y, C Y ⊆ X ∧ X ⊆ Y ∧ C Y ≠ C X ∧ (Y \ X).card = n
  have hbad_exists : ∃ n, bad n := by
    rw [Consistent] at hnot
    push Not at hnot
    rcases hnot with ⟨X, Y, hchosen_subset, hsubset, hne⟩
    exact ⟨(Y \ X).card, X, Y, hchosen_subset, hsubset, hne, rfl⟩
  let n : ℕ := Nat.find hbad_exists
  rcases Nat.find_spec hbad_exists with
    ⟨X, Y, hCY_subset_X, hX_subset_Y, hCY_ne_CX, hcard⟩
  have hnpos : 0 < n := by
    by_contra hnnot
    have hnzero : n = 0 := Nat.eq_zero_of_not_pos hnnot
    have hfind_zero : Nat.find hbad_exists = 0 := by
      simpa [n] using hnzero
    have hsdiff_zero : (Y \ X).card = 0 := by
      rw [hcard, hfind_zero]
    have hY_subset_X : Y ⊆ X :=
      (card_sdiff_eq_zero_iff_subset Y X).mp hsdiff_zero
    have hYX : Y = X := Finset.Subset.antisymm hY_subset_X hX_subset_Y
    exact hCY_ne_CX (by rw [hYX])
  have hsdiff_pos : 0 < (Y \ X).card := by
    rw [hcard]
    exact hnpos
  rcases Finset.card_pos.mp hsdiff_pos with ⟨x, hx_sdiff⟩
  rcases Finset.mem_sdiff.mp hx_sdiff with ⟨hxY, hxX⟩
  let Z : Finset α := Y.erase x
  have hxZ : x ∉ Z := by
    simp [Z]
  have hY_insert : insert x Z = Y := by
    simpa [Z] using (Finset.insert_erase hxY)
  have hX_subset_Z : X ⊆ Z := by
    intro y hyX
    have hy_ne_x : y ≠ x := by
      intro hyx
      exact hxX (by simpa [hyx] using hyX)
    exact Finset.mem_erase.mpr ⟨hy_ne_x, hX_subset_Y hyX⟩
  have hCY_ne_CZ : C Y ≠ C Z := by
    intro hCY_eq_CZ
    have hbad_smaller : bad ((Z \ X).card) := by
      refine ⟨X, Z, ?_, hX_subset_Z, ?_, rfl⟩
      · intro y hy
        exact hCY_subset_X (by simpa [hCY_eq_CZ] using hy)
      · intro hCZ_eq_CX
        exact hCY_ne_CX (by
          rw [hCY_eq_CZ]
          exact hCZ_eq_CX)
    have hmin := Nat.find_min' hbad_exists hbad_smaller
    have hlt_find : (Z \ X).card < Nat.find hbad_exists := by
      rw [← hcard]
      apply Finset.card_lt_card
      refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
      · intro y hy
        rcases Finset.mem_sdiff.mp hy with ⟨hyZ, hyX⟩
        exact Finset.mem_sdiff.mpr
          ⟨Finset.mem_of_mem_erase hyZ, hyX⟩
      · intro heq
        have hx_in_Z_sdiff : x ∈ Z \ X := by
          simpa [heq] using hx_sdiff
        exact hxZ (Finset.mem_sdiff.mp hx_in_Z_sdiff).1
    have hlt : (Z \ X).card < n := by
      simpa [n] using hlt_find
    omega
  have hxNotChosenY : x ∉ C Y := by
    intro hxCY
    exact hxX (hCY_subset_X hxCY)
  have hxNotChosen : x ∉ C (insert x Z) := by
    simpa [hY_insert] using hxNotChosenY
  have hcardZ : q ≤ Z.card := by
    by_contra hnotle
    have hZ_lt_q : Z.card < q := Nat.lt_of_not_ge hnotle
    have hY_card_le_q : Y.card ≤ q := by
      rw [← hY_insert, Finset.card_insert_of_notMem hxZ]
      omega
    have hCY_eq_Y : C Y = Y :=
      QAcceptant.eq_of_card_le hfeasible haccept hY_card_le_q
    exact hxNotChosenY (by rw [hCY_eq_Y]; exact hxY)
  have hpositive : 0 < choiceDistance C Z (insert x Z) := by
    have hne_insert : C (insert x Z) ≠ C Z := by
      simpa [hY_insert] using hCY_ne_CZ
    exact choiceDistance_insert_pos_of_choice_ne_of_fresh_not_chosen
      (C := C) hfeasible hxNotChosen hne_insert
  have hdist_even :
      choiceDistance C Z (insert x Z) =
        2 * (C Z \ C (insert x Z)).card :=
    choiceDistance_insert_eq_two_mul_loss_of_not_mem
      (C := C) (q := q) hfeasible haccept hcardZ hxNotChosen
  exact ⟨Z, x, hxZ, hpositive,
    (C Z \ C (insert x Z)).card, hdist_even⟩

/-- Below capacity, adding one fresh applicant changes no existing decisions. -/
theorem choiceDistance_insert_eq_zero_of_qAcceptant_of_card_lt
    {q : ℕ} {C : ChoiceRule α} (hfeasible : Feasible C)
    (haccept : QAcceptant q C)
    {X : Finset α} {x : α} (hcard : X.card < q) (hx : x ∉ X) :
    choiceDistance C X (insert x X) = 0 := by
  have hX_le : X.card ≤ q := le_of_lt hcard
  have hInsert_le : (insert x X).card ≤ q := by
    rw [Finset.card_insert_of_notMem hx]
    omega
  have hCX : C X = X :=
    QAcceptant.eq_of_card_le hfeasible haccept hX_le
  have hCX' : C (insert x X) = insert x X :=
    QAcceptant.eq_of_card_le hfeasible haccept hInsert_le
  simp [choiceDistance, choiceGainTerm, choiceLossTerm, hCX, hCX']

/--
For feasible q-acceptant consistent rules, a two-instability bound collapses
to one-instability. This is the first even case of the general observation that
consistent rules cannot be tightly even-unstable.
-/
theorem dUnstable_one_of_dUnstable_two_of_feasible_of_qAcceptant_of_consistent
    {q : ℕ} {C : ChoiceRule α}
    (hfeasible : Feasible C) (haccept : QAcceptant q C)
    (hcons : Consistent C) (hunstable : DUnstable 2 C) :
    DUnstable 1 C := by
  intro X x hx
  by_cases hsmall : X.card < q
  · have hzero :=
      choiceDistance_insert_eq_zero_of_qAcceptant_of_card_lt
        (C := C) hfeasible haccept hsmall hx
    omega
  · have hcard : q ≤ X.card := Nat.le_of_not_gt hsmall
    by_cases hxChosen : x ∈ C (insert x X)
    · have hcalc :=
        choiceDistance_insert_eq_if_mem
          (C := C) hfeasible haccept hcard hx
      have hdist := hunstable X x hx
      simp [hxChosen] at hcalc
      rw [hcalc] at hdist ⊢
      omega
    · have hzero :=
        choiceDistance_insert_eq_zero_of_consistent_of_fresh_not_chosen
          (C := C) hfeasible hcons hxChosen
      omega

/--
For feasible q-acceptant consistent rules, an even instability bound is never
tight: every `2*k` bound with `k > 0` improves to `2*k - 1`.
-/
theorem dUnstable_pred_of_dUnstable_even_of_feasible_of_qAcceptant_of_consistent
    {q k : ℕ} {C : ChoiceRule α}
    (hk : 0 < k) (hfeasible : Feasible C) (haccept : QAcceptant q C)
    (hcons : Consistent C) (hunstable : DUnstable (2 * k) C) :
    DUnstable (2 * k - 1) C := by
  intro X x hx
  by_cases hsmall : X.card < q
  · have hzero :=
      choiceDistance_insert_eq_zero_of_qAcceptant_of_card_lt
        (C := C) hfeasible haccept hsmall hx
    omega
  · have hcard : q ≤ X.card := Nat.le_of_not_gt hsmall
    by_cases hxChosen : x ∈ C (insert x X)
    · have hcalc :=
        choiceDistance_insert_eq_if_mem
          (C := C) hfeasible haccept hcard hx
      have hdist := hunstable X x hx
      simp [hxChosen] at hcalc
      rw [hcalc] at hdist ⊢
      omega
    · have hzero :=
        choiceDistance_insert_eq_zero_of_consistent_of_fresh_not_chosen
        (C := C) hfeasible hcons hxChosen
      omega

/--
If every nontrivial one-step change chooses the fresh applicant, then the crude
`2q` q-acceptance bound improves to `2q - 1`.
-/
theorem dUnstable_two_mul_sub_one_of_feasible_of_qAcceptant_of_not_chosen_eq_self
    {q : ℕ} {C : ChoiceRule α}
    (hfeasible : Feasible C) (haccept : QAcceptant q C)
    (hstable :
      ∀ X x, x ∉ X → x ∉ C (insert x X) → C (insert x X) = C X) :
    DUnstable (2 * q - 1) C := by
  intro X x hx
  by_cases hsmall : X.card < q
  · have hzero :=
      choiceDistance_insert_eq_zero_of_qAcceptant_of_card_lt
        (C := C) hfeasible haccept hsmall hx
    omega
  · have hcard : q ≤ X.card := Nat.le_of_not_gt hsmall
    by_cases hxChosen : x ∈ C (insert x X)
    · have hcalc :=
        choiceDistance_insert_eq_if_mem
          (C := C) hfeasible haccept hcard hx
      have hloss_le : (C X \ C (insert x X)).card ≤ q := by
        have hsubset : C X \ C (insert x X) ⊆ C X := by
          intro y hy
          exact (Finset.mem_sdiff.mp hy).1
        exact (Finset.card_le_card hsubset).trans
          (QAcceptant.card_le haccept X)
      simp [hxChosen] at hcalc
      rw [hcalc]
      omega
    · have hsame : C (insert x X) = C X :=
        hstable X x hx hxChosen
      have hinter : X ∩ C X = C X :=
        Finset.inter_eq_right.mpr (hfeasible X)
      simp [choiceDistance, choiceGainTerm, choiceLossTerm, hsame, hinter]

/--
Feasible q-representative choice rules are substitutable.  The fixed
representing order rules out an old rejected element becoming chosen: equal
q-acceptant cardinalities force some old chosen element to be displaced, which
would put the two elements above each other in the strict order.
-/
theorem substitutable_of_feasible_of_qRepresentative
    {q : ℕ} {C : ChoiceRule α}
    (hfeasible : Feasible C) (hrep : QRepresentative q C) :
    Substitutable C := by
  rcases hrep with ⟨r, hstrict, _hrep_feasible, haccept, hpriority⟩
  intro X₁ X₂ hsubset x hx
  rcases Finset.mem_inter.mp hx with ⟨hxX₁, hxCX₂⟩
  by_contra hxnotCX₁
  by_cases hX₁_le_q : X₁.card ≤ q
  · have hCX₁ : C X₁ = X₁ :=
      QAcceptant.eq_of_card_le hfeasible haccept hX₁_le_q
    exact hxnotCX₁ (by simpa [hCX₁] using hxX₁)
  · have hq_lt_X₁ : q < X₁.card := Nat.lt_of_not_ge hX₁_le_q
    have hq_le_X₁ : q ≤ X₁.card := le_of_lt hq_lt_X₁
    have hq_le_X₂ : q ≤ X₂.card :=
      hq_le_X₁.trans (Finset.card_le_card hsubset)
    have hcard_eq : (C X₁).card = (C X₂).card := by
      rw [haccept X₁, haccept X₂]
      rw [Nat.min_eq_left hq_le_X₁, Nat.min_eq_left hq_le_X₂]
    have hx_sdiff : x ∈ C X₂ \ C X₁ :=
      Finset.mem_sdiff.mpr ⟨hxCX₂, hxnotCX₁⟩
    rcases exists_mem_sdiff_of_card_eq_of_mem_sdiff hcard_eq hx_sdiff with
      ⟨y, hy_sdiff⟩
    rcases Finset.mem_sdiff.mp hy_sdiff with ⟨hyCX₁, hyNotCX₂⟩
    have hyX₁ : y ∈ X₁ := hfeasible X₁ hyCX₁
    have hyX₂ : y ∈ X₂ := hsubset hyX₁
    have hyx : r y x := hpriority hyCX₁ hxX₁ hxnotCX₁
    have hxy : r x y := hpriority hxCX₂ hyX₂ hyNotCX₂
    exact (hstrict.asymm hxy) hyx

/-- Feasible q-representative choice rules are 1-unstable for one fresh addition. -/
theorem dUnstable_one_of_feasible_of_qRepresentative
    {q : ℕ} {C : ChoiceRule α}
    (hfeasible : Feasible C) (hrep : QRepresentative q C) :
    DUnstable 1 C := by
  exact dUnstable_one_of_feasible_of_qAcceptant_of_substitutable
    (C := C) hfeasible hrep.qAcceptant
    (substitutable_of_feasible_of_qRepresentative hfeasible hrep)

/-! ## Trigger-switch choice rules -/

/--
Switch between two choice rules according to a finite-pool trigger predicate.
This is useful for construction proofs where one priority rule applies before
a trigger is present and another priority rule applies afterward.
-/
def triggerSwitchChoice
    (τ : Finset α → Prop) [DecidablePred τ] (F₀ F₁ : ChoiceRule α) :
    ChoiceRule α :=
  fun X => if τ X then F₁ X else F₀ X

/-- A trigger switch of feasible rules is feasible. -/
theorem triggerSwitchChoice_feasible
    {τ : Finset α → Prop} [DecidablePred τ] {F₀ F₁ : ChoiceRule α}
    (hF₀feas : Feasible F₀) (hF₁feas : Feasible F₁) :
    Feasible (triggerSwitchChoice τ F₀ F₁) := by
  intro X
  unfold triggerSwitchChoice
  split_ifs with hτ
  · exact hF₁feas X
  · exact hF₀feas X

/-- A trigger switch of q-acceptant rules is q-acceptant. -/
theorem triggerSwitchChoice_qAcceptant
    {q : ℕ} {τ : Finset α → Prop} [DecidablePred τ] {F₀ F₁ : ChoiceRule α}
    (hF₀accept : QAcceptant q F₀) (hF₁accept : QAcceptant q F₁) :
    QAcceptant q (triggerSwitchChoice τ F₀ F₁) := by
  intro X
  unfold triggerSwitchChoice
  split_ifs with hτ
  · exact hF₁accept X
  · exact hF₀accept X

/--
Even-distance trigger-switch upper bound.  If both modes are feasible
q-representative rules and false-to-true trigger changes lose at most `n`
old choices, then the switched rule is `2*n`-unstable.
-/
theorem triggerSwitchChoice_dUnstable_even
    {q n : ℕ} (hn : 0 < n)
    {τ : Finset α → Prop} [DecidablePred τ] {F₀ F₁ : ChoiceRule α}
    (hτmono : ∀ {X x}, x ∉ X → τ X → τ (insert x X))
    (hF₀feas : Feasible F₀) (hF₁feas : Feasible F₁)
    (hF₀rep : QRepresentative q F₀)
    (hF₁rep : QRepresentative q F₁)
    (hcross :
      ∀ X x, x ∉ X → ¬ τ X → τ (insert x X) →
        (F₀ X \ F₁ (insert x X)).card ≤ n) :
    DUnstable (2 * n) (triggerSwitchChoice τ F₀ F₁) := by
  let C : ChoiceRule α := triggerSwitchChoice τ F₀ F₁
  have hCfeas : Feasible C :=
    triggerSwitchChoice_feasible hF₀feas hF₁feas
  have hCaccept : QAcceptant q C :=
    triggerSwitchChoice_qAcceptant hF₀rep.qAcceptant hF₁rep.qAcceptant
  intro X x hx
  change choiceDistance C X (insert x X) ≤ 2 * n
  by_cases hτX : τ X
  · have hτInsert : τ (insert x X) := hτmono hx hτX
    have hstep : choiceDistance F₁ X (insert x X) ≤ 1 :=
      (dUnstable_one_of_feasible_of_qRepresentative hF₁feas hF₁rep) X x hx
    have hCeq :
        choiceDistance C X (insert x X) =
          choiceDistance F₁ X (insert x X) := by
      simp [C, triggerSwitchChoice, choiceDistance, choiceGainTerm, choiceLossTerm,
        hτX, hτInsert]
    rw [hCeq]
    omega
  · by_cases hτInsert : τ (insert x X)
    · by_cases hcard : q ≤ X.card
      · have hdist_eq :
            choiceDistance C X (insert x X) =
              if x ∈ C (insert x X) then
                2 * (C X \ C (insert x X)).card - 1
              else
                2 * (C X \ C (insert x X)).card := by
          exact choiceDistance_insert_eq_if_mem
            (C := C) (q := q) hCfeas hCaccept hcard hx
        have hloss : (C X \ C (insert x X)).card ≤ n := by
          simpa [C, triggerSwitchChoice, hτX, hτInsert] using
            hcross X x hx hτX hτInsert
        rw [hdist_eq]
        by_cases hxChosen : x ∈ C (insert x X)
        · simp [hxChosen]
          omega
        · simp [hxChosen]
          omega
      · have hX_le : X.card ≤ q := Nat.le_of_lt (Nat.lt_of_not_ge hcard)
        have hInsert_le : (insert x X).card ≤ q := by
          rw [Finset.card_insert_of_notMem hx]
          omega
        have hCX : C X = X :=
          QAcceptant.eq_of_card_le hCfeas hCaccept hX_le
        have hCInsert : C (insert x X) = insert x X :=
          QAcceptant.eq_of_card_le hCfeas hCaccept hInsert_le
        have hdist_zero : choiceDistance C X (insert x X) = 0 := by
          rw [choiceDistance, choiceGainTerm, choiceLossTerm, hCX, hCInsert]
          have hinter : X ∩ insert x X = X := by
            apply Finset.Subset.antisymm
            · intro y hy
              exact (Finset.mem_inter.mp hy).1
            · intro y hy
              exact Finset.mem_inter.mpr ⟨hy, Finset.mem_insert_of_mem hy⟩
          have hsdiff : X \ insert x X = ∅ := by
            rw [Finset.sdiff_eq_empty_iff_subset]
            intro y hy
            exact Finset.mem_insert_of_mem hy
          simp [hinter, hsdiff]
        rw [hdist_zero]
        omega
    · have hstep : choiceDistance F₀ X (insert x X) ≤ 1 :=
        (dUnstable_one_of_feasible_of_qRepresentative hF₀feas hF₀rep) X x hx
      have hCeq :
          choiceDistance C X (insert x X) =
            choiceDistance F₀ X (insert x X) := by
        simp [C, triggerSwitchChoice, choiceDistance, choiceGainTerm, choiceLossTerm,
          hτX, hτInsert]
      rw [hCeq]
      omega

/--
Odd-distance trigger-switch upper bound.  If false-to-true trigger changes
lose at most `n` old choices and choose the fresh trigger applicant, the
switched rule is `(2*n - 1)`-unstable.
-/
theorem triggerSwitchChoice_dUnstable_odd
    {q n : ℕ} (hn : 0 < n)
    {τ : Finset α → Prop} [DecidablePred τ] {F₀ F₁ : ChoiceRule α}
    (hτmono : ∀ {X x}, x ∉ X → τ X → τ (insert x X))
    (hF₀feas : Feasible F₀) (hF₁feas : Feasible F₁)
    (hF₀rep : QRepresentative q F₀)
    (hF₁rep : QRepresentative q F₁)
    (hcross_loss :
      ∀ X x, x ∉ X → ¬ τ X → τ (insert x X) →
        (F₀ X \ F₁ (insert x X)).card ≤ n)
    (hcross_chosen :
      ∀ X x, x ∉ X → ¬ τ X → τ (insert x X) →
        x ∈ F₁ (insert x X)) :
    DUnstable (2 * n - 1) (triggerSwitchChoice τ F₀ F₁) := by
  let C : ChoiceRule α := triggerSwitchChoice τ F₀ F₁
  have hCfeas : Feasible C :=
    triggerSwitchChoice_feasible hF₀feas hF₁feas
  have hCaccept : QAcceptant q C :=
    triggerSwitchChoice_qAcceptant hF₀rep.qAcceptant hF₁rep.qAcceptant
  intro X x hx
  change choiceDistance C X (insert x X) ≤ 2 * n - 1
  by_cases hτX : τ X
  · have hτInsert : τ (insert x X) := hτmono hx hτX
    have hstep : choiceDistance F₁ X (insert x X) ≤ 1 :=
      (dUnstable_one_of_feasible_of_qRepresentative hF₁feas hF₁rep) X x hx
    have hCeq :
        choiceDistance C X (insert x X) =
          choiceDistance F₁ X (insert x X) := by
      simp [C, triggerSwitchChoice, choiceDistance, choiceGainTerm, choiceLossTerm,
        hτX, hτInsert]
    rw [hCeq]
    omega
  · by_cases hτInsert : τ (insert x X)
    · by_cases hcard : q ≤ X.card
      · have hdist_eq :
            choiceDistance C X (insert x X) =
              if x ∈ C (insert x X) then
                2 * (C X \ C (insert x X)).card - 1
              else
                2 * (C X \ C (insert x X)).card := by
          exact choiceDistance_insert_eq_if_mem
            (C := C) (q := q) hCfeas hCaccept hcard hx
        have hloss : (C X \ C (insert x X)).card ≤ n := by
          simpa [C, triggerSwitchChoice, hτX, hτInsert] using
            hcross_loss X x hx hτX hτInsert
        have hxChosenC : x ∈ C (insert x X) := by
          simpa [C, triggerSwitchChoice, hτInsert] using
            hcross_chosen X x hx hτX hτInsert
        rw [hdist_eq]
        simp [hxChosenC]
        omega
      · have hX_le : X.card ≤ q := Nat.le_of_lt (Nat.lt_of_not_ge hcard)
        have hInsert_le : (insert x X).card ≤ q := by
          rw [Finset.card_insert_of_notMem hx]
          omega
        have hCX : C X = X :=
          QAcceptant.eq_of_card_le hCfeas hCaccept hX_le
        have hCInsert : C (insert x X) = insert x X :=
          QAcceptant.eq_of_card_le hCfeas hCaccept hInsert_le
        have hdist_zero : choiceDistance C X (insert x X) = 0 := by
          rw [choiceDistance, choiceGainTerm, choiceLossTerm, hCX, hCInsert]
          have hinter : X ∩ insert x X = X := by
            apply Finset.Subset.antisymm
            · intro y hy
              exact (Finset.mem_inter.mp hy).1
            · intro y hy
              exact Finset.mem_inter.mpr ⟨hy, Finset.mem_insert_of_mem hy⟩
          have hsdiff : X \ insert x X = ∅ := by
            rw [Finset.sdiff_eq_empty_iff_subset]
            intro y hy
            exact Finset.mem_insert_of_mem hy
          simp [hinter, hsdiff]
        rw [hdist_zero]
        omega
    · have hstep : choiceDistance F₀ X (insert x X) ≤ 1 :=
        (dUnstable_one_of_feasible_of_qRepresentative hF₀feas hF₀rep) X x hx
      have hCeq :
          choiceDistance C X (insert x X) =
            choiceDistance F₀ X (insert x X) := by
        simp [C, triggerSwitchChoice, choiceDistance, choiceGainTerm, choiceLossTerm,
          hτX, hτInsert]
      rw [hCeq]
      omega

/--
Even-distance trigger-switch tightness.  An exact false-to-true switch witness
with `n` displaced old choices makes the `2*n` upper bound tight.
-/
theorem triggerSwitchChoice_tightly_even
    {q n : ℕ} (hn : 0 < n)
    {τ : Finset α → Prop} [DecidablePred τ] {F₀ F₁ : ChoiceRule α}
    (hτmono : ∀ {X x}, x ∉ X → τ X → τ (insert x X))
    (hF₀feas : Feasible F₀) (hF₁feas : Feasible F₁)
    (hF₀rep : QRepresentative q F₀)
    (hF₁rep : QRepresentative q F₁)
    (hcross :
      ∀ X x, x ∉ X → ¬ τ X → τ (insert x X) →
        (F₀ X \ F₁ (insert x X)).card ≤ n)
    {X₀ : Finset α} {z : α}
    (hzX₀ : z ∉ X₀) (hcard : q ≤ X₀.card)
    (hbefore : ¬ τ X₀) (hafter : τ (insert z X₀))
    (hzRejected : z ∉ F₁ (insert z X₀))
    (hloss : (F₀ X₀ \ F₁ (insert z X₀)).card = n) :
    TightlyDUnstable (2 * n) (triggerSwitchChoice τ F₀ F₁) := by
  let C : ChoiceRule α := triggerSwitchChoice τ F₀ F₁
  have hCfeas : Feasible C :=
    triggerSwitchChoice_feasible hF₀feas hF₁feas
  have hCaccept : QAcceptant q C :=
    triggerSwitchChoice_qAcceptant hF₀rep.qAcceptant hF₁rep.qAcceptant
  have hunstable : DUnstable (2 * n) C :=
    triggerSwitchChoice_dUnstable_even
      (q := q) (n := n) hn hτmono hF₀feas hF₁feas
      hF₀rep hF₁rep hcross
  have hzRejectedC : z ∉ C (insert z X₀) := by
    simpa [C, triggerSwitchChoice, hafter] using hzRejected
  have hlossC : (C X₀ \ C (insert z X₀)).card = n := by
    simpa [C, triggerSwitchChoice, hbefore, hafter] using hloss
  have hdist : choiceDistance C X₀ (insert z X₀) = 2 * n := by
    rw [choiceDistance_insert_eq_if_mem
      (C := C) (q := q) hCfeas hCaccept hcard hzX₀]
    simp [hzRejectedC, hlossC]
  exact tightlyDUnstable_of_dUnstable_of_choiceDistance_witness
    (C := C) hunstable ⟨X₀, z, hzX₀, hdist⟩

/--
Odd-distance trigger-switch tightness.  An exact false-to-true switch witness
where the fresh trigger is chosen and `n` old choices are displaced makes the
`2*n - 1` upper bound tight.
-/
theorem triggerSwitchChoice_tightly_odd
    {q n : ℕ} (hn : 0 < n)
    {τ : Finset α → Prop} [DecidablePred τ] {F₀ F₁ : ChoiceRule α}
    (hτmono : ∀ {X x}, x ∉ X → τ X → τ (insert x X))
    (hF₀feas : Feasible F₀) (hF₁feas : Feasible F₁)
    (hF₀rep : QRepresentative q F₀)
    (hF₁rep : QRepresentative q F₁)
    (hcross_loss :
      ∀ X x, x ∉ X → ¬ τ X → τ (insert x X) →
        (F₀ X \ F₁ (insert x X)).card ≤ n)
    (hcross_chosen :
      ∀ X x, x ∉ X → ¬ τ X → τ (insert x X) →
        x ∈ F₁ (insert x X))
    {X₀ : Finset α} {z : α}
    (hzX₀ : z ∉ X₀) (hcard : q ≤ X₀.card)
    (hbefore : ¬ τ X₀) (hafter : τ (insert z X₀))
    (hzChosen : z ∈ F₁ (insert z X₀))
    (hloss : (F₀ X₀ \ F₁ (insert z X₀)).card = n) :
    TightlyDUnstable (2 * n - 1) (triggerSwitchChoice τ F₀ F₁) := by
  let C : ChoiceRule α := triggerSwitchChoice τ F₀ F₁
  have hCfeas : Feasible C :=
    triggerSwitchChoice_feasible hF₀feas hF₁feas
  have hCaccept : QAcceptant q C :=
    triggerSwitchChoice_qAcceptant hF₀rep.qAcceptant hF₁rep.qAcceptant
  have hunstable : DUnstable (2 * n - 1) C :=
    triggerSwitchChoice_dUnstable_odd
      (q := q) (n := n) hn hτmono hF₀feas hF₁feas
      hF₀rep hF₁rep hcross_loss hcross_chosen
  have hzChosenC : z ∈ C (insert z X₀) := by
    simpa [C, triggerSwitchChoice, hafter] using hzChosen
  have hlossC : (C X₀ \ C (insert z X₀)).card = n := by
    simpa [C, triggerSwitchChoice, hbefore, hafter] using hloss
  have hdist : choiceDistance C X₀ (insert z X₀) = 2 * n - 1 := by
    rw [choiceDistance_insert_eq_if_mem
      (C := C) (q := q) hCfeas hCaccept hcard hzX₀]
    simp [hzChosenC, hlossC]
  exact tightlyDUnstable_of_dUnstable_of_choiceDistance_witness
    (C := C) hunstable ⟨X₀, z, hzX₀, hdist⟩

/-- A q-representative rule with a real displacement is tightly 1-unstable. -/
theorem tightlyDUnstable_one_of_feasible_of_qRepresentative_of_hasDisplacement
    {q : ℕ} {C : ChoiceRule α}
    (hfeasible : Feasible C) (hrep : QRepresentative q C)
    (hwitness : HasDisplacement C) :
    TightlyDUnstable 1 C := by
  constructor
  · exact dUnstable_one_of_feasible_of_qRepresentative hfeasible hrep
  · intro k hk
    have hk0 : k = 0 := by omega
    subst k
    intro hzero
    rcases hwitness with ⟨X, x, y, hx, hyCX, hyNotCX'⟩
    have hdist_zero := hzero X x hx
    have hloss_pos : 0 < choiceLossTerm C X (insert x X) := by
      rw [choiceLossTerm]
      exact Finset.card_pos.mpr
        ⟨y, Finset.mem_sdiff.mpr ⟨hyCX, hyNotCX'⟩⟩
    rw [choiceDistance] at hdist_zero
    omega

/-- In a feasible q-representative rule, one fresh applicant displaces at most one old choice. -/
theorem choiceLossTerm_insert_le_one_of_feasible_of_qRepresentative
    {q : ℕ} {C : ChoiceRule α}
    (hfeasible : Feasible C) (hrep : QRepresentative q C)
    {X : Finset α} {x : α} (hx : x ∉ X) :
    choiceLossTerm C X (insert x X) ≤ 1 := by
  have hdist :=
    dUnstable_one_of_feasible_of_qRepresentative
      (C := C) hfeasible hrep X x hx
  rw [choiceDistance] at hdist
  omega

/--
Any two applicants in the borderline set of a feasible q-representative rule
must coincide.
-/
theorem eq_of_mem_borderlineSet_of_feasible_of_qRepresentative
    [Fintype α] {q : ℕ} {C : ChoiceRule α}
    (hfeasible : Feasible C) (hrep : QRepresentative q C)
    {X : Finset α} {y z : α}
    (hyB : y ∈ borderlineSet C X) (hzB : z ∈ borderlineSet C X) :
    y = z := by
  classical
  by_contra hy_ne_z
  rcases hrep with ⟨r, hstrict, hrep_feasible, haccept, hpriority⟩
  have hrep' : QRepresentative q C :=
    ⟨r, hstrict, hrep_feasible, haccept, hpriority⟩
  rw [borderlineSet] at hyB hzB
  rcases Finset.mem_biUnion.mp hyB with ⟨a, _ha, hya⟩
  rcases Finset.mem_biUnion.mp hzB with ⟨b, _hb, hzb⟩
  rcases Finset.mem_sdiff.mp hya with ⟨hyCX, hyNotCa⟩
  rcases Finset.mem_sdiff.mp hzb with ⟨hzCX, hzNotCb⟩
  have hyX : y ∈ X := hfeasible X hyCX
  have hzX : z ∈ X := hfeasible X hzCX
  have ha_not_X : a ∉ X := by
    intro haX
    exact hyNotCa (by simpa [Finset.insert_eq_of_mem haX] using hyCX)
  have hb_not_X : b ∉ X := by
    intro hbX
    exact hzNotCb (by simpa [Finset.insert_eq_of_mem hbX] using hzCX)
  have hLossA : (C X \ C (insert a X)).card ≤ 1 := by
    simpa [choiceLossTerm] using
      choiceLossTerm_insert_le_one_of_feasible_of_qRepresentative
        (C := C) hfeasible hrep' (X := X) (x := a) ha_not_X
  have hLossB : (C X \ C (insert b X)).card ≤ 1 := by
    simpa [choiceLossTerm] using
      choiceLossTerm_insert_le_one_of_feasible_of_qRepresentative
        (C := C) hfeasible hrep' (X := X) (x := b) hb_not_X
  have hzCa : z ∈ C (insert a X) :=
    mem_of_mem_of_ne_lost_of_sdiff_card_le_one
      (A := C X) (B := C (insert a X)) (lost := y) (z := z)
      (Finset.mem_sdiff.mpr ⟨hyCX, hyNotCa⟩) hzCX
      (by intro hzy; exact hy_ne_z hzy.symm) hLossA
  have hyCb : y ∈ C (insert b X) :=
    mem_of_mem_of_ne_lost_of_sdiff_card_le_one
      (A := C X) (B := C (insert b X)) (lost := z) (z := y)
      (Finset.mem_sdiff.mpr ⟨hzCX, hzNotCb⟩) hyCX
      (by intro hyz; exact hy_ne_z hyz) hLossB
  have hr_zy : r z y :=
    hpriority hzCa (Finset.mem_insert_of_mem hyX) hyNotCa
  have hr_yz : r y z :=
    hpriority hyCb (Finset.mem_insert_of_mem hzX) hzNotCb
  exact (hstrict.asymm hr_yz) hr_zy

/-- Feasible q-representative choice rules have main-text variability at most one. -/
theorem variabilityAtMost_one_of_feasible_of_qRepresentative
    [Fintype α] {q : ℕ} {C : ChoiceRule α}
    (hfeasible : Feasible C) (hrep : QRepresentative q C) :
    VariabilityAtMost 1 C := by
  intro X
  classical
  let B : Finset α := borderlineSet C X
  by_cases hB_empty : B = ∅
  · simp [B, hB_empty]
  · rcases Finset.nonempty_of_ne_empty hB_empty with ⟨y, hyB⟩
    have hsubset : B ⊆ ({y} : Finset α) := by
      intro z hzB
      have hz_eq_y : z = y :=
        eq_of_mem_borderlineSet_of_feasible_of_qRepresentative
          (C := C) hfeasible hrep
          (by simpa [B] using hzB) (by simpa [B] using hyB)
      simp [hz_eq_y]
    have hcard := Finset.card_le_card hsubset
    simpa [B] using hcard

/--
Any two applicants in the waitlisted set of a feasible q-representative rule
must coincide.
-/
theorem eq_of_mem_waitlistedSet_of_feasible_of_qRepresentative
    [Fintype α] {q : ℕ} {C : ChoiceRule α}
    (hfeasible : Feasible C) (hrep : QRepresentative q C)
    {X : Finset α} {y z : α}
    (hyW : y ∈ waitlistedSet C X) (hzW : z ∈ waitlistedSet C X) :
    y = z := by
  classical
  by_contra hy_ne_z
  rcases hrep with ⟨r, hstrict, hrep_feasible, haccept, hpriority⟩
  have hrep' : QRepresentative q C :=
    ⟨r, hstrict, hrep_feasible, haccept, hpriority⟩
  have hsub : Substitutable C :=
    substitutable_of_feasible_of_qRepresentative hfeasible hrep'
  have hcons : Consistent C :=
    consistent_of_qAcceptant_of_substitutable haccept hsub
  rw [waitlistedSet] at hyW hzW
  rcases Finset.mem_biUnion.mp hyW with ⟨a, haX, hya⟩
  rcases Finset.mem_sdiff.mp hya with ⟨hyCEraseA, hyNotCX⟩
  rcases Finset.mem_biUnion.mp hzW with ⟨b, hbX, hzb⟩
  rcases Finset.mem_sdiff.mp hzb with ⟨hzCEraseB, hzNotCX⟩
  have hyX : y ∈ X := Finset.mem_of_mem_erase (hfeasible (X.erase a) hyCEraseA)
  have hzX : z ∈ X := Finset.mem_of_mem_erase (hfeasible (X.erase b) hzCEraseB)
  have hq_lt_X : q < X.card := by
    by_contra hnot
    have hcard : X.card ≤ q := Nat.le_of_not_gt hnot
    have hCX : C X = X :=
      QAcceptant.eq_of_card_le hfeasible haccept hcard
    exact hyNotCX (by simpa [hCX] using hyX)
  have hcardCX : (C X).card = q := by
    rw [haccept X, Nat.min_eq_left (le_of_lt hq_lt_X)]
  have haCX : a ∈ C X := by
    by_contra haNotCX
    have hchosen_subset : C X ⊆ X.erase a := by
      intro t ht
      exact Finset.mem_erase.mpr
        ⟨by
          intro hta
          subst t
          exact haNotCX ht,
          hfeasible X ht⟩
    have hsame : C X = C (X.erase a) :=
      hcons hchosen_subset (Finset.erase_subset a X)
    exact hyNotCX (by simpa [hsame] using hyCEraseA)
  have hbCX : b ∈ C X := by
    by_contra hbNotCX
    have hchosen_subset : C X ⊆ X.erase b := by
      intro t ht
      exact Finset.mem_erase.mpr
        ⟨by
          intro htb
          subst t
          exact hbNotCX ht,
          hfeasible X ht⟩
    have hsame : C X = C (X.erase b) :=
      hcons hchosen_subset (Finset.erase_subset b X)
    exact hzNotCX (by simpa [hsame] using hzCEraseB)
  have hcardEraseA : q ≤ (X.erase a).card := by
    rw [Finset.card_erase_of_mem haX]
    omega
  have hcardEraseB : q ≤ (X.erase b).card := by
    rw [Finset.card_erase_of_mem hbX]
    omega
  have hcardCEraseA : (C (X.erase a)).card = q := by
    rw [haccept (X.erase a), Nat.min_eq_left hcardEraseA]
  have hcardCEraseB : (C (X.erase b)).card = q := by
    rw [haccept (X.erase b), Nat.min_eq_left hcardEraseB]
  have hnewA_card_le_one : (C (X.erase a) \ C X).card ≤ 1 := by
    have hold_loss_subset : C X \ C (X.erase a) ⊆ ({a} : Finset α) := by
      intro t ht
      rcases Finset.mem_sdiff.mp ht with ⟨htCX, htNotErase⟩
      by_contra hta_singleton
      have hta : t ≠ a := by
        intro hta
        exact hta_singleton (by simp [hta])
      have htErase : t ∈ X.erase a :=
        Finset.mem_erase.mpr ⟨hta, hfeasible X htCX⟩
      exact htNotErase
        (hsub (Finset.erase_subset a X)
          (Finset.mem_inter.mpr ⟨htErase, htCX⟩))
    have hcard_eq : (C (X.erase a)).card = (C X).card := by
      rw [hcardCEraseA, hcardCX]
    rw [Finset.card_sdiff_comm hcard_eq]
    exact (Finset.card_le_card hold_loss_subset).trans (by simp)
  have hnewB_card_le_one : (C (X.erase b) \ C X).card ≤ 1 := by
    have hold_loss_subset : C X \ C (X.erase b) ⊆ ({b} : Finset α) := by
      intro t ht
      rcases Finset.mem_sdiff.mp ht with ⟨htCX, htNotErase⟩
      by_contra htb_singleton
      have htb : t ≠ b := by
        intro htb
        exact htb_singleton (by simp [htb])
      have htErase : t ∈ X.erase b :=
        Finset.mem_erase.mpr ⟨htb, hfeasible X htCX⟩
      exact htNotErase
        (hsub (Finset.erase_subset b X)
          (Finset.mem_inter.mpr ⟨htErase, htCX⟩))
    have hcard_eq : (C (X.erase b)).card = (C X).card := by
      rw [hcardCEraseB, hcardCX]
    rw [Finset.card_sdiff_comm hcard_eq]
    exact (Finset.card_le_card hold_loss_subset).trans (by simp)
  have hzNotCEraseA : z ∉ C (X.erase a) := by
    intro hzCEraseA
    have hzCX' : z ∈ C X :=
      mem_of_mem_of_ne_lost_of_sdiff_card_le_one
        (A := C (X.erase a)) (B := C X) (lost := y) (z := z)
        (Finset.mem_sdiff.mpr ⟨hyCEraseA, hyNotCX⟩) hzCEraseA
        (by intro hzy; exact hy_ne_z hzy.symm) hnewA_card_le_one
    exact hzNotCX hzCX'
  have hyNotCEraseB : y ∉ C (X.erase b) := by
    intro hyCEraseB
    have hyCX' : y ∈ C X :=
      mem_of_mem_of_ne_lost_of_sdiff_card_le_one
        (A := C (X.erase b)) (B := C X) (lost := z) (z := y)
        (Finset.mem_sdiff.mpr ⟨hzCEraseB, hzNotCX⟩) hyCEraseB
        (by intro hyz; exact hy_ne_z hyz) hnewB_card_le_one
    exact hyNotCX hyCX'
  have hz_ne_a : z ≠ a := by
    intro hza
    subst z
    exact hzNotCX haCX
  have hy_ne_b : y ≠ b := by
    intro hyb
    subst y
    exact hyNotCX hbCX
  have hzEraseA : z ∈ X.erase a :=
    Finset.mem_erase.mpr ⟨hz_ne_a, hzX⟩
  have hyEraseB : y ∈ X.erase b :=
    Finset.mem_erase.mpr ⟨hy_ne_b, hyX⟩
  have hryz : r y z := hpriority hyCEraseA hzEraseA hzNotCEraseA
  have hrzy : r z y := hpriority hzCEraseB hyEraseB hyNotCEraseB
  exact (hstrict.asymm hryz) hrzy

/-- Feasible q-representative choice rules have waitlisted sets of size at most one. -/
theorem waitlistedSet_card_le_one_of_feasible_of_qRepresentative
    [Fintype α] {q : ℕ} {C : ChoiceRule α}
    (hfeasible : Feasible C) (hrep : QRepresentative q C) (X : Finset α) :
    (waitlistedSet C X).card ≤ 1 := by
  classical
  let W : Finset α := waitlistedSet C X
  by_cases hW_empty : W = ∅
  · simp [W, hW_empty]
  · rcases Finset.nonempty_of_ne_empty hW_empty with ⟨y, hyW⟩
    have hsubset : W ⊆ ({y} : Finset α) := by
      intro z hzW
      have hz_eq_y : z = y :=
        eq_of_mem_waitlistedSet_of_feasible_of_qRepresentative
          (C := C) hfeasible hrep
          (by simpa [W] using hzW) (by simpa [W] using hyW)
      simp [hz_eq_y]
    have hcard := Finset.card_le_card hsubset
    simpa [W] using hcard

/--
For a feasible q-representative rule at full capacity, a changing fresh
insertion has the same old borderline set as the new waitlisted set.
-/
theorem borderlineSet_eq_waitlistedSet_insert_of_feasible_of_qRepresentative_of_choice_ne
    [Fintype α] {q : ℕ} {C : ChoiceRule α}
    (hfeasible : Feasible C) (hrep : QRepresentative q C)
    {X : Finset α} {x : α}
    (hx : x ∉ X) (hcard : q ≤ X.card)
    (hchange : C (insert x X) ≠ C X) :
    borderlineSet C X = waitlistedSet C (insert x X) := by
  classical
  have haccept : QAcceptant q C := hrep.qAcceptant
  have hsub : Substitutable C :=
    substitutable_of_feasible_of_qRepresentative hfeasible hrep
  have hconsistent : Consistent C :=
    consistent_of_qAcceptant_of_substitutable haccept hsub
  have hxChosen : x ∈ C (insert x X) := by
    by_contra hxNotChosen
    exact hchange
      (choice_insert_eq_self_of_consistent_of_fresh_not_chosen
        hfeasible hconsistent hxNotChosen)
  have hxNotCX : x ∉ C X := by
    intro hxCX
    exact hx (hfeasible X hxCX)
  have hcard_eq :
      (C X).card = (C (insert x X)).card := by
    have hCX : (C X).card = q := by
      rw [haccept X, Nat.min_eq_left hcard]
    have hInsert : (C (insert x X)).card = q := by
      rw [haccept (insert x X), Nat.min_eq_left]
      rw [Finset.card_insert_of_notMem hx]
      omega
    exact hCX.trans hInsert.symm
  rcases exists_mem_sdiff_of_card_eq_of_mem_sdiff
      (A := C X) (B := C (insert x X)) hcard_eq
      (Finset.mem_sdiff.mpr ⟨hxChosen, hxNotCX⟩) with
    ⟨y, hyLoss⟩
  have hyBorder : y ∈ borderlineSet C X := by
    rw [borderlineSet]
    exact Finset.mem_biUnion.mpr
      ⟨x, Finset.mem_univ x, hyLoss⟩
  have herase : (insert x X).erase x = X := by
    ext z
    by_cases hzx : z = x
    · subst z
      simp [hx]
    · simp [Finset.mem_erase, hzx]
  have hyWait : y ∈ waitlistedSet C (insert x X) := by
    rw [waitlistedSet]
    exact Finset.mem_biUnion.mpr
      ⟨x, Finset.mem_insert_self x X, by simpa [herase] using hyLoss⟩
  apply Finset.Subset.antisymm
  · intro z hz
    have hzy : z = y :=
      eq_of_mem_borderlineSet_of_feasible_of_qRepresentative
        (C := C) hfeasible hrep hz hyBorder
    simpa [hzy] using hyWait
  · intro z hz
    have hzy : z = y :=
      eq_of_mem_waitlistedSet_of_feasible_of_qRepresentative
        (C := C) hfeasible hrep hz hyWait
    simpa [hzy] using hyBorder

/-- Feasible q-representative choice rules have general variability at most one. -/
theorem generalVariabilityAtMost_one_of_feasible_of_qRepresentative
    [Fintype α] {q : ℕ} {C : ChoiceRule α}
    (hfeasible : Feasible C) (hrep : QRepresentative q C) :
    GeneralVariabilityAtMost 1 C := by
  intro X
  exact ⟨variabilityAtMost_one_of_feasible_of_qRepresentative hfeasible hrep X,
    waitlistedSet_card_le_one_of_feasible_of_qRepresentative hfeasible hrep X⟩

/-- General at-most-one variability plus a displacement witness gives exact general variability one. -/
theorem generalVariabilityExactly_one_of_atMost_one_of_hasDisplacement
    [Fintype α] {C : ChoiceRule α}
    (hatMost : GeneralVariabilityAtMost 1 C) (hwitness : HasDisplacement C) :
    GeneralVariabilityExactly 1 C := by
  refine ⟨hatMost, Or.inl ?_⟩
  rcases hwitness with ⟨X, x, y, _hx, hyCX, hyNotCX'⟩
  refine ⟨X, le_antisymm (hatMost X).1 ?_⟩
  have hyB : y ∈ borderlineSet C X := by
    classical
    rw [borderlineSet]
    exact Finset.mem_biUnion.mpr
      ⟨x, Finset.mem_univ x, Finset.mem_sdiff.mpr ⟨hyCX, hyNotCX'⟩⟩
  have hpos : 0 < (borderlineSet C X).card :=
    Finset.card_pos.mpr ⟨y, hyB⟩
  omega

/--
Feasible q-representative choice rules have exact general variability one
whenever there is an actual one-step displacement.
-/
theorem generalVariabilityExactly_one_of_feasible_of_qRepresentative_of_hasDisplacement
    [Fintype α] {q : ℕ} {C : ChoiceRule α}
    (hfeasible : Feasible C) (hrep : QRepresentative q C)
    (hwitness : HasDisplacement C) :
    GeneralVariabilityExactly 1 C := by
  exact generalVariabilityExactly_one_of_atMost_one_of_hasDisplacement
    (generalVariabilityAtMost_one_of_feasible_of_qRepresentative hfeasible hrep)
    hwitness

/-- At-most-one variability plus a displacement witness gives exact variability one. -/
theorem variabilityExactly_one_of_atMost_one_of_hasDisplacement
    [Fintype α] {C : ChoiceRule α}
    (hatMost : VariabilityAtMost 1 C) (hwitness : HasDisplacement C) :
    VariabilityExactly 1 C := by
  constructor
  · exact hatMost
  · rcases hwitness with ⟨X, x, y, _hx, hyCX, hyNotCX'⟩
    refine ⟨X, le_antisymm (hatMost X) ?_⟩
    have hyB : y ∈ borderlineSet C X := by
      classical
      rw [borderlineSet]
      exact Finset.mem_biUnion.mpr
        ⟨x, Finset.mem_univ x, Finset.mem_sdiff.mpr ⟨hyCX, hyNotCX'⟩⟩
    have hpos : 0 < (borderlineSet C X).card :=
      Finset.card_pos.mpr ⟨y, hyB⟩
    omega

/-- Exact variability one implies that some one-step displacement occurs. -/
theorem hasDisplacement_of_variabilityExactly_one
    [Fintype α] {C : ChoiceRule α}
    (hexact : VariabilityExactly 1 C) :
    HasDisplacement C := by
  classical
  rcases hexact with ⟨_hatMost, X, hcard⟩
  have hpos : 0 < (borderlineSet C X).card := by
    omega
  rcases Finset.card_pos.mp hpos with ⟨y, hyB⟩
  rw [borderlineSet] at hyB
  rcases Finset.mem_biUnion.mp hyB with ⟨x, _hxUniv, hyloss⟩
  rcases Finset.mem_sdiff.mp hyloss with ⟨hyCX, hyNotCX'⟩
  have hxNotX : x ∉ X := by
    intro hxX
    exact hyNotCX'
      (by simpa [Finset.insert_eq_of_mem hxX] using hyCX)
  exact ⟨X, x, y, hxNotX, hyCX, hyNotCX'⟩

/-- Exact variability one is at-most-one variability plus a displacement witness. -/
theorem variabilityExactly_one_iff_atMost_one_and_hasDisplacement
    [Fintype α] {C : ChoiceRule α} :
    VariabilityExactly 1 C ↔
      VariabilityAtMost 1 C ∧ HasDisplacement C := by
  constructor
  · intro hexact
    exact ⟨hexact.1, hasDisplacement_of_variabilityExactly_one hexact⟩
  · rintro ⟨hatMost, hdisp⟩
    exact variabilityExactly_one_of_atMost_one_of_hasDisplacement
      hatMost hdisp

/--
Feasible q-representative choice rules have exact variability one whenever
there is an actual one-step displacement.
-/
theorem variabilityExactly_one_of_feasible_of_qRepresentative_of_hasDisplacement
    [Fintype α] {q : ℕ} {C : ChoiceRule α}
    (hfeasible : Feasible C) (hrep : QRepresentative q C)
    (hwitness : HasDisplacement C) :
    VariabilityExactly 1 C := by
  exact variabilityExactly_one_of_atMost_one_of_hasDisplacement
    (variabilityAtMost_one_of_feasible_of_qRepresentative hfeasible hrep)
    hwitness

/--
If `C` is substitutable, then removing the choices of `C` preserves inclusion
of feasible sets.
-/
theorem sdiff_choice_subset_sdiff_choice_of_subset_of_substitutable
    {C : ChoiceRule α} (hsub : Substitutable C)
    {X₁ X₂ : Finset α} (hsubset : X₁ ⊆ X₂) :
    X₁ \ C X₁ ⊆ X₂ \ C X₂ := by
  intro x hx
  rcases Finset.mem_sdiff.mp hx with ⟨hxX₁, hxnotC₁⟩
  refine Finset.mem_sdiff.mpr ⟨hsubset hxX₁, ?_⟩
  intro hxC₂
  exact hxnotC₁ (hsub hsubset (Finset.mem_inter.mpr ⟨hxX₁, hxC₂⟩))

/-- Sequential composition of feasible choice rules is feasible. -/
theorem feasible_sequentialComposition_of_forall_mem
    {Cs : List (ChoiceRule α)}
    (hfeasible : ∀ C ∈ Cs, Feasible C) :
    Feasible (sequentialComposition Cs) := by
  induction Cs with
  | nil =>
      intro X x hx
      simp [sequentialComposition] at hx
  | cons C Cs ih =>
      intro X x hx
      simp [sequentialComposition] at hx
      rcases hx with hxC | hxTail
      · exact hfeasible C List.mem_cons_self X hxC
      · have htail : Feasible (sequentialComposition Cs) := by
          apply ih
          intro D hD
          exact hfeasible D (List.mem_cons_of_mem C hD)
        exact (Finset.mem_sdiff.mp (htail (X \ C X) hxTail)).1

/-- Arithmetic identity for capacity accounting in sequential composition. -/
theorem min_add_min_sub_min_eq_min_add (q s n : ℕ) :
    min q n + min s (n - min q n) = min (q + s) n := by
  by_cases hqn : q ≤ n
  · rw [Nat.min_eq_left hqn]
    by_cases hsn : s ≤ n - q
    · rw [Nat.min_eq_left hsn]
      rw [Nat.min_eq_left]
      omega
    · have hnqs : n - q ≤ s := by omega
      rw [Nat.min_eq_right hnqs]
      rw [Nat.min_eq_right (by omega)]
      omega
  · have hnq : n ≤ q := by omega
    rw [Nat.min_eq_right hnq]
    have hright : min (q + s) n = n := Nat.min_eq_right (by omega)
    rw [hright]
    simp

/-- Extract stage feasibility from a paired capacity/choice-rule ledger. -/
theorem feasible_of_mem_of_forall₂_feasible_qAcceptant
    {qs : List ℕ} {Cs : List (ChoiceRule α)}
    (hstages : List.Forall₂
      (fun q C => Feasible C ∧ QAcceptant q C) qs Cs)
    {C : ChoiceRule α} (hC : C ∈ Cs) :
    Feasible C := by
  induction hstages with
  | nil =>
      simp at hC
  | cons hhead _htail ih =>
      simp at hC
      rcases hC with rfl | hC
      · exact hhead.1
      · exact ih hC

/--
Sequential composition of feasible q-acceptant choice rules is q-acceptant,
with total capacity equal to the sum of the stage capacities.
-/
theorem qAcceptant_sequentialComposition_of_forall₂_feasible_qAcceptant
    {qs : List ℕ} {Cs : List (ChoiceRule α)}
    (hstages : List.Forall₂
      (fun q C => Feasible C ∧ QAcceptant q C) qs Cs) :
    QAcceptant qs.sum (sequentialComposition Cs) := by
  induction hstages with
  | nil =>
      intro X
      simp [sequentialComposition]
  | @cons q C qs Cs hhead htail ih =>
      rcases hhead with ⟨hfeasibleC, hacceptC⟩
      intro X
      let R : Finset α := X \ C X
      let T : ChoiceRule α := sequentialComposition Cs
      have htailFeasible : Feasible T := by
        exact feasible_sequentialComposition_of_forall_mem
          (Cs := Cs)
          (fun D hD =>
            feasible_of_mem_of_forall₂_feasible_qAcceptant
              (Cs := Cs) htail hD)
      have hdisjoint : C X ∩ T R = ∅ := by
        ext a
        constructor
        · intro ha
          rcases Finset.mem_inter.mp ha with ⟨haCX, haTR⟩
          have haR : a ∈ R := htailFeasible R haTR
          exact False.elim ((Finset.mem_sdiff.mp haR).2 haCX)
        · intro ha
          simp at ha
      have hcard_union :
          (C X ∪ T R).card = (C X).card + (T R).card := by
        have hcard := Finset.card_union_add_card_inter (C X) (T R)
        rw [hdisjoint] at hcard
        simp at hcard
        omega
      have hRcard : R.card = X.card - (C X).card := by
        exact Finset.card_sdiff_of_subset (hfeasibleC X)
      have hCXcard : (C X).card = min q X.card := hacceptC X
      have hTRcard : (T R).card = min qs.sum R.card := ih R
      calc
        (sequentialComposition (C :: Cs) X).card
            = (C X ∪ T R).card := by simp [sequentialComposition, R, T]
        _ = (C X).card + (T R).card := hcard_union
        _ = min q X.card + min qs.sum (X.card - min q X.card) := by
          rw [hTRcard, hRcard, hCXcard]
        _ = min (q + qs.sum) X.card :=
          min_add_min_sub_min_eq_min_add q qs.sum X.card
        _ = min (q :: qs).sum X.card := by
          simp

/-- Sequential composition of feasible substitutable choice rules is substitutable. -/
theorem substitutable_sequentialComposition_of_forall_mem
    {Cs : List (ChoiceRule α)}
    (hfeasible : ∀ C ∈ Cs, Feasible C)
    (hsub : ∀ C ∈ Cs, Substitutable C) :
    Substitutable (sequentialComposition Cs) := by
  induction Cs with
  | nil =>
      intro X₁ X₂ hsubset x hx
      simp [sequentialComposition] at hx
  | cons C Cs ih =>
      intro X₁ X₂ hsubset x hx
      rcases Finset.mem_inter.mp hx with ⟨hxX₁, hxChosen₂⟩
      simp [sequentialComposition] at hxChosen₂ ⊢
      rcases hxChosen₂ with hxC₂ | hxTail₂
      · exact Or.inl
          (hsub C List.mem_cons_self hsubset
            (Finset.mem_inter.mpr ⟨hxX₁, hxC₂⟩))
      · by_cases hxC₁ : x ∈ C X₁
        · exact Or.inl hxC₁
        · have htail : Substitutable (sequentialComposition Cs) := by
            apply ih
            · intro D hD
              exact hfeasible D (List.mem_cons_of_mem C hD)
            · intro D hD
              exact hsub D (List.mem_cons_of_mem C hD)
          have htailSubset :
              X₁ \ C X₁ ⊆ X₂ \ C X₂ :=
            sdiff_choice_subset_sdiff_choice_of_subset_of_substitutable
              (C := C) (hsub C List.mem_cons_self) hsubset
          have hxTail₁ : x ∈ sequentialComposition Cs (X₁ \ C X₁) :=
            htail htailSubset
              (Finset.mem_inter.mpr
                ⟨Finset.mem_sdiff.mpr ⟨hxX₁, hxC₁⟩, hxTail₂⟩)
          exact Or.inr hxTail₁

/--
If `S'` extends `S` by at most one element, then it is either unchanged or a
single insertion into `S`.
-/
theorem eq_or_exists_eq_insert_of_subset_of_sdiff_card_le_one
    {S S' : Finset α} (hsubset : S ⊆ S')
    (hcard : (S' \ S).card ≤ 1) :
    S' = S ∨ ∃ y, y ∉ S ∧ S' = insert y S := by
  by_cases hdiff_empty : S' \ S = ∅
  · left
    apply Finset.Subset.antisymm
    · intro z hzS'
      by_contra hzS
      have hzDiff : z ∈ S' \ S := Finset.mem_sdiff.mpr ⟨hzS', hzS⟩
      simp [hdiff_empty] at hzDiff
    · exact hsubset
  · right
    rcases Finset.nonempty_of_ne_empty hdiff_empty with ⟨y, hyDiff⟩
    rcases Finset.mem_sdiff.mp hyDiff with ⟨hyS', hyNotS⟩
    have hdiff_subset_singleton : S' \ S ⊆ ({y} : Finset α) := by
      intro z hzDiff
      by_contra hzSingleton
      have hz_ne_y : z ≠ y := by
        intro hzy
        exact hzSingleton (by simp [hzy])
      have hpair_subset : insert z ({y} : Finset α) ⊆ S' \ S := by
        intro w hw
        rw [Finset.mem_insert] at hw
        rcases hw with rfl | hw
        · exact hzDiff
        · have hwy : w = y := by simpa using hw
          simpa [hwy] using hyDiff
      have hpair_card : (insert z ({y} : Finset α)).card = 2 := by
        rw [Finset.card_insert_of_notMem]
        · simp
        · simpa using hz_ne_y
      have htwo_le : 2 ≤ (S' \ S).card := by
        rw [← hpair_card]
        exact Finset.card_le_card hpair_subset
      omega
    refine ⟨y, hyNotS, ?_⟩
    apply Finset.Subset.antisymm
    · intro z hzS'
      by_cases hzS : z ∈ S
      · exact Finset.mem_insert_of_mem hzS
      · have hzDiff : z ∈ S' \ S := Finset.mem_sdiff.mpr ⟨hzS', hzS⟩
        have hzY : z = y := by
          have hzMemSingleton := hdiff_subset_singleton hzDiff
          simpa using hzMemSingleton
        simp [hzY]
    · intro z hzInsert
      rw [Finset.mem_insert] at hzInsert
      rcases hzInsert with rfl | hzS
      · exact hyS'
      · exact hsubset hzS

/-- A one-insertion loss is contained in the borderline set at the smaller pool. -/
theorem choice_loss_subset_borderlineSet_of_eq_insert
    [Fintype α] {T : ChoiceRule α} {S S' : Finset α} {y : α}
    (hS' : S' = insert y S) :
    T S \ T S' ⊆ borderlineSet T S := by
  intro z hz
  rw [borderlineSet]
  exact Finset.mem_biUnion.mpr
    ⟨y, Finset.mem_univ y, by simpa [hS'] using hz⟩

/--
If `S'` extends `S` by at most one element, every tail-stage loss from `S` to
`S'` is already a one-step borderline loss at `S`.
-/
theorem choice_loss_subset_borderlineSet_of_subset_sdiff_card_le_one
    [Fintype α] {T : ChoiceRule α} {S S' : Finset α}
    (hsubset : S ⊆ S') (hcard : (S' \ S).card ≤ 1) :
    T S \ T S' ⊆ borderlineSet T S := by
  rcases eq_or_exists_eq_insert_of_subset_of_sdiff_card_le_one
      hsubset hcard with hEq | ⟨y, _hyNotS, hEq⟩
  · intro z hz
    simp [hEq] at hz
  · exact choice_loss_subset_borderlineSet_of_eq_insert (T := T) hEq

/--
A loss of the first-then-tail rule is contained in the union of the first-stage
loss and the tail-stage loss on the corresponding remainders.
-/
theorem firstThen_loss_subset_first_loss_union_tail_loss
    (C T : ChoiceRule α) (X X' : Finset α) :
    (C X ∪ T (X \ C X)) \ (C X' ∪ T (X' \ C X')) ⊆
      (C X \ C X') ∪ (T (X \ C X) \ T (X' \ C X')) := by
  intro y hy
  rcases Finset.mem_sdiff.mp hy with ⟨hyComp, hyNotComp'⟩
  have hyNotC' : y ∉ C X' := by
    intro hyC'
    exact hyNotComp' (Finset.mem_union_left _ hyC')
  have hyNotT' : y ∉ T (X' \ C X') := by
    intro hyT'
    exact hyNotComp' (Finset.mem_union_right _ hyT')
  rcases Finset.mem_union.mp hyComp with hyC | hyT
  · exact Finset.mem_union_left _
      (Finset.mem_sdiff.mpr ⟨hyC, hyNotC'⟩)
  · exact Finset.mem_union_right _
      (Finset.mem_sdiff.mpr ⟨hyT, hyNotT'⟩)

/--
If every one-applicant first-stage expansion changes the remainder by at most
one element, then the composed borderline set is contained in the union of the
first-stage borderline set and the tail borderline set at the original
remainder.
-/
theorem borderlineSet_firstThen_subset_union_of_remainder_sdiff_card_le_one
    [Fintype α] {C T : ChoiceRule α} {X : Finset α}
    (hrem_subset :
      ∀ x, X \ C X ⊆ insert x X \ C (insert x X))
    (hrem_card :
      ∀ x, ((insert x X \ C (insert x X)) \ (X \ C X)).card ≤ 1) :
    borderlineSet (fun Y => C Y ∪ T (Y \ C Y)) X ⊆
      borderlineSet C X ∪ borderlineSet T (X \ C X) := by
  intro y hy
  rw [borderlineSet] at hy ⊢
  rcases Finset.mem_biUnion.mp hy with ⟨x, _hxUniv, hyLoss⟩
  have hyLossUnion :
      y ∈ (C X \ C (insert x X)) ∪
        (T (X \ C X) \ T (insert x X \ C (insert x X))) :=
    firstThen_loss_subset_first_loss_union_tail_loss
      (C := C) (T := T) (X := X) (X' := insert x X) hyLoss
  rcases Finset.mem_union.mp hyLossUnion with hyFirst | hyTail
  · exact Finset.mem_union_left _
      (Finset.mem_biUnion.mpr ⟨x, Finset.mem_univ x, hyFirst⟩)
  · have hyTailBorder :
        y ∈ borderlineSet T (X \ C X) :=
      choice_loss_subset_borderlineSet_of_subset_sdiff_card_le_one
        (T := T) (hrem_subset x) (hrem_card x) hyTail
    exact Finset.mem_union_right _ hyTailBorder

/--
Conditional additive variability for an abstract first-then-tail composition.
-/
theorem variabilityAtMost_firstThen_of_remainder_sdiff_card_le_one
    [Fintype α] {mC mTail : ℕ} {C T : ChoiceRule α}
    (hvarC : VariabilityAtMost mC C)
    (hvarTail : VariabilityAtMost mTail T)
  (hrem_subset :
      ∀ X x, X \ C X ⊆ insert x X \ C (insert x X))
    (hrem_card :
      ∀ X x, ((insert x X \ C (insert x X)) \ (X \ C X)).card ≤ 1) :
    VariabilityAtMost (mC + mTail) (fun X => C X ∪ T (X \ C X)) := by
  intro X
  change (borderlineSet (fun Y => C Y ∪ T (Y \ C Y)) X).card ≤ mC + mTail
  have hborder_subset :
      borderlineSet (fun Y => C Y ∪ T (Y \ C Y)) X ⊆
        borderlineSet C X ∪ borderlineSet T (X \ C X) :=
    borderlineSet_firstThen_subset_union_of_remainder_sdiff_card_le_one
      (C := C) (T := T) (X := X) (hrem_subset X) (hrem_card X)
  have hcard_subset :=
    Finset.card_le_card hborder_subset
  have hcard_union :
      (borderlineSet C X ∪ borderlineSet T (X \ C X)).card ≤
        (borderlineSet C X).card + (borderlineSet T (X \ C X)).card :=
    Finset.card_union_le _ _
  have hC := hvarC X
  have hTail := hvarTail (X \ C X)
  omega

/-- Under substitutability, one-step instability bounds old first-stage losses by one. -/
theorem choiceLossTerm_insert_le_one_of_substitutable_of_dUnstable_one
    {C : ChoiceRule α} (hsub : Substitutable C)
    (hunstable : DUnstable 1 C) {X : Finset α} {x : α} (hx : x ∉ X) :
    choiceLossTerm C X (insert x X) ≤ 1 := by
  have hsubset : X ⊆ insert x X := by
    intro z hz
    exact Finset.mem_insert_of_mem hz
  have hgain :
      choiceGainTerm C X (insert x X) = 0 :=
    (substitutable_iff_choiceGainTerm_eq_zero C).mp hsub hsubset
  have hdist := hunstable X x hx
  rw [choiceDistance, hgain] at hdist
  simpa using hdist

/--
A borderline witness is an exact one-for-one exchange: if adding a fresh `x`
displaces `y`, then the fresh applicant is chosen and the new chosen set is
obtained by replacing `y` by `x`.
-/
theorem choice_insert_eq_insert_erase_choice_of_borderline_witness
    {q : ℕ} {C : ChoiceRule α}
    (hfeasible : Feasible C) (haccept : QAcceptant q C)
    (hsub : Substitutable C) (hunstable : DUnstable 1 C)
    {X : Finset α} {x y : α} (hx : x ∉ X)
    (hy : y ∈ C X \ C (insert x X)) :
    x ∈ C (insert x X) ∧ (C X).card = q ∧
      C (insert x X) = insert x ((C X).erase y) := by
  classical
  rcases Finset.mem_sdiff.mp hy with ⟨hyCX, hyNotCInsert⟩
  have hyX : y ∈ X := hfeasible X hyCX
  have hq_le_X : q ≤ X.card := by
    by_contra hnot
    have hsmall : X.card < q := Nat.lt_of_not_ge hnot
    have hCX : C X = X :=
      QAcceptant.eq_of_card_le hfeasible haccept (le_of_lt hsmall)
    have hInsert_card : (insert x X).card ≤ q := by
      rw [Finset.card_insert_of_notMem hx]
      omega
    have hCInsert : C (insert x X) = insert x X :=
      QAcceptant.eq_of_card_le hfeasible haccept hInsert_card
    exact hyNotCInsert (by
      rw [hCInsert]
      exact Finset.mem_insert_of_mem hyX)
  have hcardCX : (C X).card = q := by
    rw [haccept X, Nat.min_eq_left hq_le_X]
  have hcardInsert : (C (insert x X)).card = q := by
    have hX_subset : X ⊆ insert x X := by
      intro z hz
      exact Finset.mem_insert_of_mem hz
    have hq_le_insert : q ≤ (insert x X).card :=
      hq_le_X.trans (Finset.card_le_card hX_subset)
    rw [haccept (insert x X), Nat.min_eq_left hq_le_insert]
  have hcard_eq : (C (insert x X)).card = (C X).card := by
    rw [hcardInsert, hcardCX]
  have hnew_subset_singleton :
      C (insert x X) \ C X ⊆ ({x} : Finset α) := by
    intro z hz
    rcases Finset.mem_sdiff.mp hz with ⟨hzCInsert, hzNotCX⟩
    have hzOffer : z ∈ insert x X := hfeasible (insert x X) hzCInsert
    rw [Finset.mem_insert] at hzOffer
    rcases hzOffer with rfl | hzX
    · exact Finset.mem_singleton_self _
    · have hzInter : z ∈ X ∩ C (insert x X) :=
        Finset.mem_inter.mpr ⟨hzX, hzCInsert⟩
      exact False.elim (hzNotCX
        (hsub (by intro a ha; exact Finset.mem_insert_of_mem ha) hzInter))
  rcases exists_mem_sdiff_of_card_eq_of_mem_sdiff
      (A := C (insert x X)) (B := C X) hcard_eq
      (Finset.mem_sdiff.mpr ⟨hyCX, hyNotCInsert⟩) with
    ⟨z, hzNew⟩
  have hxChosen : x ∈ C (insert x X) := by
    have hz_singleton : z ∈ ({x} : Finset α) := hnew_subset_singleton hzNew
    have hzx : z = x := by simpa using hz_singleton
    simpa [hzx] using (Finset.mem_sdiff.mp hzNew).1
  have hloss_card_le_one :
      (C X \ C (insert x X)).card ≤ 1 := by
    exact choiceLossTerm_insert_le_one_of_substitutable_of_dUnstable_one
      hsub hunstable hx
  have herased_subset : (C X).erase y ⊆ C (insert x X) := by
    intro z hz
    have hz_ne_y : z ≠ y := (Finset.mem_erase.mp hz).1
    have hzCX : z ∈ C X := (Finset.mem_erase.mp hz).2
    exact mem_of_mem_of_ne_lost_of_sdiff_card_le_one
      (A := C X) (B := C (insert x X)) (lost := y) (z := z)
      (Finset.mem_sdiff.mpr ⟨hyCX, hyNotCInsert⟩) hzCX hz_ne_y
      hloss_card_le_one
  have hinsert_subset :
      insert x ((C X).erase y) ⊆ C (insert x X) := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hzErase
    · exact hxChosen
    · exact herased_subset hzErase
  have hxNotErase : x ∉ (C X).erase y := by
    intro hxErase
    exact hx (hfeasible X (Finset.mem_of_mem_erase hxErase))
  have hqpos : 0 < q := by
    rw [← hcardCX]
    exact Finset.card_pos.mpr ⟨y, hyCX⟩
  have hcard_insert : (insert x ((C X).erase y)).card = q := by
    rw [Finset.card_insert_of_notMem hxNotErase]
    rw [Finset.card_erase_of_mem hyCX, hcardCX]
    omega
  exact
    ⟨hxChosen, hcardCX,
      (Finset.eq_of_subset_of_card_le hinsert_subset (by
        rw [hcard_insert, hcardInsert])).symm⟩

/--
If the first stage chooses the fresh applicant, then the fresh applicant is not
passed to the tail, and the one-element remainder premise follows from
substitutability plus one-step instability.
-/
theorem remainder_insert_sdiff_card_le_one_of_substitutable_of_dUnstable_one_of_new_chosen
    {C : ChoiceRule α} (hsub : Substitutable C)
    (hunstable : DUnstable 1 C) {X : Finset α} {x : α}
    (hx : x ∉ X) (hxChosen : x ∈ C (insert x X)) :
    ((insert x X \ C (insert x X)) \ (X \ C X)).card ≤ 1 := by
  have hsubset :
      (insert x X \ C (insert x X)) \ (X \ C X) ⊆
        C X \ C (insert x X) := by
    intro z hz
    rcases Finset.mem_sdiff.mp hz with ⟨hzRem', hzNotRem⟩
    rcases Finset.mem_sdiff.mp hzRem' with ⟨hzInsert, hzNotC'⟩
    rw [Finset.mem_insert] at hzInsert
    rcases hzInsert with rfl | hzX
    · exact False.elim (hzNotC' hxChosen)
    · refine Finset.mem_sdiff.mpr ⟨?_, hzNotC'⟩
      by_contra hzNotC
      exact hzNotRem (Finset.mem_sdiff.mpr ⟨hzX, hzNotC⟩)
  have hcard_loss :
      ((insert x X \ C (insert x X)) \ (X \ C X)).card ≤
        choiceLossTerm C X (insert x X) := by
    simpa [choiceLossTerm] using Finset.card_le_card hsubset
  have hloss :
      choiceLossTerm C X (insert x X) ≤ 1 :=
    choiceLossTerm_insert_le_one_of_substitutable_of_dUnstable_one
      (C := C) hsub hunstable hx
  exact hcard_loss.trans hloss

/--
For a feasible q-acceptant substitutable first stage, adding one fresh
applicant expands the tail remainder by at most one element.
-/
theorem remainder_insert_sdiff_card_le_one_of_feasible_of_qAcceptant_of_substitutable
    {q : ℕ} {C : ChoiceRule α}
    (hfeasible : Feasible C) (haccept : QAcceptant q C)
    (hsub : Substitutable C) {X : Finset α} {x : α} (hx : x ∉ X) :
    ((insert x X \ C (insert x X)) \ (X \ C X)).card ≤ 1 := by
  by_cases hxChosen : x ∈ C (insert x X)
  · exact remainder_insert_sdiff_card_le_one_of_substitutable_of_dUnstable_one_of_new_chosen
      (C := C) hsub
      (dUnstable_one_of_feasible_of_qAcceptant_of_substitutable
        (C := C) hfeasible haccept hsub)
      hx hxChosen
  · have hcons : Consistent C :=
      consistent_of_qAcceptant_of_substitutable haccept hsub
    have hCX' : C (insert x X) = C X :=
      choice_insert_eq_self_of_consistent_of_fresh_not_chosen
        hfeasible hcons hxChosen
    have hsubset_singleton :
        (insert x X \ C (insert x X)) \ (X \ C X) ⊆ ({x} : Finset α) := by
      intro y hy
      rcases Finset.mem_sdiff.mp hy with ⟨hyRem', hyNotRem⟩
      rcases Finset.mem_sdiff.mp hyRem' with ⟨hyInsert, hyNotCX'⟩
      rcases Finset.mem_insert.mp hyInsert with rfl | hyX
      · exact Finset.mem_singleton_self _
      · have hyNotCX : y ∉ C X := by
          simpa [hCX'] using hyNotCX'
        exact False.elim (hyNotRem (Finset.mem_sdiff.mpr ⟨hyX, hyNotCX⟩))
    exact (Finset.card_le_card hsubset_singleton).trans (by simp)

/--
If a feasible q-representative first stage receives one fresh applicant, the
set passed to the tail expands by at most one element.
-/
theorem remainder_insert_sdiff_card_le_one_of_feasible_of_qRepresentative
    {q : ℕ} {C : ChoiceRule α}
    (hfeasible : Feasible C) (hrep : QRepresentative q C)
    {X : Finset α} {x : α} (hx : x ∉ X) :
    ((insert x X \ C (insert x X)) \ (X \ C X)).card ≤ 1 := by
  by_cases hxChosen : x ∈ C (insert x X)
  · exact remainder_insert_sdiff_card_le_one_of_substitutable_of_dUnstable_one_of_new_chosen
      (C := C)
      (substitutable_of_feasible_of_qRepresentative hfeasible hrep)
      (dUnstable_one_of_feasible_of_qRepresentative hfeasible hrep)
      hx hxChosen
  · have hsub : Substitutable C :=
      substitutable_of_feasible_of_qRepresentative hfeasible hrep
    have hcons : Consistent C :=
      consistent_of_qAcceptant_of_substitutable hrep.qAcceptant hsub
    have hchosen_subset_X : C (insert x X) ⊆ X := by
      intro y hy
      have hyInsert : y ∈ insert x X := hfeasible (insert x X) hy
      rcases Finset.mem_insert.mp hyInsert with rfl | hyX
      · exact False.elim (hxChosen hy)
      · exact hyX
    have hCX' : C (insert x X) = C X :=
      hcons hchosen_subset_X (by intro y hy; exact Finset.mem_insert_of_mem hy)
    have hsubset_singleton :
        (insert x X \ C (insert x X)) \ (X \ C X) ⊆ ({x} : Finset α) := by
      intro y hy
      rcases Finset.mem_sdiff.mp hy with ⟨hyRem', hyNotRem⟩
      rcases Finset.mem_sdiff.mp hyRem' with ⟨hyInsert, hyNotCX'⟩
      rcases Finset.mem_insert.mp hyInsert with rfl | hyX
      · exact Finset.mem_singleton_self _
      · have hyNotCX : y ∉ C X := by
          simpa [hCX'] using hyNotCX'
        exact False.elim (hyNotRem (Finset.mem_sdiff.mpr ⟨hyX, hyNotCX⟩))
    exact (Finset.card_le_card hsubset_singleton).trans (by simp)

/--
Adding a feasible q-acceptant substitutable first stage before a tail adds the
first-stage variability bound to the tail variability bound.
-/
theorem variabilityAtMost_firstThen_of_feasible_qAcceptant_substitutable
    [Fintype α] {q mC mTail : ℕ} {C T : ChoiceRule α}
    (hfeasible : Feasible C) (haccept : QAcceptant q C)
    (hsub : Substitutable C)
    (hvarC : VariabilityAtMost mC C)
    (hvarTail : VariabilityAtMost mTail T) :
    VariabilityAtMost (mC + mTail) (fun X => C X ∪ T (X \ C X)) := by
  refine variabilityAtMost_firstThen_of_remainder_sdiff_card_le_one
    (C := C) (T := T) hvarC hvarTail ?_ ?_
  · intro X x
    exact sdiff_choice_subset_sdiff_choice_of_subset_of_substitutable
      (C := C) hsub (by intro y hy; exact Finset.mem_insert_of_mem hy)
  · intro X x
    by_cases hx : x ∈ X
    · have hinsert : insert x X = X := Finset.insert_eq_of_mem hx
      simp [hinsert]
    · exact
        remainder_insert_sdiff_card_le_one_of_feasible_of_qAcceptant_of_substitutable
          (C := C) hfeasible haccept hsub hx

/--
Adding a feasible q-acceptant 1-unstable first stage before a tail adds the
first-stage variability bound to the tail variability bound.
-/
theorem variabilityAtMost_firstThen_of_feasible_qAcceptant_dUnstable_one
    [Fintype α] {q mC mTail : ℕ} {C T : ChoiceRule α}
    (hfeasible : Feasible C) (haccept : QAcceptant q C)
    (hunstable : DUnstable 1 C)
    (hvarC : VariabilityAtMost mC C)
    (hvarTail : VariabilityAtMost mTail T) :
    VariabilityAtMost (mC + mTail) (fun X => C X ∪ T (X \ C X)) := by
  exact variabilityAtMost_firstThen_of_feasible_qAcceptant_substitutable
    (C := C) (T := T) hfeasible haccept
    (substitutable_of_dUnstable_one_of_feasible_of_qAcceptant
      (C := C) hfeasible haccept hunstable)
    hvarC hvarTail

/--
Sequential composition of feasible q-acceptant 1-unstable stages has
variability at most the sum of the supplied stage variability bounds.
-/
theorem variabilityAtMost_sequentialComposition_of_forall₂_feasible_qAcceptant_dUnstable
    [Fintype α] {qms : List (ℕ × ℕ)} {Cs : List (ChoiceRule α)}
    (hstages : List.Forall₂
      (fun qm C =>
        Feasible C ∧ QAcceptant qm.1 C ∧ DUnstable 1 C ∧
          VariabilityAtMost qm.2 C)
      qms Cs) :
    VariabilityAtMost (qms.map Prod.snd).sum (sequentialComposition Cs) := by
  induction hstages with
  | nil =>
      intro X
      have hborder_empty : borderlineSet (sequentialComposition []) X = ∅ := by
        rw [borderlineSet]
        ext y
        simp [sequentialComposition]
      simp [hborder_empty]
  | @cons qm C qms Cs hhead _htail ih =>
      rcases qm with ⟨q, m⟩
      rcases hhead with ⟨hfeasible, haccept, hunstable, hvar⟩
      have hfirstThen :
          VariabilityAtMost (m + (qms.map Prod.snd).sum)
            (fun X => C X ∪ sequentialComposition Cs (X \ C X)) :=
        variabilityAtMost_firstThen_of_feasible_qAcceptant_dUnstable_one
          (C := C) (T := sequentialComposition Cs)
          hfeasible haccept hunstable hvar ih
      simpa [sequentialComposition] using hfirstThen

/--
Adding a fresh applicant to a feasible q-representative first stage makes the
tail remainder monotone and changes it by at most one element.
-/
theorem variabilityAtMost_firstThen_of_feasible_qRepresentative
    [Fintype α] {q mTail : ℕ} {C T : ChoiceRule α}
    (hfeasible : Feasible C) (hrep : QRepresentative q C)
    (hvarTail : VariabilityAtMost mTail T) :
    VariabilityAtMost (1 + mTail) (fun X => C X ∪ T (X \ C X)) := by
  have hsub : Substitutable C :=
    substitutable_of_feasible_of_qRepresentative hfeasible hrep
  refine variabilityAtMost_firstThen_of_remainder_sdiff_card_le_one
    (C := C) (T := T)
    (variabilityAtMost_one_of_feasible_of_qRepresentative hfeasible hrep)
    hvarTail ?_ ?_
  · intro X x
    exact sdiff_choice_subset_sdiff_choice_of_subset_of_substitutable
      (C := C) hsub (by intro y hy; exact Finset.mem_insert_of_mem hy)
  · intro X x
    by_cases hx : x ∈ X
    · have hinsert : insert x X = X := Finset.insert_eq_of_mem hx
      simp [hinsert]
    · exact remainder_insert_sdiff_card_le_one_of_feasible_of_qRepresentative
        (C := C) hfeasible hrep hx

/--
Sequential composition of feasible q-representative queues has variability at
most the number of queues.
-/
theorem variabilityAtMost_length_of_forall_mem_qRepresentative
    [Fintype α] {Cs : List (ChoiceRule α)}
    (hqueues : ∀ C ∈ Cs, ∃ q, Feasible C ∧ QRepresentative q C) :
    VariabilityAtMost Cs.length (sequentialComposition Cs) := by
  induction Cs with
  | nil =>
      intro X
      have hborder_empty : borderlineSet (sequentialComposition []) X = ∅ := by
        rw [borderlineSet]
        ext y
        simp [sequentialComposition]
      simp [hborder_empty]
  | cons C Cs ih =>
      rcases hqueues C List.mem_cons_self with ⟨q, hfeasible, hrep⟩
      have htail : VariabilityAtMost Cs.length (sequentialComposition Cs) := by
        apply ih
        intro D hD
        exact hqueues D (List.mem_cons_of_mem C hD)
      have hcons :
          VariabilityAtMost (1 + Cs.length)
            (fun X => C X ∪ sequentialComposition Cs (X \ C X)) :=
        variabilityAtMost_firstThen_of_feasible_qRepresentative
          (C := C) (T := sequentialComposition Cs) hfeasible hrep htail
      simpa [sequentialComposition, Nat.add_comm] using hcons

end FiniteChoice
end AppliedModelingLib
