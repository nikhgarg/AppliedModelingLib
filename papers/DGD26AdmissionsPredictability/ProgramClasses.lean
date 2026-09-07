import AppliedModelingLib.Foundations.Math.FiniteChoice

/-!
# Abstract Sequential-Queue Program Procedures

Finite, parameterized source-procedure templates for the one-, two-, three-,
and six-queue admissions classes. Queue `j` gives first priority to its own
priority applicant and second priority to its own reference applicant. All
remaining applicants are ordered by their identifier. At the reference pool,
inserting priority applicant `j` displaces reference applicant `j`; hence each
queue has the explicit displacement construction used for the exact
variability claims. These are mathematical queue procedures, not a model of
an empirical roster or simulator.
-/

namespace DGD26AdmissionsPredictability
namespace ProgramClasses

open AppliedModelingLib.FiniteChoice

/-- Priority key for queue `j` in the abstract `n`-queue procedure. -/
def queueRank (n : ℕ) (j : Fin n) (a : Fin (2 * n)) : ℕ :=
  if a.val = n + j.val then 0
  else if a.val = j.val then 1
  else 2 + a.val

/-- Executable top-one queue under the abstract priority key. -/
def queueChoice (n : ℕ) (j : Fin n) : ChoiceRule (Fin (2 * n)) :=
  fun X => X.filter fun a => ∀ b ∈ X, queueRank n j a ≤ queueRank n j b

/-- The ordered list of `n` single-capacity source-procedure queues. -/
def queues (n : ℕ) : List (ChoiceRule (Fin (2 * n))) :=
  List.ofFn fun j : Fin n => queueChoice n j

/-- Abstract `n`-queue sequential admissions procedure. -/
def choice (n : ℕ) : ChoiceRule (Fin (2 * n)) :=
  sequentialComposition (queues n)

/-- Reference pool, containing one currently selected applicant per queue. -/
def incumbentPool (n : ℕ) : Finset (Fin (2 * n)) :=
  Finset.univ.filter fun a => a.val < n

/-- The abstract priority key has no ties. -/
theorem queueRank_injective (n : ℕ) (j : Fin n) :
    Function.Injective (queueRank n j) := by
  intro a b hab
  unfold queueRank at hab
  split_ifs at hab with haT haI hbT hbI
  all_goals apply Fin.ext
  all_goals simp only [Fin.val_eq_val]
  all_goals omega

/-- Every abstract single-capacity queue chooses only offered applicants. -/
theorem queueChoice_feasible (n : ℕ) (j : Fin n) :
    Feasible (queueChoice n j) := by
  intro X a ha
  exact (Finset.mem_filter.mp ha).1

/-- Every nonempty pool has a unique applicant of minimum procedure rank. -/
theorem queueChoice_eq_singleton_of_nonempty
    (n : ℕ) (j : Fin n) {X : Finset (Fin (2 * n))}
    (hX : X.Nonempty) :
    ∃ a ∈ X, queueChoice n j X = {a} := by
  let ranks := X.image (queueRank n j)
  have hranks : ranks.Nonempty := hX.image _
  let rmin := ranks.min' hranks
  have hrmin : rmin ∈ ranks := ranks.min'_mem hranks
  rcases Finset.mem_image.mp hrmin with ⟨a, haX, harank⟩
  refine ⟨a, haX, ?_⟩
  apply Finset.Subset.antisymm
  · intro b hb
    have hbmin : queueRank n j b ≤ queueRank n j a :=
      (Finset.mem_filter.mp hb).2 a haX
    have hamin : queueRank n j a ≤ queueRank n j b := by
      rw [harank]
      exact ranks.min'_le _ (Finset.mem_image.mpr ⟨b, (Finset.mem_filter.mp hb).1, rfl⟩)
    have hab : a = b := queueRank_injective n j (Nat.le_antisymm hamin hbmin)
    simpa [hab]
  · intro b hb
    have hba : b = a := Finset.mem_singleton.mp hb
    subst b
    refine Finset.mem_filter.mpr ⟨haX, ?_⟩
    intro b hbX
    rw [harank]
    exact ranks.min'_le _ (Finset.mem_image.mpr ⟨b, hbX, rfl⟩)

/-- Every procedure queue fills its single seat whenever the pool is nonempty. -/
theorem queueChoice_qAcceptant (n : ℕ) (j : Fin n) :
    QAcceptant 1 (queueChoice n j) := by
  intro X
  by_cases hX : X.Nonempty
  · rcases queueChoice_eq_singleton_of_nonempty n j hX with ⟨a, _haX, hchoice⟩
    rw [hchoice, Finset.card_singleton,
      Nat.min_eq_left (Finset.one_le_card.mpr hX)]
  · have hXempty : X = ∅ := Finset.not_nonempty_iff_eq_empty.mp hX
    subst X
    simp [queueChoice]

/-- Every procedure queue is represented by its strict numeric priority order. -/
theorem queueChoice_qRepresentative (n : ℕ) (j : Fin n) :
    QRepresentative 1 (queueChoice n j) := by
  refine ⟨fun a b => queueRank n j a < queueRank n j b, ?_,
    queueChoice_feasible n j,
    queueChoice_qAcceptant n j, ?_⟩
  · constructor
    · intro a
      exact Nat.lt_irrefl _
    · constructor
      · intro a b c hab hbc
        exact Nat.lt_trans hab hbc
      · intro a b hab
        have hrank_ne : queueRank n j a ≠ queueRank n j b := by
          intro hrank
          exact hab (queueRank_injective n j hrank)
        omega
  · intro X a b ha hbX hbNot
    have hale : queueRank n j a ≤ queueRank n j b :=
      (Finset.mem_filter.mp ha).2 b hbX
    have hab : a ≠ b := by
      intro hab
      subst b
      exact hbNot ha
    have hrank_ne : queueRank n j a ≠ queueRank n j b := by
      intro hrank
      exact hab (queueRank_injective n j hrank)
    omega

/-- Every queue in the procedure list has the required single-order properties. -/
theorem queues_member_properties (n : ℕ) :
    ∀ C ∈ queues n, Feasible C ∧ QRepresentative 1 C := by
  intro C hC
  rw [queues, List.mem_ofFn] at hC
  rcases hC with ⟨j, rfl⟩
  exact ⟨queueChoice_feasible n j, queueChoice_qRepresentative n j⟩

/-- Capacity ledger for the procedure's single-seat queues. -/
theorem queues_ledger (n : ℕ) :
    List.Forall₂
      (fun q C => Feasible C ∧ QRepresentative q C)
      (List.replicate n 1) (queues n) := by
  have build : ∀ Cs : List (ChoiceRule (Fin (2 * n))),
      (∀ C ∈ Cs, Feasible C ∧ QRepresentative 1 C) →
        List.Forall₂
          (fun q C => Feasible C ∧ QRepresentative q C)
          (List.replicate Cs.length 1) Cs := by
    intro Cs hCs
    induction Cs with
    | nil =>
        simp
    | cons C Cs ih =>
        rw [List.length_cons, List.replicate_succ]
        exact List.Forall₂.cons
          (hCs C List.mem_cons_self)
          (ih (fun D hD => hCs D (List.mem_cons_of_mem C hD)))
  simpa [queues] using build (queues n) (queues_member_properties n)

/--
The abstract `n`-queue procedure is feasible, fills its `n` seats, is
1-unstable, and has variability at most `n`.
-/
theorem choice_upper_properties (n : ℕ) :
    Feasible (choice n) ∧ QAcceptant n (choice n) ∧
      DUnstable 1 (choice n) ∧ VariabilityAtMost n (choice n) := by
  have hledger := queues_ledger n
  have hfeasible : ∀ C ∈ queues n, Feasible C := by
    intro C hC
    exact (queues_member_properties n C hC).1
  have hacceptLedger : List.Forall₂
      (fun q C => Feasible C ∧ QAcceptant q C)
      (List.replicate n 1) (queues n) := by
    have transform : ∀ {qs : List ℕ} {Cs : List (ChoiceRule (Fin (2 * n)))},
        List.Forall₂
          (fun q C => Feasible C ∧ QRepresentative q C) qs Cs →
        List.Forall₂
          (fun q C => Feasible C ∧ QAcceptant q C) qs Cs := by
      intro qs Cs h
      induction h with
      | nil => exact List.Forall₂.nil
      | cons hhead _htail ih =>
          exact List.Forall₂.cons ⟨hhead.1, hhead.2.qAcceptant⟩ ih
    exact transform hledger
  have hsubstitutable : ∀ C ∈ queues n, Substitutable C := by
    intro C hC
    exact substitutable_of_feasible_of_qRepresentative
      (queues_member_properties n C hC).1
      (queues_member_properties n C hC).2
  have hfeasChoice : Feasible (choice n) := by
    exact feasible_sequentialComposition_of_forall_mem hfeasible
  have hacceptChoice : QAcceptant n (choice n) := by
    simpa [choice] using
      qAcceptant_sequentialComposition_of_forall₂_feasible_qAcceptant
        hacceptLedger
  have hsubChoice : Substitutable (choice n) := by
    exact substitutable_sequentialComposition_of_forall_mem
      hfeasible hsubstitutable
  have hunstableChoice : DUnstable 1 (choice n) :=
    dUnstable_one_of_feasible_of_qAcceptant_of_substitutable
      hfeasChoice hacceptChoice hsubChoice
  have hvariability : VariabilityAtMost n (choice n) := by
    have hqueues : ∀ C ∈ queues n,
        ∃ q, Feasible C ∧ QRepresentative q C := by
      intro C hC
      exact ⟨1, queues_member_properties n C hC⟩
    simpa [choice, queues] using
      variabilityAtMost_length_of_forall_mem_qRepresentative hqueues
  exact ⟨hfeasChoice, hacceptChoice, hunstableChoice, hvariability⟩

/-- The one-queue procedure realizes one distinct borderline applicant. -/
theorem one_queue_witness :
    (borderlineSet (choice 1) (incumbentPool 1)).card = 1 := by
  decide

/-- The two-queue procedure realizes two distinct borderline applicants. -/
theorem two_queue_witness :
    (borderlineSet (choice 2) (incumbentPool 2)).card = 2 := by
  decide

/-- The three-queue procedure realizes three distinct borderline applicants. -/
theorem three_queue_witness :
    (borderlineSet (choice 3) (incumbentPool 3)).card = 3 := by
  decide

/-- The six-queue procedure realizes six distinct borderline applicants. -/
theorem six_queue_witness :
    (borderlineSet (choice 6) (incumbentPool 6)).card = 6 := by
  decide

/-- The abstract one-queue procedure has exact variability one. -/
theorem one_queue_properties :
    Feasible (choice 1) ∧ QAcceptant 1 (choice 1) ∧
      DUnstable 1 (choice 1) ∧ VariabilityExactly 1 (choice 1) := by
  have h := choice_upper_properties 1
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, incumbentPool 1, one_queue_witness⟩

/-- The abstract two-queue procedure has exact variability two. -/
theorem two_queue_properties :
    Feasible (choice 2) ∧ QAcceptant 2 (choice 2) ∧
      DUnstable 1 (choice 2) ∧ VariabilityExactly 2 (choice 2) := by
  have h := choice_upper_properties 2
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, incumbentPool 2, two_queue_witness⟩

/-- The abstract three-queue procedure has exact variability three. -/
theorem three_queue_properties :
    Feasible (choice 3) ∧ QAcceptant 3 (choice 3) ∧
      DUnstable 1 (choice 3) ∧ VariabilityExactly 3 (choice 3) := by
  have h := choice_upper_properties 3
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, incumbentPool 3, three_queue_witness⟩

/-- The abstract six-queue procedure has exact variability six. -/
theorem six_queue_properties :
    Feasible (choice 6) ∧ QAcceptant 6 (choice 6) ∧
      DUnstable 1 (choice 6) ∧ VariabilityExactly 6 (choice 6) := by
  have h := choice_upper_properties 6
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, incumbentPool 6, six_queue_witness⟩

end ProgramClasses
end DGD26AdmissionsPredictability
