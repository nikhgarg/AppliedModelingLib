import AppliedModelingLib.Foundations.Math.FiniteChoice
import Mathlib.Order.Extension.Linear

/-!
# Work file for the converse q-representativeness direction

This file is intentionally paper-local.  It keeps the revealed relation in a
nested namespace so it can coexist with older scratch files that experimented
with the same names.
-/

namespace AppliedModelingLib
namespace FiniteChoice
namespace QRepresentativeConverseWork

variable {α : Type*} [DecidableEq α]

/--
`x` is revealed above `y` when some offered pool chooses `x` while offering and
rejecting `y`.
-/
def RevealedAbove (C : ChoiceRule α) (x y : α) : Prop :=
  ∃ X, x ∈ C X ∧ y ∈ X ∧ y ∉ C X

theorem RevealedAbove.irrefl {C : ChoiceRule α} (x : α) :
    ¬ RevealedAbove C x x := by
  rintro ⟨_X, hxCX, _hxX, hxNotCX⟩
  exact hxNotCX hxCX

theorem RevealedAbove.ne {C : ChoiceRule α} {x y : α}
    (hxy : RevealedAbove C x y) :
    x ≠ y := by
  intro h
  subst y
  exact RevealedAbove.irrefl (C := C) x hxy

/--
Under substitutability and q-acceptance, every revealed comparison has a
canonical witness: the chosen q-set plus the rejected alternative.
-/
theorem RevealedAbove.exists_canonical_choice_of_substitutable
    {q : ℕ} {C : ChoiceRule α}
    (hfeasible : Feasible C) (haccept : QAcceptant q C)
    (hsub : Substitutable C) {x y : α}
    (hxy : RevealedAbove C x y) :
    ∃ P : Finset α, x ∈ P ∧ y ∉ P ∧ P.card = q ∧
      C (insert y P) = P := by
  rcases hxy with ⟨X, hxCX, hyX, hyNotCX⟩
  refine ⟨C X, hxCX, hyNotCX, ?_, ?_⟩
  · have hnot_card_le : ¬ X.card ≤ q := by
      intro hcard
      have hCX : C X = X :=
        QAcceptant.eq_of_card_le hfeasible haccept hcard
      exact hyNotCX (by simpa [hCX] using hyX)
    have hq_lt : q < X.card := Nat.lt_of_not_ge hnot_card_le
    rw [haccept X, Nat.min_eq_left (le_of_lt hq_lt)]
  · have hconsistent : Consistent C :=
      consistent_of_qAcceptant_of_substitutable haccept hsub
    have hchosen_subset : C X ⊆ insert y (C X) := by
      intro z hz
      exact Finset.mem_insert_of_mem hz
    have hinsert_subset : insert y (C X) ⊆ X := by
      intro z hz
      rw [Finset.mem_insert] at hz
      rcases hz with rfl | hzCX
      · exact hyX
      · exact hfeasible X hzCX
    exact (hconsistent hchosen_subset hinsert_subset).symm

theorem RevealedAbove.of_canonical_choice
    {C : ChoiceRule α} {P : Finset α} {x y : α}
    (hxP : x ∈ P) (hyP : y ∉ P) (hchoice : C (insert y P) = P) :
    RevealedAbove C x y := by
  refine ⟨insert y P, ?_, ?_, ?_⟩
  · simpa [hchoice] using hxP
  · exact Finset.mem_insert_self y P
  · simpa [hchoice] using hyP

/--
A canonical revealed witness turns into a one-step displacement after removing
any chosen element from its canonical chosen set.
-/
theorem mem_borderlineSet_of_canonical_choice_erase
    [Fintype α] {q : ℕ} {C : ChoiceRule α}
    (hfeasible : Feasible C) (haccept : QAcceptant q C)
    {P : Finset α} {a y : α}
    (haP : a ∈ P) (hyP : y ∉ P) (hcard : P.card = q)
    (hchoice : C (insert y P) = P) :
    y ∈ borderlineSet C (insert y (P.erase a)) := by
  classical
  let S : Finset α := insert y (P.erase a)
  have hyErase : y ∉ P.erase a := by
    intro hy
    exact hyP (Finset.mem_of_mem_erase hy)
  have hcardS : S.card = q := by
    change (insert y (P.erase a)).card = q
    rw [Finset.card_insert_of_notMem hyErase]
    rw [Finset.card_erase_add_one haP]
    exact hcard
  have hCS : C S = S :=
    QAcceptant.eq_of_card_le hfeasible haccept (by omega)
  have hinsertS : insert a S = insert y P := by
    ext z
    by_cases hza : z = a
    · subst z
      simp [S, haP]
    · simp [S, Finset.mem_erase, hza]
  rw [borderlineSet]
  exact Finset.mem_biUnion.mpr
    ⟨a, Finset.mem_univ a, by
      exact Finset.mem_sdiff.mpr
        ⟨by simp [hCS, S],
          by
            rw [hinsertS, hchoice]
            exact hyP⟩⟩

/-- Variability at most one makes each borderline set a subsingleton. -/
theorem eq_of_mem_borderlineSet_of_variabilityAtMost_one
    [Fintype α] {C : ChoiceRule α}
    (hvar : VariabilityAtMost 1 C) {X : Finset α} {y z : α}
    (hy : y ∈ borderlineSet C X) (hz : z ∈ borderlineSet C X) :
    y = z := by
  by_contra hne
  have hpair_subset :
      insert y ({z} : Finset α) ⊆ borderlineSet C X := by
    intro w hw
    rw [Finset.mem_insert] at hw
    rcases hw with rfl | hw
    · exact hy
    · have hwz : w = z := by simpa using hw
      simpa [hwz] using hz
  have hpair_card : (insert y ({z} : Finset α)).card = 2 := by
    rw [Finset.card_insert_of_notMem]
    · simp
    · simpa using hne
  have htwo_le : 2 ≤ (borderlineSet C X).card := by
    rw [← hpair_card]
    exact Finset.card_le_card hpair_subset
  have hone := hvar X
  omega

/--
Equivalently, two losses from the same base pool must be the same applicant.
-/
theorem not_two_distinct_losses_same_base_of_variabilityAtMost_one
    [Fintype α] {C : ChoiceRule α}
    (hvar : VariabilityAtMost 1 C) {X : Finset α}
    {a b y z : α}
    (hy : y ∈ C X \ C (insert a X))
    (hz : z ∈ C X \ C (insert b X)) :
    y = z := by
  classical
  have hyB : y ∈ borderlineSet C X := by
    rw [borderlineSet]
    exact Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ a, hy⟩
  have hzB : z ∈ borderlineSet C X := by
    rw [borderlineSet]
    exact Finset.mem_biUnion.mpr ⟨b, Finset.mem_univ b, hz⟩
  exact eq_of_mem_borderlineSet_of_variabilityAtMost_one hvar hyB hzB

/--
Finite path lemma: if an element is chosen at `X` and not chosen after adding a
finite set `T`, then along some one-element insertion from an intermediate
`X ∪ S` it is lost.
-/
theorem exists_one_step_loss_of_mem_choice_union_of_not_mem_choice_union
    {C : ChoiceRule α} {X T : Finset α} {x : α}
    (hxStart : x ∈ C X) (hxEnd : x ∉ C (X ∪ T)) :
    ∃ S b, S ⊆ T ∧ b ∈ T ∧ b ∉ S ∧
      x ∈ C (X ∪ S) ∧ x ∉ C (insert b (X ∪ S)) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
      simp at hxEnd
      exact False.elim (hxEnd hxStart)
  | @insert b T hbT ih =>
      by_cases hxTail : x ∈ C (X ∪ T)
      · refine ⟨T, b, ?_, ?_, ?_, hxTail, ?_⟩
        · intro z hz
          exact Finset.mem_insert_of_mem hz
        · exact Finset.mem_insert_self b T
        · exact hbT
        · have hset : X ∪ insert b T = insert b (X ∪ T) := by
            ext z
            simp
          simpa [hset] using hxEnd
      · rcases ih hxTail with
          ⟨S, a, hST, haT, haS, hxS, hxLoss⟩
        refine ⟨S, a, ?_, ?_, haS, hxS, hxLoss⟩
        · intro z hz
          exact Finset.mem_insert_of_mem (hST hz)
        · exact Finset.mem_insert_of_mem haT

/--
Version of the finite path lemma for nested endpoints.
-/
theorem exists_one_step_loss_of_mem_choice_of_not_mem_choice_of_subset
    {C : ChoiceRule α} {X U : Finset α} {x : α}
    (hXU : X ⊆ U) (hxStart : x ∈ C X) (hxEnd : x ∉ C U) :
    ∃ W b, X ⊆ W ∧ W ⊆ U ∧ b ∈ U ∧ b ∉ W ∧
      x ∈ C W ∧ x ∉ C (insert b W) := by
  classical
  have hU : X ∪ (U \ X) = U := by
    ext z
    constructor
    · intro hz
      rcases Finset.mem_union.mp hz with hzX | hzUX
      · exact hXU hzX
      · exact (Finset.mem_sdiff.mp hzUX).1
    · intro hzU
      by_cases hzX : z ∈ X
      · exact Finset.mem_union_left _ hzX
      · exact Finset.mem_union_right _
          (Finset.mem_sdiff.mpr ⟨hzU, hzX⟩)
  have hxEndUnion : x ∉ C (X ∪ (U \ X)) := by
    simpa [hU] using hxEnd
  rcases exists_one_step_loss_of_mem_choice_union_of_not_mem_choice_union
      (C := C) (X := X) (T := U \ X) hxStart hxEndUnion with
    ⟨S, b, hS, hbUX, hbS, hxS, hxLoss⟩
  refine ⟨X ∪ S, b, ?_, ?_, ?_, ?_, hxS, hxLoss⟩
  · intro z hz
    exact Finset.mem_union_left S hz
  · intro z hz
    rcases Finset.mem_union.mp hz with hzX | hzS
    · exact hXU hzX
    · exact (Finset.mem_sdiff.mp (hS hzS)).1
  · exact (Finset.mem_sdiff.mp hbUX).1
  · intro hbW
    rcases Finset.mem_union.mp hbW with hbX | hbS'
    · exact (Finset.mem_sdiff.mp hbUX).2 hbX
    · exact hbS hbS'

/--
Under substitutability, rejection persists upward: if an offered applicant is
rejected from a smaller pool, then it remains rejected in any larger pool.
-/
theorem not_mem_choice_of_substitutable_of_subset_of_mem_of_not_mem
    {C : ChoiceRule α} (hsub : Substitutable C)
    {X Y : Finset α} {x : α}
    (hXY : X ⊆ Y) (hxX : x ∈ X) (hxNotX : x ∉ C X) :
    x ∉ C Y := by
  intro hxCY
  exact hxNotX
    (hsub hXY (Finset.mem_inter.mpr ⟨hxX, hxCY⟩))

theorem exists_mem_sdiff_ne_of_one_lt_card
    {A B : Finset α} {a : α}
    (hcard : 1 < (A \ B).card) :
    ∃ c, c ∈ A \ B ∧ c ≠ a := by
  classical
  by_contra hnone
  have hsubset : A \ B ⊆ ({a} : Finset α) := by
    intro c hc
    by_cases hca : c = a
    · simp [hca]
    · exact False.elim (hnone ⟨c, hc, hca⟩)
  have hle : (A \ B).card ≤ 1 := by
    have hcard_sub := Finset.card_le_card hsubset
    simpa using hcard_sub
  omega

/--
The finite exchange condition still missing from the unconditional asymmetry
proof: two opposite canonical witnesses can be exchanged to the same base.
-/
def HasCommonCanonicalExchangeBase
    (P Q : Finset α) (x y : α) : Prop :=
  ∃ a, a ∈ P ∧ ∃ b, b ∈ Q ∧
    insert y (P.erase a) = insert x (Q.erase b)

/--
Two canonical witnesses for opposite revealed comparisons `x ≻ y` and
`y ≻ x`.
-/
def OppositeCanonicalChoices
    (C : ChoiceRule α) (q : ℕ) (x y : α)
    (P Q : Finset α) : Prop :=
  x ∈ P ∧ y ∉ P ∧ P.card = q ∧ C (insert y P) = P ∧
    y ∈ Q ∧ x ∉ Q ∧ Q.card = q ∧ C (insert x Q) = Q

/-- Difference size between opposite canonical witnesses after removing `x` and `y`. -/
def oppositeCanonicalDiffCard
    (P Q : Finset α) (x y : α) : ℕ :=
  ((P.erase x) \ (Q.erase y)).card

theorem oppositeCanonicalDiffCard_lt_of_subset_erase
    {P P' Q : Finset α} {x y a : α}
    (ha : a ∈ (P.erase x) \ (Q.erase y))
    (hsubset :
      (P'.erase x) \ (Q.erase y) ⊆
        ((P.erase x) \ (Q.erase y)).erase a) :
    oppositeCanonicalDiffCard P' Q x y <
      oppositeCanonicalDiffCard P Q x y := by
  have hle := Finset.card_le_card hsubset
  have herase : (((P.erase x) \ (Q.erase y)).erase a).card + 1 =
      ((P.erase x) \ (Q.erase y)).card :=
    Finset.card_erase_add_one ha
  simp [oppositeCanonicalDiffCard]
  omega

theorem insert_erase_insert_eq_insert_of_mem
    {P : Finset α} {a y : α} (haP : a ∈ P) :
    insert a (insert y (P.erase a)) = insert y P := by
  ext z
  constructor
  · intro hz
    rw [Finset.mem_insert] at hz
    rw [Finset.mem_insert]
    rcases hz with rfl | hz
    · exact Or.inr haP
    · rcases Finset.mem_insert.mp hz with rfl | hzErase
      · exact Or.inl rfl
      · exact Or.inr (Finset.mem_of_mem_erase hzErase)
  · intro hz
    rw [Finset.mem_insert] at hz
    rw [Finset.mem_insert]
    rcases hz with rfl | hzP
    · exact Or.inr (Finset.mem_insert_self _ (P.erase a))
    · by_cases hza : z = a
      · exact Or.inl hza
      · exact Or.inr
          (Finset.mem_insert_of_mem
            (Finset.mem_erase.mpr ⟨hza, hzP⟩))

theorem exists_minimal_oppositeCanonicalChoices
    {C : ChoiceRule α} {q : ℕ} {x y : α}
    (hexists : ∃ P Q, OppositeCanonicalChoices C q x y P Q) :
    ∃ P Q, OppositeCanonicalChoices C q x y P Q ∧
      ∀ P' Q', OppositeCanonicalChoices C q x y P' Q' →
        oppositeCanonicalDiffCard P Q x y ≤
          oppositeCanonicalDiffCard P' Q' x y := by
  classical
  let good : ℕ → Prop := fun n =>
    ∃ P Q, OppositeCanonicalChoices C q x y P Q ∧
      oppositeCanonicalDiffCard P Q x y = n
  have hgood_exists : ∃ n, good n := by
    rcases hexists with ⟨P, Q, hcanon⟩
    exact ⟨oppositeCanonicalDiffCard P Q x y, P, Q, hcanon, rfl⟩
  let n : ℕ := Nat.find hgood_exists
  rcases Nat.find_spec hgood_exists with ⟨P, Q, hcanon, hdiff⟩
  refine ⟨P, Q, hcanon, ?_⟩
  intro P' Q' hcanon'
  have hgood' :
      good (oppositeCanonicalDiffCard P' Q' x y) :=
    ⟨P', Q', hcanon', rfl⟩
  have hmin := Nat.find_min' hgood_exists hgood'
  rw [hdiff]
  exact hmin

theorem HasCommonCanonicalExchangeBase.of_core_erase_eq
    {P Q : Finset α} {x y a b : α}
    (hxP : x ∈ P) (hyQ : y ∈ Q)
    (haA : a ∈ P.erase x) (hbB : b ∈ Q.erase y)
    (hcore : (P.erase x).erase a = (Q.erase y).erase b) :
    HasCommonCanonicalExchangeBase P Q x y := by
  classical
  rcases Finset.mem_erase.mp haA with ⟨hax, haP⟩
  rcases Finset.mem_erase.mp hbB with ⟨hby, hbQ⟩
  refine ⟨a, haP, b, hbQ, ?_⟩
  ext z
  constructor
  · intro hz
    rw [Finset.mem_insert] at hz
    rw [Finset.mem_insert]
    rcases hz with rfl | hzPa
    · right
      exact Finset.mem_erase.mpr ⟨hby.symm, hyQ⟩
    · by_cases hzx : z = x
      · exact Or.inl hzx
      · right
        have hzAerase : z ∈ (P.erase x).erase a := by
          rcases Finset.mem_erase.mp hzPa with ⟨hza, hzP⟩
          exact Finset.mem_erase.mpr
            ⟨hza, Finset.mem_erase.mpr ⟨hzx, hzP⟩⟩
        have hzBerase : z ∈ (Q.erase y).erase b := by
          simpa [hcore] using hzAerase
        rcases Finset.mem_erase.mp hzBerase with ⟨hzb, hzB⟩
        exact Finset.mem_erase.mpr
          ⟨hzb, Finset.mem_of_mem_erase hzB⟩
  · intro hz
    rw [Finset.mem_insert] at hz
    rw [Finset.mem_insert]
    rcases hz with rfl | hzQb
    · right
      exact Finset.mem_erase.mpr ⟨hax.symm, hxP⟩
    · by_cases hzy : z = y
      · exact Or.inl hzy
      · right
        have hzBerase : z ∈ (Q.erase y).erase b := by
          rcases Finset.mem_erase.mp hzQb with ⟨hzb, hzQ⟩
          exact Finset.mem_erase.mpr
            ⟨hzb, Finset.mem_erase.mpr ⟨hzy, hzQ⟩⟩
        have hzAerase : z ∈ (P.erase x).erase a := by
          simpa [hcore] using hzBerase
        rcases Finset.mem_erase.mp hzAerase with ⟨hza, hzA⟩
        exact Finset.mem_erase.mpr
          ⟨hza, Finset.mem_of_mem_erase hzA⟩

/--
If the two canonical q-sets differ by at most one element after removing the
compared applicants, then they admit a common one-exchange base.
-/
theorem HasCommonCanonicalExchangeBase.of_erase_sdiff_card_le_one
    {q : ℕ} {P Q : Finset α} {x y : α}
    (hxP : x ∈ P) (hyQ : y ∈ Q)
    (hcardP : P.card = q) (hcardQ : Q.card = q)
    (hq : 1 < q)
    (hnear : ((P.erase x) \ (Q.erase y)).card ≤ 1) :
    HasCommonCanonicalExchangeBase P Q x y := by
  classical
  let A : Finset α := P.erase x
  let B : Finset α := Q.erase y
  have hcardAB : A.card = B.card := by
    have hAadd : A.card + 1 = P.card := by
      simpa [A] using Finset.card_erase_add_one hxP
    have hBadd : B.card + 1 = Q.card := by
      simpa [B] using Finset.card_erase_add_one hyQ
    omega
  have hnearAB : (A \ B).card ≤ 1 := by
    simpa [A, B] using hnear
  by_cases hnonempty : (A \ B).Nonempty
  · rcases hnonempty with ⟨a, haAB⟩
    rcases exists_mem_sdiff_of_card_eq_of_mem_sdiff
        (A := B) (B := A) hcardAB.symm haAB with
      ⟨b, hbBA⟩
    have hnearBA : (B \ A).card ≤ 1 := by
      rw [← Finset.card_sdiff_comm hcardAB]
      exact hnearAB
    have hcore : A.erase a = B.erase b := by
      ext z
      constructor
      · intro hz
        rcases Finset.mem_erase.mp hz with ⟨hza, hzA⟩
        have hzB : z ∈ B :=
          mem_of_mem_of_ne_lost_of_sdiff_card_le_one
            (A := A) (B := B) (lost := a) (z := z)
            haAB hzA hza hnearAB
        have hzb : z ≠ b := by
          intro hzb'
          subst z
          exact (Finset.mem_sdiff.mp hbBA).2 hzA
        exact Finset.mem_erase.mpr ⟨hzb, hzB⟩
      · intro hz
        rcases Finset.mem_erase.mp hz with ⟨hzb, hzB⟩
        have hzA : z ∈ A :=
          mem_of_mem_of_ne_lost_of_sdiff_card_le_one
            (A := B) (B := A) (lost := b) (z := z)
            hbBA hzB hzb hnearBA
        have hza : z ≠ a := by
          intro hza'
          subst z
          exact (Finset.mem_sdiff.mp haAB).2 hzB
        exact Finset.mem_erase.mpr ⟨hza, hzA⟩
    exact
      HasCommonCanonicalExchangeBase.of_core_erase_eq
        (P := P) (Q := Q) (x := x) (y := y)
        (a := a) (b := b) hxP hyQ
        (by simpa [A] using (Finset.mem_sdiff.mp haAB).1)
        (by simpa [B] using (Finset.mem_sdiff.mp hbBA).1)
        (by simpa [A, B] using hcore)
  · have hsubsetAB : A ⊆ B := by
      intro z hzA
      by_contra hzB
      exact hnonempty ⟨z, Finset.mem_sdiff.mpr ⟨hzA, hzB⟩⟩
    have hAB : A = B :=
      Finset.eq_of_subset_of_card_le hsubsetAB (by omega)
    have hApos : 0 < A.card := by
      have hAadd : A.card + 1 = P.card := by
        simpa [A] using Finset.card_erase_add_one hxP
      rw [hcardP] at hAadd
      omega
    rcases Finset.card_pos.mp hApos with ⟨c, hcA⟩
    have hcB : c ∈ B := by
      simpa [hAB] using hcA
    have hcore : A.erase c = B.erase c := by
      rw [hAB]
    exact
      HasCommonCanonicalExchangeBase.of_core_erase_eq
        (P := P) (Q := Q) (x := x) (y := y)
        (a := c) (b := c) hxP hyQ
        (by simpa [A] using hcA)
        (by simpa [B] using hcB)
        (by simpa [A, B] using hcore)

/--
Opposite canonical revealed witnesses are impossible once their one-step
displacements share a common exchanged base.
-/
theorem false_of_opposite_canonical_choices_of_common_exchange
    [Fintype α] {q : ℕ} {C : ChoiceRule α}
    (hfeasible : Feasible C) (haccept : QAcceptant q C)
    (hvar : VariabilityAtMost 1 C)
    {x y : α} {P Q : Finset α}
    (hxP : x ∈ P) (hyP : y ∉ P) (hcardP : P.card = q)
    (hchoiceP : C (insert y P) = P)
    (hyQ : y ∈ Q) (hxQ : x ∉ Q) (hcardQ : Q.card = q)
    (hchoiceQ : C (insert x Q) = Q)
    (hcommon : HasCommonCanonicalExchangeBase P Q x y) :
    False := by
  classical
  rcases hcommon with ⟨a, haP, b, hbQ, hbase⟩
  have hyBorder :
      y ∈ borderlineSet C (insert y (P.erase a)) :=
    mem_borderlineSet_of_canonical_choice_erase
      (C := C) hfeasible haccept haP hyP hcardP hchoiceP
  have hxBorderQ :
      x ∈ borderlineSet C (insert x (Q.erase b)) :=
    mem_borderlineSet_of_canonical_choice_erase
      (C := C) hfeasible haccept hbQ hxQ hcardQ hchoiceQ
  have hxBorder :
      x ∈ borderlineSet C (insert y (P.erase a)) := by
    simpa [hbase] using hxBorderQ
  have hy_eq_x : y = x :=
    eq_of_mem_borderlineSet_of_variabilityAtMost_one
      (C := C) hvar hyBorder hxBorder
  have hne : x ≠ y := by
    intro hxy
    subst y
    exact hyP hxP
  exact hne hy_eq_x.symm

/--
The target asymmetry theorem reduces to the finite common-exchange step above.
-/
theorem revealedAbove_asymm_of_variabilityAtMost_one_of_common_exchange
    [Fintype α] {q : ℕ} {C : ChoiceRule α}
    (hfeasible : Feasible C) (haccept : QAcceptant q C)
    (hunstable : DUnstable 1 C) (hvar : VariabilityAtMost 1 C)
    (hexchange :
      ∀ {x y : α} {P Q : Finset α},
        x ∈ P → y ∉ P → P.card = q → C (insert y P) = P →
        y ∈ Q → x ∉ Q → Q.card = q → C (insert x Q) = Q →
        HasCommonCanonicalExchangeBase P Q x y)
    {x y : α} (hxy : RevealedAbove C x y) :
    ¬ RevealedAbove C y x := by
  intro hyx
  have hsub : Substitutable C :=
    substitutable_of_dUnstable_one_of_feasible_of_qAcceptant
      (C := C) hfeasible haccept hunstable
  rcases RevealedAbove.exists_canonical_choice_of_substitutable
      (C := C) hfeasible haccept hsub hxy with
    ⟨P, hxP, hyP, hcardP, hchoiceP⟩
  rcases RevealedAbove.exists_canonical_choice_of_substitutable
      (C := C) hfeasible haccept hsub hyx with
    ⟨Q, hyQ, hxQ, hcardQ, hchoiceQ⟩
  exact false_of_opposite_canonical_choices_of_common_exchange
    (C := C) hfeasible haccept hvar
    hxP hyP hcardP hchoiceP
    hyQ hxQ hcardQ hchoiceQ
    (hexchange hxP hyP hcardP hchoiceP hyQ hxQ hcardQ hchoiceQ)

/--
For capacities above one, the common-exchange premise follows from the sharper
condition that opposite canonical witnesses differ by at most one element after
removing the two compared applicants.
-/
theorem revealedAbove_asymm_of_variabilityAtMost_one_of_near_canonical_choices
    [Fintype α] {q : ℕ} {C : ChoiceRule α}
    (hfeasible : Feasible C) (haccept : QAcceptant q C)
    (hunstable : DUnstable 1 C) (hvar : VariabilityAtMost 1 C)
    (hq : 1 < q)
    (hnear :
      ∀ {x y : α} {P Q : Finset α},
        x ∈ P → y ∉ P → P.card = q → C (insert y P) = P →
        y ∈ Q → x ∉ Q → Q.card = q → C (insert x Q) = Q →
        ((P.erase x) \ (Q.erase y)).card ≤ 1)
    {x y : α} (hxy : RevealedAbove C x y) :
    ¬ RevealedAbove C y x := by
  exact
    revealedAbove_asymm_of_variabilityAtMost_one_of_common_exchange
      (C := C) hfeasible haccept hunstable hvar
      (fun hxP hyP hcardP hchoiceP hyQ hxQ hcardQ hchoiceQ =>
        HasCommonCanonicalExchangeBase.of_erase_sdiff_card_le_one
          (P := _) (Q := _) (x := _) (y := _)
          hxP hyQ hcardP hcardQ hq
          (hnear hxP hyP hcardP hchoiceP hyQ hxQ hcardQ hchoiceQ))
      hxy

/--
Minimal opposite canonical witnesses must be near.  Otherwise a finite
first-loss descent constructs a strictly closer opposite canonical witness,
contradicting minimality.
-/
theorem oppositeCanonicalDiffCard_le_one_of_minimal_oppositeCanonicalChoices
    [Fintype α] {q : ℕ} {C : ChoiceRule α}
    (hfeasible : Feasible C) (haccept : QAcceptant q C)
    (hunstable : DUnstable 1 C) (hvar : VariabilityAtMost 1 C)
    {x y : α} {P Q : Finset α}
    (hcanon : OppositeCanonicalChoices C q x y P Q)
    (hmin :
      ∀ P' Q', OppositeCanonicalChoices C q x y P' Q' →
        oppositeCanonicalDiffCard P Q x y ≤
          oppositeCanonicalDiffCard P' Q' x y) :
    oppositeCanonicalDiffCard P Q x y ≤ 1 := by
  classical
  by_contra hnotNear
  have hdiff_gt : 1 < oppositeCanonicalDiffCard P Q x y :=
    Nat.lt_of_not_ge hnotNear
  rcases hcanon with
    ⟨hxP, hyP, hcardP, hchoiceP, hyQ, hxQ, hcardQ, hchoiceQ⟩
  have hsub : Substitutable C :=
    substitutable_of_dUnstable_one_of_feasible_of_qAcceptant
      (C := C) hfeasible haccept hunstable
  have hconsistent : Consistent C :=
    consistent_of_qAcceptant_of_substitutable haccept hsub
  let A : Finset α := P.erase x
  let B : Finset α := Q.erase y
  have hdiff_gt_AB : 1 < (A \ B).card := by
    simpa [oppositeCanonicalDiffCard, A, B] using hdiff_gt
  have hdiff_nonempty : (A \ B).Nonempty :=
    Finset.card_pos.mp (by omega)
  rcases hdiff_nonempty with ⟨a, haD⟩
  rcases Finset.mem_sdiff.mp haD with ⟨haA, haNotB⟩
  rcases Finset.mem_erase.mp haA with ⟨hax, haP⟩
  have hay : a ≠ y := by
    intro hay_eq
    exact hyP (by simpa [hay_eq] using haP)
  have haNotQ : a ∉ Q := by
    intro haQ
    exact haNotB (Finset.mem_erase.mpr ⟨hay, haQ⟩)
  let X₀ : Finset α := insert y (P.erase a)
  have hx_ne_a : x ≠ a := by
    intro hxa
    exact hax hxa.symm
  have hxX₀ : x ∈ X₀ := by
    exact Finset.mem_insert_of_mem
      (Finset.mem_erase.mpr ⟨hx_ne_a, hxP⟩)
  have hyX₀ : y ∈ X₀ :=
    Finset.mem_insert_self y (P.erase a)
  have hy_not_erase_a : y ∉ P.erase a := by
    intro hyErase
    exact hyP (Finset.mem_of_mem_erase hyErase)
  have hcardX₀ : X₀.card = q := by
    have herase := Finset.card_erase_add_one haP
    change (insert y (P.erase a)).card = q
    rw [Finset.card_insert_of_notMem hy_not_erase_a]
    omega
  have hCX₀ : C X₀ = X₀ :=
    QAcceptant.eq_of_card_le hfeasible haccept (by omega)
  have hxCX₀ : x ∈ C X₀ := by
    simpa [hCX₀] using hxX₀
  have hyCX₀ : y ∈ C X₀ := by
    simpa [hCX₀] using hyX₀
  let E : Finset α := B \ A
  let U : Finset α := X₀ ∪ E
  have hinsertxQ_subset_U : insert x Q ⊆ U := by
    intro t ht
    rw [Finset.mem_insert] at ht
    rcases ht with rfl | htQ
    · exact Finset.mem_union_left E hxX₀
    · by_cases hty : t = y
      · subst t
        exact Finset.mem_union_left E hyX₀
      · have htB : t ∈ B := Finset.mem_erase.mpr ⟨hty, htQ⟩
        by_cases htA : t ∈ A
        · rcases Finset.mem_erase.mp htA with ⟨htx, htP⟩
          have hta : t ≠ a := by
            intro hta_eq
            subst t
            exact haNotB htB
          exact Finset.mem_union_left E
            (Finset.mem_insert_of_mem
              (Finset.mem_erase.mpr ⟨hta, htP⟩))
        · exact Finset.mem_union_right X₀
            (Finset.mem_sdiff.mpr ⟨htB, htA⟩)
  have hxNotC_insertxQ : x ∉ C (insert x Q) := by
    simpa [hchoiceQ] using hxQ
  have hxNotCU : x ∉ C U :=
    not_mem_choice_of_substitutable_of_subset_of_mem_of_not_mem
      (C := C) hsub hinsertxQ_subset_U
      (Finset.mem_insert_self x Q) hxNotC_insertxQ
  have hX₀U : X₀ ⊆ U := by
    intro t ht
    exact Finset.mem_union_left E ht
  rcases exists_one_step_loss_of_mem_choice_of_not_mem_choice_of_subset
      (C := C) hX₀U hxCX₀ hxNotCU with
    ⟨W, b, hX₀W, hWU, hbU, hbW, hxCW, hxNotCbW⟩
  have hxy_ne : x ≠ y := by
    intro hxy_eq
    subst y
    exact hyP hxP
  have hyNotCW : y ∉ C W := by
    intro hyCW
    have hinsert_a_X₀ : insert a X₀ = insert y P := by
      simpa [X₀] using
        insert_erase_insert_eq_insert_of_mem (P := P) (a := a) (y := y) haP
    have hyNotC_insert_a_X₀ : y ∉ C (insert a X₀) := by
      simpa [hinsert_a_X₀, hchoiceP] using hyP
    have hsubset_insert_a : insert a X₀ ⊆ insert a W := by
      intro t ht
      rw [Finset.mem_insert] at ht
      rw [Finset.mem_insert]
      rcases ht with rfl | htX₀
      · exact Or.inl rfl
      · exact Or.inr (hX₀W htX₀)
    have hy_insert_a_X₀ : y ∈ insert a X₀ :=
      Finset.mem_insert_of_mem hyX₀
    have hyNotC_insert_a_W : y ∉ C (insert a W) :=
      not_mem_choice_of_substitutable_of_subset_of_mem_of_not_mem
        (C := C) hsub hsubset_insert_a hy_insert_a_X₀
        hyNotC_insert_a_X₀
    have hyLoss : y ∈ C W \ C (insert a W) :=
      Finset.mem_sdiff.mpr ⟨hyCW, hyNotC_insert_a_W⟩
    have hxLoss : x ∈ C W \ C (insert b W) :=
      Finset.mem_sdiff.mpr ⟨hxCW, hxNotCbW⟩
    have hy_eq_x :=
      not_two_distinct_losses_same_base_of_variabilityAtMost_one
        (C := C) hvar hyLoss hxLoss
    exact hxy_ne hy_eq_x.symm
  rcases exists_one_step_loss_of_mem_choice_of_not_mem_choice_of_subset
      (C := C) hX₀W hyCX₀ hyNotCW with
    ⟨W₀, c, hX₀W₀, hW₀W, hcW, hcW₀, hyCW₀, hyNotCcW₀⟩
  let Z : Finset α := insert c W₀
  have hZW : Z ⊆ W := by
    intro t ht
    change t ∈ insert c W₀ at ht
    rw [Finset.mem_insert] at ht
    rcases ht with rfl | htW₀
    · exact hcW
    · exact hW₀W htW₀
  have hxZ : x ∈ Z := by
    exact Finset.mem_insert_of_mem (hX₀W₀ hxX₀)
  have hyZ : y ∈ Z := by
    exact Finset.mem_insert_of_mem (hX₀W₀ hyX₀)
  have hxCZ : x ∈ C Z :=
    hsub hZW (Finset.mem_inter.mpr ⟨hxZ, hxCW⟩)
  have hyNotCZ : y ∉ C Z := by
    simpa [Z] using hyNotCcW₀
  let P' : Finset α := C Z
  have hcardP' : P'.card = q := by
    have hnot_le : ¬ Z.card ≤ q := by
      intro hle
      have hCZ_eq : C Z = Z :=
        QAcceptant.eq_of_card_le hfeasible haccept hle
      exact hyNotCZ (by simpa [hCZ_eq] using hyZ)
    have hq_le : q ≤ Z.card := le_of_lt (Nat.lt_of_not_ge hnot_le)
    have hcardCZ : (C Z).card = q := by
      rw [haccept Z, Nat.min_eq_left hq_le]
    simpa [P'] using hcardCZ
  have hP'_subset_Z : P' ⊆ Z := by
    intro t ht
    exact hfeasible Z ht
  have hinsert_y_P'_subset_Z : insert y P' ⊆ Z := by
    intro t ht
    rw [Finset.mem_insert] at ht
    rcases ht with rfl | htP'
    · exact hyZ
    · exact hP'_subset_Z htP'
  have hP'_subset_insert_y : P' ⊆ insert y P' := by
    intro t ht
    exact Finset.mem_insert_of_mem ht
  have hchoiceP' : C (insert y P') = P' := by
    change C (insert y (C Z)) = C Z
    exact (hconsistent hP'_subset_insert_y hinsert_y_P'_subset_Z).symm
  have hcanon' : OppositeCanonicalChoices C q x y P' Q :=
    ⟨by simpa [P'] using hxCZ,
      by simpa [P'] using hyNotCZ,
      hcardP',
      hchoiceP',
      hyQ, hxQ, hcardQ, hchoiceQ⟩
  have hZU : Z ⊆ U := hZW.trans hWU
  have hsubset_diff :
      (P'.erase x) \ (Q.erase y) ⊆
        ((P.erase x) \ (Q.erase y)).erase a := by
    intro t ht
    rcases Finset.mem_sdiff.mp ht with ⟨htP'erase, htNotB⟩
    rcases Finset.mem_erase.mp htP'erase with ⟨htx, htP'⟩
    have htZ : t ∈ Z := hP'_subset_Z htP'
    have htU : t ∈ U := hZU htZ
    have htNotE : t ∉ E := by
      intro htE
      exact htNotB (Finset.mem_sdiff.mp htE).1
    have htX₀ : t ∈ X₀ := by
      rcases Finset.mem_union.mp htU with htX₀ | htE
      · exact htX₀
      · exact False.elim (htNotE htE)
    change t ∈ insert y (P.erase a) at htX₀
    rcases Finset.mem_insert.mp htX₀ with ht_y | htEraseA
    · subst t
      exact False.elim (hyNotCZ htP')
    · rcases Finset.mem_erase.mp htEraseA with ⟨hta, htP⟩
      exact Finset.mem_erase.mpr
        ⟨hta, Finset.mem_sdiff.mpr
          ⟨Finset.mem_erase.mpr ⟨htx, htP⟩, htNotB⟩⟩
  have hlt :
      oppositeCanonicalDiffCard P' Q x y <
        oppositeCanonicalDiffCard P Q x y :=
    oppositeCanonicalDiffCard_lt_of_subset_erase
      (P := P) (P' := P') (Q := Q) (x := x) (y := y) (a := a)
      (by simpa [A, B] using haD) hsubset_diff
  have hle_min := hmin P' Q hcanon'
  omega

/--
Asymmetry follows if every minimal pair of opposite canonical witnesses is
near after deleting the compared applicants.
-/
theorem revealedAbove_asymm_of_variabilityAtMost_one_of_minimal_near
    [Fintype α] {q : ℕ} {C : ChoiceRule α}
    (hfeasible : Feasible C) (haccept : QAcceptant q C)
    (hunstable : DUnstable 1 C) (hvar : VariabilityAtMost 1 C)
    (hq : 1 < q)
    (hminimalNear :
      ∀ {x y : α} {P Q : Finset α},
        OppositeCanonicalChoices C q x y P Q →
          (∀ P' Q', OppositeCanonicalChoices C q x y P' Q' →
            oppositeCanonicalDiffCard P Q x y ≤
              oppositeCanonicalDiffCard P' Q' x y) →
            oppositeCanonicalDiffCard P Q x y ≤ 1)
    {x y : α} (hxy : RevealedAbove C x y) :
    ¬ RevealedAbove C y x := by
  intro hyx
  have hsub : Substitutable C :=
    substitutable_of_dUnstable_one_of_feasible_of_qAcceptant
      (C := C) hfeasible haccept hunstable
  rcases RevealedAbove.exists_canonical_choice_of_substitutable
      (C := C) hfeasible haccept hsub hxy with
    ⟨P, hxP, hyP, hcardP, hchoiceP⟩
  rcases RevealedAbove.exists_canonical_choice_of_substitutable
      (C := C) hfeasible haccept hsub hyx with
    ⟨Q, hyQ, hxQ, hcardQ, hchoiceQ⟩
  have hexists :
      ∃ P Q, OppositeCanonicalChoices C q x y P Q :=
    ⟨P, Q, hxP, hyP, hcardP, hchoiceP,
      hyQ, hxQ, hcardQ, hchoiceQ⟩
  rcases exists_minimal_oppositeCanonicalChoices hexists with
    ⟨P₀, Q₀, hcanon₀, hmin₀⟩
  have hnear₀ :
      ((P₀.erase x) \ (Q₀.erase y)).card ≤ 1 := by
    simpa [oppositeCanonicalDiffCard] using
      hminimalNear hcanon₀ hmin₀
  rcases hcanon₀ with
    ⟨hxP₀, hyP₀, hcardP₀, hchoiceP₀,
      hyQ₀, hxQ₀, hcardQ₀, hchoiceQ₀⟩
  exact
    false_of_opposite_canonical_choices_of_common_exchange
      (C := C) hfeasible haccept hvar
      hxP₀ hyP₀ hcardP₀ hchoiceP₀
      hyQ₀ hxQ₀ hcardQ₀ hchoiceQ₀
      (HasCommonCanonicalExchangeBase.of_erase_sdiff_card_le_one
        (P := P₀) (Q := Q₀) (x := x) (y := y)
        hxP₀ hyQ₀ hcardP₀ hcardQ₀ hq hnear₀)

/--
For capacity one, opposite revealed comparisons are impossible: the canonical
chosen sets are singletons, so the two canonical choice equations apply to the
same two-applicant pool with different chosen singletons.
-/
theorem revealedAbove_asymm_of_qAcceptant_one_of_substitutable
    {C : ChoiceRule α}
    (hfeasible : Feasible C) (haccept : QAcceptant 1 C)
    (hsub : Substitutable C)
    {x y : α} (hxy : RevealedAbove C x y) :
    ¬ RevealedAbove C y x := by
  intro hyx
  rcases RevealedAbove.exists_canonical_choice_of_substitutable
      (C := C) hfeasible haccept hsub hxy with
    ⟨P, hxP, hyP, hcardP, hchoiceP⟩
  rcases RevealedAbove.exists_canonical_choice_of_substitutable
      (C := C) hfeasible haccept hsub hyx with
    ⟨Q, hyQ, _hxQ, hcardQ, hchoiceQ⟩
  have hP : P = {x} := by
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨hxP, ?_⟩
    intro z hzP
    exact
      (Finset.card_le_one.mp (by omega : P.card ≤ 1))
        z hzP x hxP
  have hQ : Q = {y} := by
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨hyQ, ?_⟩
    intro z hzQ
    exact
      (Finset.card_le_one.mp (by omega : Q.card ≤ 1))
        z hzQ y hyQ
  have hsamePool : insert y P = insert x Q := by
    rw [hP, hQ]
    ext z
    simp [or_comm]
  have hPQ : P = Q := by
    calc
      P = C (insert y P) := hchoiceP.symm
      _ = C (insert x Q) := by rw [hsamePool]
      _ = Q := hchoiceQ
  exact hyP (by simpa [hPQ] using hyQ)

/--
Given asymmetry, revealed preference is transitive.  The proof adds `c` to a
canonical witness for `a` revealed above `b`; if `c` were chosen, it would
reveal `c` above `b`, contradicting `b` revealed above `c`.
-/
theorem RevealedAbove.trans_of_asymm
    {q : ℕ} {C : ChoiceRule α}
    (hfeasible : Feasible C) (haccept : QAcceptant q C)
    (hsub : Substitutable C)
    (hasymm : ∀ {x y}, RevealedAbove C x y → ¬ RevealedAbove C y x)
    {a b c : α}
    (hab : RevealedAbove C a b) (hbc : RevealedAbove C b c) :
    RevealedAbove C a c := by
  rcases RevealedAbove.exists_canonical_choice_of_substitutable
      hfeasible haccept hsub hab with
    ⟨P, haP, hbP, _hcardP, hchoiceP⟩
  let X : Finset α := insert b P
  have haCX : a ∈ C X := by
    simpa [X, hchoiceP] using haP
  have hbX : b ∈ X := Finset.mem_insert_self b P
  have hbNotCX : b ∉ C X := by
    simpa [X, hchoiceP] using hbP
  let Xc : Finset α := insert c X
  have hX_subset_Xc : X ⊆ Xc := by
    intro z hz
    exact Finset.mem_insert_of_mem hz
  have hcNotCXc : c ∉ C Xc := by
    intro hcCXc
    have hbNotCXc : b ∉ C Xc := by
      intro hbCXc
      exact hbNotCX
        (hsub hX_subset_Xc (Finset.mem_inter.mpr ⟨hbX, hbCXc⟩))
    have hcb : RevealedAbove C c b :=
      ⟨Xc, hcCXc, Finset.mem_insert_of_mem hbX, hbNotCXc⟩
    exact hasymm hbc hcb
  have hCXc_subset_X : C Xc ⊆ X := by
    intro z hz
    have hzOffered : z ∈ Xc := hfeasible Xc hz
    rw [Finset.mem_insert] at hzOffered
    rcases hzOffered with rfl | hzX
    · exact False.elim (hcNotCXc hz)
    · exact hzX
  have hconsistent : Consistent C :=
    consistent_of_qAcceptant_of_substitutable haccept hsub
  have hsame : C Xc = C X :=
    hconsistent hCXc_subset_X hX_subset_Xc
  refine ⟨Xc, ?_, Finset.mem_insert_self c X, hcNotCXc⟩
  simpa [hsame] using haCX

/-- A transitive revealed relation is asymmetric because it is irreflexive. -/
theorem RevealedAbove.asymm_of_trans {C : ChoiceRule α}
    (htrans :
      ∀ {x y z}, RevealedAbove C x y → RevealedAbove C y z →
        RevealedAbove C x z)
    {x y : α} (hxy : RevealedAbove C x y) :
    ¬ RevealedAbove C y x := by
  intro hyx
  exact RevealedAbove.irrefl (C := C) x (htrans hxy hyx)

set_option linter.unusedSectionVars false in
/--
Any irreflexive transitive relation extends to a strict total order.
-/
theorem exists_strictTotalOrder_extension_of_trans
    {r : α → α → Prop}
    (hirr : ∀ x, ¬ r x x)
    (htrans : ∀ {x y z}, r x y → r y z → r x z) :
    ∃ s : α → α → Prop, StrictTotalOrder s ∧
      ∀ {x y}, r x y → s x y := by
  classical
  let leR : α → α → Prop := fun x y => x = y ∨ r x y
  haveI : IsPartialOrder α leR := by
    refine
      { refl := ?_
        trans := ?_
        antisymm := ?_ }
    · intro x
      exact Or.inl rfl
    · intro x y z hxy hyz
      rcases hxy with rfl | hxy
      · exact hyz
      rcases hyz with rfl | hyz
      · exact Or.inr hxy
      · exact Or.inr (htrans hxy hyz)
    · intro x y hxy hyx
      rcases hxy with hxy_eq | hxy_rel
      · exact hxy_eq
      rcases hyx with hyx_eq | hyx_rel
      · exact hyx_eq.symm
      · exact False.elim (hirr x (htrans hxy_rel hyx_rel))
  rcases extend_partialOrder leR with ⟨le, hlinear, hle⟩
  let s : α → α → Prop := fun x y => le x y ∧ x ≠ y
  refine ⟨s, ?_, ?_⟩
  · constructor
    · intro x hx
      exact hx.2 rfl
    constructor
    · intro x y z hxy hyz
      refine ⟨hlinear.trans x y z hxy.1 hyz.1, ?_⟩
      intro hxz
      subst z
      have hyx : le y x := hyz.1
      have hxy_eq : x = y := hlinear.antisymm x y hxy.1 hyx
      exact hxy.2 hxy_eq
    · intro x y hne
      rcases hlinear.total x y with hxy | hyx
      · exact Or.inl ⟨hxy, hne⟩
      · exact Or.inr ⟨hyx, hne.symm⟩
  · intro x y hxy
    refine ⟨hle x y (Or.inr hxy), ?_⟩
    intro hxy_eq
    subst y
    exact hirr x hxy

/--
If revealed preference is transitive, extending it gives a q-representative
order.
-/
theorem qRepresentative_of_revealedAbove_trans
    {q : ℕ} {C : ChoiceRule α}
    (hfeasible : Feasible C) (haccept : QAcceptant q C)
    (htrans :
      ∀ {x y z}, RevealedAbove C x y → RevealedAbove C y z →
        RevealedAbove C x z) :
    QRepresentative q C := by
  rcases exists_strictTotalOrder_extension_of_trans
      (r := RevealedAbove C)
      (fun x => RevealedAbove.irrefl (C := C) x)
      (by intro x y z hxy hyz; exact htrans hxy hyz) with
    ⟨r, hstrict, hext⟩
  refine ⟨r, hstrict, hfeasible, haccept, ?_⟩
  intro X x y hxCX hyX hyNotCX
  exact hext ⟨X, hxCX, hyX, hyNotCX⟩

/--
Thus the full converse is reduced to the asymmetry/exchange argument.
-/
theorem qRepresentative_of_revealedAbove_asymm
    {q : ℕ} {C : ChoiceRule α}
    (hfeasible : Feasible C) (haccept : QAcceptant q C)
    (hunstable : DUnstable 1 C)
    (hasymm : ∀ {x y}, RevealedAbove C x y → ¬ RevealedAbove C y x) :
    QRepresentative q C := by
  have hsub : Substitutable C :=
    substitutable_of_dUnstable_one_of_feasible_of_qAcceptant
      (C := C) hfeasible haccept hunstable
  apply qRepresentative_of_revealedAbove_trans (C := C) hfeasible haccept
  intro x y z hxy hyz
  exact RevealedAbove.trans_of_asymm
    (C := C) hfeasible haccept hsub hasymm hxy hyz

/--
Capacity-one converse: every feasible 1-acceptant, 1-unstable rule is
1-representative.
-/
theorem qRepresentative_of_qAcceptant_one_of_dUnstable_one
    {C : ChoiceRule α}
    (hfeasible : Feasible C) (haccept : QAcceptant 1 C)
    (hunstable : DUnstable 1 C) :
    QRepresentative 1 C := by
  have hsub : Substitutable C :=
    substitutable_of_dUnstable_one_of_feasible_of_qAcceptant
      (C := C) hfeasible haccept hunstable
  exact
    qRepresentative_of_revealedAbove_asymm
      (C := C) hfeasible haccept hunstable
      (fun hxy =>
        revealedAbove_asymm_of_qAcceptant_one_of_substitutable
          (C := C) hfeasible haccept hsub hxy)

/--
For capacities above one, the q-representative converse is reduced to the
near-canonical-witness condition.
-/
theorem qRepresentative_of_near_opposite_canonical_choices
    [Fintype α] {q : ℕ} {C : ChoiceRule α}
    (hfeasible : Feasible C) (haccept : QAcceptant q C)
    (hunstable : DUnstable 1 C) (hvar : VariabilityAtMost 1 C)
    (hq : 1 < q)
    (hnear :
      ∀ {x y : α} {P Q : Finset α},
        x ∈ P → y ∉ P → P.card = q → C (insert y P) = P →
        y ∈ Q → x ∉ Q → Q.card = q → C (insert x Q) = Q →
        ((P.erase x) \ (Q.erase y)).card ≤ 1) :
    QRepresentative q C := by
  exact
    qRepresentative_of_revealedAbove_asymm
      (C := C) hfeasible haccept hunstable
      (fun hxy =>
        revealedAbove_asymm_of_variabilityAtMost_one_of_near_canonical_choices
          (C := C) hfeasible haccept hunstable hvar hq hnear hxy)

/--
For capacities above one, the q-representative converse is reduced to proving
the near condition for minimal opposite canonical witness pairs.
-/
theorem qRepresentative_of_minimal_opposite_canonical_choices_near
    [Fintype α] {q : ℕ} {C : ChoiceRule α}
    (hfeasible : Feasible C) (haccept : QAcceptant q C)
    (hunstable : DUnstable 1 C) (hvar : VariabilityAtMost 1 C)
    (hq : 1 < q)
    (hminimalNear :
      ∀ {x y : α} {P Q : Finset α},
        OppositeCanonicalChoices C q x y P Q →
          (∀ P' Q', OppositeCanonicalChoices C q x y P' Q' →
            oppositeCanonicalDiffCard P Q x y ≤
              oppositeCanonicalDiffCard P' Q' x y) →
            oppositeCanonicalDiffCard P Q x y ≤ 1) :
    QRepresentative q C := by
  exact
    qRepresentative_of_revealedAbove_asymm
      (C := C) hfeasible haccept hunstable
      (fun hxy =>
        revealedAbove_asymm_of_variabilityAtMost_one_of_minimal_near
          (C := C) hfeasible haccept hunstable hvar hq hminimalNear hxy)

/--
Full q-representative converse: feasible q-acceptance, 1-instability, and
variability at most one imply representation by one priority order.
-/
theorem qRepresentative_of_feasible_qAcceptant_dUnstable_one_variabilityAtMost_one
    [Fintype α] {q : ℕ} {C : ChoiceRule α}
    (hfeasible : Feasible C) (haccept : QAcceptant q C)
    (hunstable : DUnstable 1 C) (hvar : VariabilityAtMost 1 C) :
    QRepresentative q C := by
  by_cases hq0 : q = 0
  · subst q
    have hasymm :
        ∀ {x y}, RevealedAbove C x y → ¬ RevealedAbove C y x := by
      intro x y hxy _hyx
      rcases hxy with ⟨X, hxCX, _hyX, _hyNotCX⟩
      have hcard : (C X).card = 0 := by
        simpa using haccept X
      have hCX : C X = ∅ := Finset.card_eq_zero.mp hcard
      simp [hCX] at hxCX
    exact qRepresentative_of_revealedAbove_asymm
      (C := C) hfeasible haccept hunstable hasymm
  · by_cases hq1 : q = 1
    · subst q
      exact qRepresentative_of_qAcceptant_one_of_dUnstable_one
        (C := C) hfeasible haccept hunstable
    · have hq : 1 < q := by omega
      exact
        qRepresentative_of_minimal_opposite_canonical_choices_near
          (C := C) hfeasible haccept hunstable hvar hq
          (fun hcanon hmin =>
            oppositeCanonicalDiffCard_le_one_of_minimal_oppositeCanonicalChoices
              (C := C) hfeasible haccept hunstable hvar hcanon hmin)

end QRepresentativeConverseWork
end FiniteChoice
end AppliedModelingLib
