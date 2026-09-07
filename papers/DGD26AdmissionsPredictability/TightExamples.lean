import AppliedModelingLib.Foundations.Math.FiniteChoice
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic

/-!
# Tight Instability Examples

Concrete paper-local examples toward the theorem that q-acceptant choice
functions can be tightly d-unstable for every `1 ≤ d ≤ 2q`.

This file currently formalizes the tight-1 case, small even cases (`q = 1`,
tight instability `2`; and `q = 2`, tight instability `4`), and nontrivial
higher odd cases (`q = 2`, tight instability `3`; and `q = 3`, tight
instability `5`).  It also formalizes padded even and odd trigger-switch
families, giving tight `d`-instability constructions for every `1 ≤ d ≤ 2q`.
-/

namespace DGD26AdmissionsPredictability

open AppliedModelingLib.FiniteChoice

/-! ## Ranked trigger-switch construction criteria -/

section RankedTriggerSwitch

variable {β : Type*} [DecidableEq β] [LinearOrder β]

/--
A concrete trigger switch between two top-q ranked priority rules.  Lower rank
means higher priority; ties are broken by the ambient order on `β`.
-/
noncomputable def rankedTriggerSwitchChoice (q : ℕ)
    (τ : Finset β → Prop) [DecidablePred τ]
    (rank₀ rank₁ : β → ℕ) : ChoiceRule β :=
  triggerSwitchChoice τ
    (rankedTopQChoice q rank₀)
    (rankedTopQChoice q rank₁)

/-- A ranked trigger switch is feasible. -/
theorem rankedTriggerSwitchChoice_feasible
    {q : ℕ} {τ : Finset β → Prop} [DecidablePred τ]
    {rank₀ rank₁ : β → ℕ} :
    Feasible (rankedTriggerSwitchChoice q τ rank₀ rank₁) := by
  classical
  simpa [rankedTriggerSwitchChoice] using
    (triggerSwitchChoice_feasible
      (rankedTopQChoice_feasible (α := β) q rank₀)
      (rankedTopQChoice_feasible (α := β) q rank₁))

/-- A ranked trigger switch is q-acceptant. -/
theorem rankedTriggerSwitchChoice_qAcceptant
    {q : ℕ} {τ : Finset β → Prop} [DecidablePred τ]
    {rank₀ rank₁ : β → ℕ} :
    QAcceptant q (rankedTriggerSwitchChoice q τ rank₀ rank₁) := by
  classical
  simpa [rankedTriggerSwitchChoice] using
    (triggerSwitchChoice_qAcceptant
      (rankedTopQChoice_qAcceptant (α := β) q rank₀)
      (rankedTopQChoice_qAcceptant (α := β) q rank₁))

/--
Even ranked trigger-switch construction criterion.  If the false-to-true
switch can lose at most `n` old admits, and one witness loses exactly `n`
while rejecting the trigger applicant, the rule is tightly `2*n`-unstable.
-/
theorem rankedTriggerSwitchChoice_tightly_even
    {q n : ℕ} (hn : 0 < n)
    {τ : Finset β → Prop} [DecidablePred τ]
    {rank₀ rank₁ : β → ℕ}
    (hτmono : ∀ {X x}, x ∉ X → τ X → τ (insert x X))
    (hcross :
      ∀ X x, x ∉ X → ¬ τ X → τ (insert x X) →
        (rankedTopQChoice q rank₀ X \
          rankedTopQChoice q rank₁ (insert x X)).card ≤ n)
    {X₀ : Finset β} {z : β}
    (hzX₀ : z ∉ X₀) (hcard : q ≤ X₀.card)
    (hbefore : ¬ τ X₀) (hafter : τ (insert z X₀))
    (hzRejected : z ∉ rankedTopQChoice q rank₁ (insert z X₀))
    (hloss :
      (rankedTopQChoice q rank₀ X₀ \
        rankedTopQChoice q rank₁ (insert z X₀)).card = n) :
    TightlyDUnstable (2 * n)
      (rankedTriggerSwitchChoice q τ rank₀ rank₁) := by
  classical
  simpa [rankedTriggerSwitchChoice] using
    (triggerSwitchChoice_tightly_even
      (q := q) (n := n) hn hτmono
      (rankedTopQChoice_feasible (α := β) q rank₀)
      (rankedTopQChoice_feasible (α := β) q rank₁)
      (rankedTopQChoice_qRepresentative (α := β) q rank₀)
      (rankedTopQChoice_qRepresentative (α := β) q rank₁)
      hcross hzX₀ hcard hbefore hafter hzRejected hloss)

/--
Odd ranked trigger-switch construction criterion.  If the false-to-true switch
loses at most `n` old admits and chooses the fresh trigger applicant, and one
witness loses exactly `n`, the rule is tightly `2*n - 1`-unstable.
-/
theorem rankedTriggerSwitchChoice_tightly_odd
    {q n : ℕ} (hn : 0 < n)
    {τ : Finset β → Prop} [DecidablePred τ]
    {rank₀ rank₁ : β → ℕ}
    (hτmono : ∀ {X x}, x ∉ X → τ X → τ (insert x X))
    (hcross_loss :
      ∀ X x, x ∉ X → ¬ τ X → τ (insert x X) →
        (rankedTopQChoice q rank₀ X \
          rankedTopQChoice q rank₁ (insert x X)).card ≤ n)
    (hcross_chosen :
      ∀ X x, x ∉ X → ¬ τ X → τ (insert x X) →
        x ∈ rankedTopQChoice q rank₁ (insert x X))
    {X₀ : Finset β} {z : β}
    (hzX₀ : z ∉ X₀) (hcard : q ≤ X₀.card)
    (hbefore : ¬ τ X₀) (hafter : τ (insert z X₀))
    (hzChosen : z ∈ rankedTopQChoice q rank₁ (insert z X₀))
    (hloss :
      (rankedTopQChoice q rank₀ X₀ \
        rankedTopQChoice q rank₁ (insert z X₀)).card = n) :
    TightlyDUnstable (2 * n - 1)
      (rankedTriggerSwitchChoice q τ rank₀ rank₁) := by
  classical
  simpa [rankedTriggerSwitchChoice] using
    (triggerSwitchChoice_tightly_odd
      (q := q) (n := n) hn hτmono
      (rankedTopQChoice_feasible (α := β) q rank₀)
      (rankedTopQChoice_feasible (α := β) q rank₁)
      (rankedTopQChoice_qRepresentative (α := β) q rank₀)
      (rankedTopQChoice_qRepresentative (α := β) q rank₁)
      hcross_loss hcross_chosen hzX₀ hcard hbefore hafter
      hzChosen hloss)

end RankedTriggerSwitch

/-! ## Padded lower-even witness construction -/

section PaddedEven

/-- Fresh trigger applicant for the lower-even padded construction. -/
noncomputable def paddedEvenZ (q n : ℕ) : Fin (q + n + 1) :=
  ⟨q + n, by omega⟩

/-- Witness pool: every applicant except the trigger. -/
noncomputable def paddedEvenBase (q n : ℕ) : Finset (Fin (q + n + 1)) :=
  Finset.univ.erase (paddedEvenZ q n)

/-- Before-trigger rank: the first q applicants are the top q. -/
def paddedEvenRank₀ (q n : ℕ) (i : Fin (q + n + 1)) : ℕ :=
  if i.1 < q then 0 else 2

/--
After-trigger rank: padding remains first, the promoted block moves above the
demoted block, and the trigger itself is last.
-/
def paddedEvenRank₁ (q n : ℕ) (i : Fin (q + n + 1)) : ℕ :=
  if i.1 < q - n then 0
  else if q ≤ i.1 ∧ i.1 < q + n then 1
  else if i.1 < q then 2
  else 3

/-- The q applicants chosen before the even trigger fires. -/
def paddedEvenBeforeChoiceSet (q n : ℕ) : Finset (Fin (q + n + 1)) :=
  Finset.univ.filter (fun i => i.1 < q)

/-- The q applicants chosen after the even trigger fires. -/
def paddedEvenAfterChoiceSet (q n : ℕ) : Finset (Fin (q + n + 1)) :=
  Finset.univ.filter (fun i => i.1 < q - n ∨ (q ≤ i.1 ∧ i.1 < q + n))

/-- The block demoted from the before choice when the even trigger fires. -/
def paddedEvenDemotedBlock (q n : ℕ) : Finset (Fin (q + n + 1)) :=
  Finset.univ.filter (fun i => q - n ≤ i.1 ∧ i.1 < q)

/-- The padded lower-even trigger-switch rule. -/
noncomputable def paddedEvenChoice (q n : ℕ) : ChoiceRule (Fin (q + n + 1)) :=
  rankedTriggerSwitchChoice q
    (fun X : Finset (Fin (q + n + 1)) => paddedEvenZ q n ∈ X)
    (paddedEvenRank₀ q n)
    (paddedEvenRank₁ q n)

theorem paddedEvenBeforeChoiceSet_card (q n : ℕ) :
    (paddedEvenBeforeChoiceSet q n).card = q := by
  unfold paddedEvenBeforeChoiceSet
  rw [Fin.card_filter_val_lt]
  omega

theorem paddedEvenAfterChoiceSet_card {q n : ℕ} (hnq : n ≤ q) :
    (paddedEvenAfterChoiceSet q n).card = q := by
  classical
  unfold paddedEvenAfterChoiceSet
  let P : Finset (Fin (q + n + 1)) :=
    Finset.univ.filter (fun i => i.1 < q - n)
  let B : Finset (Fin (q + n + 1)) :=
    Finset.univ.filter (fun i => q ≤ i.1 ∧ i.1 < q + n)
  have hfilter : Finset.univ.filter
      (fun i : Fin (q + n + 1) => i.1 < q - n ∨ (q ≤ i.1 ∧ i.1 < q + n)) =
      P ∪ B := by
    ext i
    simp [P, B]
  rw [hfilter]
  have hdisj : Disjoint P B := by
    rw [Finset.disjoint_left]
    intro i hiP hiB
    simp [P] at hiP
    simp [B] at hiB
    omega
  rw [Finset.card_union_of_disjoint hdisj]
  have hP : P.card = q - n := by
    simp [P, Fin.card_filter_val_lt]
    omega
  have hB : B.card = n := by
    let High : Finset (Fin (q + n + 1)) :=
      Finset.univ.filter (fun i => i.1 < q + n)
    let Low : Finset (Fin (q + n + 1)) :=
      Finset.univ.filter (fun i => i.1 < q)
    have hB_eq : B = High \ Low := by
      ext i
      simp [B, High, Low]
      omega
    have hLowSub : Low ⊆ High := by
      intro i hi
      simp [Low] at hi
      simp [High]
      omega
    rw [hB_eq, Finset.card_sdiff_of_subset hLowSub]
    have hHigh : High.card = q + n := by
      simp [High, Fin.card_filter_val_lt]
    have hLow : Low.card = q := by
      simp [Low, Fin.card_filter_val_lt]
      omega
    rw [hHigh, hLow]
    omega
  omega

theorem paddedEvenBeforeChoiceSet_subset_base (q n : ℕ) :
    paddedEvenBeforeChoiceSet q n ⊆ paddedEvenBase q n := by
  intro i hi
  simp [paddedEvenBeforeChoiceSet] at hi
  simp [paddedEvenBase, paddedEvenZ]
  intro hiz
  have hval := congrArg Fin.val hiz
  simp at hval
  omega

theorem paddedEvenBefore_choice_eq (q n : ℕ) :
    rankedTopQChoice q (paddedEvenRank₀ q n) (paddedEvenBase q n) =
      paddedEvenBeforeChoiceSet q n := by
  classical
  unfold rankedTopQChoice
  letI : LinearOrder (Fin (q + n + 1)) := orderByRank (paddedEvenRank₀ q n)
  exact linearTopQChoice_eq_of_card_of_forall_lt
    (α := Fin (q + n + 1))
    (paddedEvenBeforeChoiceSet_subset_base q n)
    (paddedEvenBeforeChoiceSet_card q n)
    (by
      intro s hs y _hyBase hyNot
      change (toLex (paddedEvenRank₀ q n s, s) : Lex (ℕ × Fin (q + n + 1))) <
        toLex (paddedEvenRank₀ q n y, y)
      apply Prod.Lex.left
      have hsRank : paddedEvenRank₀ q n s = 0 := by
        simp [paddedEvenRank₀, paddedEvenBeforeChoiceSet] at hs ⊢
        exact hs
      have hyRank : paddedEvenRank₀ q n y = 2 := by
        have hyge : ¬ y.1 < q := by
          intro hylt
          exact hyNot (by simp [paddedEvenBeforeChoiceSet, hylt])
        simp [paddedEvenRank₀, hyge]
      rw [hsRank, hyRank]
      omega)

theorem paddedEven_insert_base_eq_univ (q n : ℕ) :
    insert (paddedEvenZ q n) (paddedEvenBase q n) =
      (Finset.univ : Finset (Fin (q + n + 1))) := by
  ext i
  by_cases hiz : i = paddedEvenZ q n
  · subst i
    simp [paddedEvenBase]
  · simp [paddedEvenBase]

theorem paddedEvenAfter_choice_eq {q n : ℕ} (hnq : n ≤ q) :
    rankedTopQChoice q (paddedEvenRank₁ q n)
        (insert (paddedEvenZ q n) (paddedEvenBase q n)) =
      paddedEvenAfterChoiceSet q n := by
  classical
  rw [paddedEven_insert_base_eq_univ]
  unfold rankedTopQChoice
  letI : LinearOrder (Fin (q + n + 1)) := orderByRank (paddedEvenRank₁ q n)
  exact linearTopQChoice_eq_of_card_of_forall_lt
    (α := Fin (q + n + 1))
    (by intro i _hi; simp)
    (paddedEvenAfterChoiceSet_card hnq)
    (by
      intro s hs y _hyUniv hyNot
      change (toLex (paddedEvenRank₁ q n s, s) : Lex (ℕ × Fin (q + n + 1))) <
        toLex (paddedEvenRank₁ q n y, y)
      apply Prod.Lex.left
      have hsCond : s.1 < q - n ∨ (q ≤ s.1 ∧ s.1 < q + n) := by
        simpa [paddedEvenAfterChoiceSet] using hs
      have hyNotCond :
          ¬ (y.1 < q - n ∨ (q ≤ y.1 ∧ y.1 < q + n)) := by
        intro hyCond
        exact hyNot (by simpa [paddedEvenAfterChoiceSet] using hyCond)
      have hsRank : paddedEvenRank₁ q n s ≤ 1 := by
        rcases hsCond with hsP | hsB
        · simp [paddedEvenRank₁, hsP]
        · by_cases hsP : s.1 < q - n
          · simp [paddedEvenRank₁, hsP]
          · simp [paddedEvenRank₁, hsP, hsB]
      have hyRank : 2 ≤ paddedEvenRank₁ q n y := by
        have hyNotP : ¬ y.1 < q - n := by
          intro hyP
          exact hyNotCond (Or.inl hyP)
        have hyNotB : ¬ (q ≤ y.1 ∧ y.1 < q + n) := by
          intro hyB
          exact hyNotCond (Or.inr hyB)
        simp [paddedEvenRank₁, hyNotP, hyNotB]
        by_cases hyq : y.1 < q <;> simp [hyq]
      omega)

theorem paddedEven_fresh_not_chosen_after {q n : ℕ} (hnq : n ≤ q) :
    paddedEvenZ q n ∉
      rankedTopQChoice q (paddedEvenRank₁ q n)
        (insert (paddedEvenZ q n) (paddedEvenBase q n)) := by
  rw [paddedEvenAfter_choice_eq hnq]
  simp [paddedEvenAfterChoiceSet, paddedEvenZ]
  omega

theorem paddedEvenDemotedBlock_card {q n : ℕ} (hnq : n ≤ q) :
    (paddedEvenDemotedBlock q n).card = n := by
  classical
  let High : Finset (Fin (q + n + 1)) :=
    Finset.univ.filter (fun i => i.1 < q)
  let Low : Finset (Fin (q + n + 1)) :=
    Finset.univ.filter (fun i => i.1 < q - n)
  have hA_eq : paddedEvenDemotedBlock q n = High \ Low := by
    ext i
    simp [paddedEvenDemotedBlock, High, Low]
    omega
  have hLowSub : Low ⊆ High := by
    intro i hi
    simp [Low] at hi
    simp [High]
    omega
  rw [hA_eq, Finset.card_sdiff_of_subset hLowSub]
  have hHigh : High.card = q := by
    simp [High, Fin.card_filter_val_lt]
    omega
  have hLow : Low.card = q - n := by
    simp [Low, Fin.card_filter_val_lt]
    omega
  rw [hHigh, hLow]
  omega

theorem paddedEven_old_applicant_rank₁_le_two
    {q n : ℕ} {i : Fin (q + n + 1)}
    (hiNotZ : i ≠ paddedEvenZ q n) :
    paddedEvenRank₁ q n i ≤ 2 := by
  classical
  unfold paddedEvenRank₁
  split_ifs with hP hB hA
  · omega
  · omega
  · omega
  · have hval : i.1 ≠ q + n := by
      intro h
      apply hiNotZ
      ext
      exact h
    have hiBound : i.1 < q + n + 1 := i.2
    omega

theorem paddedEven_rank₁_z_eq_three (q n : ℕ) :
    paddedEvenRank₁ q n (paddedEvenZ q n) = 3 := by
  simp [paddedEvenRank₁, paddedEvenZ]
  omega

theorem paddedEven_fresh_not_chosen_after_of_card_ge
    {q n : ℕ} {X : Finset (Fin (q + n + 1))}
    (hzX : paddedEvenZ q n ∉ X) (hcard : q ≤ X.card) :
    paddedEvenZ q n ∉
      rankedTopQChoice q (paddedEvenRank₁ q n)
        (insert (paddedEvenZ q n) X) := by
  classical
  intro hzChosen
  let C : Finset (Fin (q + n + 1)) :=
    rankedTopQChoice q (paddedEvenRank₁ q n) (insert (paddedEvenZ q n) X)
  have hCcard : C.card = q := by
    dsimp [C]
    rw [rankedTopQChoice_qAcceptant (α := Fin (q + n + 1)) q (paddedEvenRank₁ q n)]
    have hqInsert : q ≤ (insert (paddedEvenZ q n) X).card := by
      exact hcard.trans (Finset.card_le_card (by
        intro y hy
        exact Finset.mem_insert_of_mem hy))
    exact Nat.min_eq_left hqInsert
  have hnotSubset : ¬ X ⊆ C := by
    intro hXsub
    have hinsertSub : insert (paddedEvenZ q n) X ⊆ C := by
      intro y hy
      rw [Finset.mem_insert] at hy
      rcases hy with rfl | hyX
      · exact hzChosen
      · exact hXsub hyX
    have hcard_insert_le : (insert (paddedEvenZ q n) X).card ≤ C.card :=
      Finset.card_le_card hinsertSub
    rw [hCcard, Finset.card_insert_of_notMem hzX] at hcard_insert_le
    omega
  have hy_exists : ∃ y, y ∈ X ∧ y ∉ C := by
    by_contra hnone
    apply hnotSubset
    intro y hyX
    by_contra hyC
    exact hnone ⟨y, hyX, hyC⟩
  rcases hy_exists with ⟨y, hyX, hyNotC⟩
  have hyInsert : y ∈ insert (paddedEvenZ q n) X :=
    Finset.mem_insert_of_mem hyX
  have hzy :=
    rankedTopQChoice_priority
      (α := Fin (q + n + 1)) q (paddedEvenRank₁ q n)
      (X := insert (paddedEvenZ q n) X)
      hzChosen hyInsert hyNotC
  have hzRank : paddedEvenRank₁ q n (paddedEvenZ q n) = 3 :=
    paddedEven_rank₁_z_eq_three q n
  have hyNotZ : y ≠ paddedEvenZ q n := by
    intro hyz
    subst y
    exact hzX hyX
  have hyRankLe : paddedEvenRank₁ q n y ≤ 2 :=
    paddedEven_old_applicant_rank₁_le_two hyNotZ
  have hrankLt : paddedEvenRank₁ q n (paddedEvenZ q n) <
      paddedEvenRank₁ q n y := by
    have hlex :
        (toLex (paddedEvenRank₁ q n (paddedEvenZ q n), paddedEvenZ q n) :
          Lex (ℕ × Fin (q + n + 1))) <
          toLex (paddedEvenRank₁ q n y, y) := by
      simpa using hzy
    rcases (Prod.Lex.toLex_lt_toLex.mp hlex) with hrank | heq
    · exact hrank
    · rcases heq with ⟨hrankEq, _hyLt⟩
      omega
  omega

theorem paddedEven_loss_subset_demoted
    {q n : ℕ} {X : Finset (Fin (q + n + 1))}
    (hzX : paddedEvenZ q n ∉ X) :
    rankedTopQChoice q (paddedEvenRank₀ q n) X \
      rankedTopQChoice q (paddedEvenRank₁ q n) (insert (paddedEvenZ q n) X) ⊆
        paddedEvenDemotedBlock q n := by
  classical
  intro y hyLoss
  rcases Finset.mem_sdiff.mp hyLoss with ⟨hyC0, hyNotC1⟩
  by_cases hsmall : X.card < q
  · have hXle : X.card ≤ q := le_of_lt hsmall
    have hInsertLe : (insert (paddedEvenZ q n) X).card ≤ q := by
      rw [Finset.card_insert_of_notMem hzX]
      omega
    have hC0 : rankedTopQChoice q (paddedEvenRank₀ q n) X = X :=
      QAcceptant.eq_of_card_le
        (rankedTopQChoice_feasible (α := Fin (q + n + 1)) q (paddedEvenRank₀ q n))
        (rankedTopQChoice_qAcceptant (α := Fin (q + n + 1)) q (paddedEvenRank₀ q n))
        hXle
    have hC1 : rankedTopQChoice q (paddedEvenRank₁ q n)
        (insert (paddedEvenZ q n) X) = insert (paddedEvenZ q n) X :=
      QAcceptant.eq_of_card_le
        (rankedTopQChoice_feasible (α := Fin (q + n + 1)) q (paddedEvenRank₁ q n))
        (rankedTopQChoice_qAcceptant (α := Fin (q + n + 1)) q (paddedEvenRank₁ q n))
        hInsertLe
    have hyX : y ∈ X := by simpa [hC0] using hyC0
    exact False.elim (hyNotC1 (by simpa [hC1] using Finset.mem_insert_of_mem hyX))
  · have hcard : q ≤ X.card := Nat.le_of_not_gt hsmall
    by_contra hyNotA
    let C0 : Finset (Fin (q + n + 1)) :=
      rankedTopQChoice q (paddedEvenRank₀ q n) X
    let C1 : Finset (Fin (q + n + 1)) :=
      rankedTopQChoice q (paddedEvenRank₁ q n) (insert (paddedEvenZ q n) X)
    have hyC0' : y ∈ C0 := hyC0
    have hyNotC1' : y ∉ C1 := hyNotC1
    have hC0card : C0.card = q := by
      dsimp [C0]
      rw [rankedTopQChoice_qAcceptant (α := Fin (q + n + 1)) q (paddedEvenRank₀ q n)]
      exact Nat.min_eq_left hcard
    have hC1card : C1.card = q := by
      dsimp [C1]
      rw [rankedTopQChoice_qAcceptant (α := Fin (q + n + 1)) q (paddedEvenRank₁ q n)]
      have hqInsert : q ≤ (insert (paddedEvenZ q n) X).card :=
        hcard.trans (Finset.card_le_card (by
          intro a ha
          exact Finset.mem_insert_of_mem ha))
      exact Nat.min_eq_left hqInsert
    have hcardEq : C1.card = C0.card := by rw [hC1card, hC0card]
    have hy_sdiff : y ∈ C0 \ C1 :=
      Finset.mem_sdiff.mpr ⟨hyC0', hyNotC1'⟩
    rcases exists_mem_sdiff_of_card_eq_of_mem_sdiff
        (A := C1) (B := C0) hcardEq hy_sdiff with ⟨v, hv_sdiff⟩
    rcases Finset.mem_sdiff.mp hv_sdiff with ⟨hvC1, hvNotC0⟩
    have hzNotC1 :
        paddedEvenZ q n ∉ C1 :=
      paddedEven_fresh_not_chosen_after_of_card_ge (q := q) (n := n) hzX hcard
    have hvNotZ : v ≠ paddedEvenZ q n := by
      intro hvz
      subst v
      exact hzNotC1 hvC1
    have hvOfferInsert : v ∈ insert (paddedEvenZ q n) X :=
      rankedTopQChoice_feasible (α := Fin (q + n + 1)) q (paddedEvenRank₁ q n)
        (insert (paddedEvenZ q n) X) hvC1
    have hvX : v ∈ X := by
      rw [Finset.mem_insert] at hvOfferInsert
      rcases hvOfferInsert with hvz | hvx
      · exact False.elim (hvNotZ hvz)
      · exact hvx
    have hyX : y ∈ X :=
      rankedTopQChoice_feasible (α := Fin (q + n + 1)) q (paddedEvenRank₀ q n)
        X hyC0'
    have h0 :=
      rankedTopQChoice_priority
        (α := Fin (q + n + 1)) q (paddedEvenRank₀ q n)
        (X := X) hyC0' hvX hvNotC0
    have h1 :=
      rankedTopQChoice_priority
        (α := Fin (q + n + 1)) q (paddedEvenRank₁ q n)
        (X := insert (paddedEvenZ q n) X) hvC1
        (Finset.mem_insert_of_mem hyX) hyNotC1'
    have h0lex :
        (toLex (paddedEvenRank₀ q n y, y) : Lex (ℕ × Fin (q + n + 1))) <
          toLex (paddedEvenRank₀ q n v, v) := by
      simpa using h0
    have h1lex :
        (toLex (paddedEvenRank₁ q n v, v) : Lex (ℕ × Fin (q + n + 1))) <
          toLex (paddedEvenRank₁ q n y, y) := by
      simpa using h1
    have h0cases := Prod.Lex.toLex_lt_toLex.mp h0lex
    have h1cases := Prod.Lex.toLex_lt_toLex.mp h1lex
    clear h0 h1
    have hyNotZ : y ≠ paddedEvenZ q n := by
      intro hyz
      subst y
      exact hzX hyX
    have hyBound : y.1 < q - n ∨ (q ≤ y.1 ∧ y.1 < q + n) := by
      have hyUniverse : y.1 < q + n + 1 := y.2
      have hyNotA' : ¬ (q - n ≤ y.1 ∧ y.1 < q) := by
        simpa [paddedEvenDemotedBlock] using hyNotA
      have hyNotZVal : y.1 ≠ q + n := by
        intro hval
        apply hyNotZ
        ext
        exact hval
      omega
    have hvNotZVal : v.1 ≠ q + n := by
      intro hval
      apply hvNotZ
      ext
      exact hval
    rcases hyBound with hyP | hyB
    · have hyR0 : paddedEvenRank₀ q n y = 0 := by
        unfold paddedEvenRank₀
        rw [if_pos (by omega)]
      have hyR1 : paddedEvenRank₁ q n y = 0 := by
        unfold paddedEvenRank₁
        rw [if_pos hyP]
      have hvR1zero_lt : paddedEvenRank₁ q n v = 0 ∧ v < y := by
        rw [hyR1] at h1cases
        rcases h1cases with hlt | heq
        · omega
        · exact heq
      have hvP : v.1 < q - n := by
        have hvR := hvR1zero_lt.1
        by_contra hvNotP
        have hvNotP' : ¬ v.1 < q - n := hvNotP
        unfold paddedEvenRank₁ at hvR
        rw [if_neg hvNotP'] at hvR
        by_cases hvB : q ≤ v.1 ∧ v.1 < q + n
        · rw [if_pos hvB] at hvR
          omega
        · rw [if_neg hvB] at hvR
          by_cases hvltq : v.1 < q
          · rw [if_pos hvltq] at hvR
            omega
          · rw [if_neg hvltq] at hvR
            omega
      have hvR0 : paddedEvenRank₀ q n v = 0 := by
        unfold paddedEvenRank₀
        rw [if_pos (by omega)]
      rw [hyR0, hvR0] at h0cases
      rcases h0cases with hlt | heq
      · omega
      · exact (not_lt_of_gt hvR1zero_lt.2) heq.2
    · have hyR0 : paddedEvenRank₀ q n y = 2 := by
        unfold paddedEvenRank₀
        rw [if_neg (by omega)]
      have hyR1 : paddedEvenRank₁ q n y = 1 := by
        have hyNotP : ¬ y.1 < q - n := by omega
        unfold paddedEvenRank₁
        rw [if_neg hyNotP]
        rw [if_pos hyB]
      have hvR0le : paddedEvenRank₀ q n v ≤ 2 := by
        unfold paddedEvenRank₀
        split_ifs with hvlt
        · omega
        · omega
      have hvR0eq_ylt : paddedEvenRank₀ q n v = 2 ∧ y < v := by
        rw [hyR0] at h0cases
        rcases h0cases with hlt | heq
        · have : 2 < paddedEvenRank₀ q n v := hlt
          omega
        · exact ⟨heq.1.symm, heq.2⟩
      have hvB : q ≤ v.1 ∧ v.1 < q + n := by
        have hvR := hvR0eq_ylt.1
        have hvge : q ≤ v.1 := by
          by_contra hvlt
          have hvlt' : v.1 < q := by omega
          unfold paddedEvenRank₀ at hvR
          rw [if_pos hvlt'] at hvR
          omega
        have hvBound : v.1 < q + n + 1 := v.2
        exact ⟨hvge, by omega⟩
      have hvR1 : paddedEvenRank₁ q n v = 1 := by
        have hvNotP : ¬ v.1 < q - n := by omega
        have hvPromoted : q ≤ v.1 ∧ v.1 < q + n := hvB
        unfold paddedEvenRank₁
        rw [if_neg hvNotP]
        rw [if_pos hvPromoted]
      rw [hyR1, hvR1] at h1cases
      rcases h1cases with hlt | heq
      · omega
      · exact (not_lt_of_gt heq.2) hvR0eq_ylt.2

theorem paddedEven_cross_loss_bound {q n : ℕ} (hnq : n ≤ q) :
    ∀ X x, x ∉ X → ¬ paddedEvenZ q n ∈ X →
      paddedEvenZ q n ∈ insert x X →
        (rankedTopQChoice q (paddedEvenRank₀ q n) X \
          rankedTopQChoice q (paddedEvenRank₁ q n) (insert x X)).card ≤ n := by
  intro X x hx hbefore hafter
  have hxz : x = paddedEvenZ q n := by
    rw [Finset.mem_insert] at hafter
    rcases hafter with hz_eq_x | hzX
    · exact hz_eq_x.symm
    · exact False.elim (hbefore hzX)
  subst x
  have hsubset := paddedEven_loss_subset_demoted (q := q) (n := n) (X := X) hbefore
  have hcardle := Finset.card_le_card hsubset
  rw [paddedEvenDemotedBlock_card (q := q) (n := n) hnq] at hcardle
  exact hcardle

theorem paddedEven_loss_card {q n : ℕ} (hnq : n ≤ q) :
    (rankedTopQChoice q (paddedEvenRank₀ q n) (paddedEvenBase q n) \
      rankedTopQChoice q (paddedEvenRank₁ q n)
        (insert (paddedEvenZ q n) (paddedEvenBase q n))).card = n := by
  classical
  rw [paddedEvenBefore_choice_eq, paddedEvenAfter_choice_eq hnq]
  let A : Finset (Fin (q + n + 1)) :=
    Finset.univ.filter (fun i => q - n ≤ i.1 ∧ i.1 < q)
  have hsdiff : paddedEvenBeforeChoiceSet q n \
      paddedEvenAfterChoiceSet q n = A := by
    ext i
    simp [paddedEvenBeforeChoiceSet, paddedEvenAfterChoiceSet, A]
    omega
  rw [hsdiff]
  let High : Finset (Fin (q + n + 1)) :=
    Finset.univ.filter (fun i => i.1 < q)
  let Low : Finset (Fin (q + n + 1)) :=
    Finset.univ.filter (fun i => i.1 < q - n)
  have hA_eq : A = High \ Low := by
    ext i
    simp [A, High, Low]
    omega
  have hLowSub : Low ⊆ High := by
    intro i hi
    simp [Low] at hi
    simp [High]
    omega
  rw [hA_eq, Finset.card_sdiff_of_subset hLowSub]
  have hHigh : High.card = q := by
    simp [High, Fin.card_filter_val_lt]
    omega
  have hLow : Low.card = q - n := by
    simp [Low, Fin.card_filter_val_lt]
    omega
  rw [hHigh, hLow]
  omega

theorem paddedEven_base_card_ge (q n : ℕ) :
    q ≤ (paddedEvenBase q n).card := by
  have hsub := paddedEvenBeforeChoiceSet_subset_base q n
  have hcard := Finset.card_le_card hsub
  rw [paddedEvenBeforeChoiceSet_card q n] at hcard
  exact hcard

theorem paddedEven_fresh_not_mem_base (q n : ℕ) :
    paddedEvenZ q n ∉ paddedEvenBase q n := by
  simp [paddedEvenBase]

theorem paddedEven_tightlyDUnstable {q n : ℕ} (hnpos : 0 < n) (hnq : n ≤ q) :
    TightlyDUnstable (2 * n) (paddedEvenChoice q n) := by
  classical
  exact rankedTriggerSwitchChoice_tightly_even
    (β := Fin (q + n + 1)) (q := q) (n := n) hnpos
    (τ := fun X : Finset (Fin (q + n + 1)) => paddedEvenZ q n ∈ X)
    (rank₀ := paddedEvenRank₀ q n) (rank₁ := paddedEvenRank₁ q n)
    (by
      intro X x hx hτX
      exact Finset.mem_insert_of_mem hτX)
    (by
      intro X x hx hbefore hafter
      exact paddedEven_cross_loss_bound (q := q) (n := n) hnq
        X x hx hbefore hafter)
    (X₀ := paddedEvenBase q n) (z := paddedEvenZ q n)
    (paddedEven_fresh_not_mem_base q n)
    (paddedEven_base_card_ge q n)
    (paddedEven_fresh_not_mem_base q n)
    (by simp)
    (paddedEven_fresh_not_chosen_after (q := q) (n := n) hnq)
    (paddedEven_loss_card (q := q) (n := n) hnq)

/-- The padded lower-even construction has an exact one-step distance `2*n` witness. -/
theorem paddedEven_choiceDistance_witness {q n : ℕ} (hnq : n ≤ q) :
    choiceDistance (paddedEvenChoice q n) (paddedEvenBase q n)
      (insert (paddedEvenZ q n) (paddedEvenBase q n)) = 2 * n := by
  classical
  rw [choiceDistance_insert_eq_if_mem
    (C := paddedEvenChoice q n) (q := q)
    (rankedTriggerSwitchChoice_feasible (q := q)
      (τ := fun X : Finset (Fin (q + n + 1)) => paddedEvenZ q n ∈ X)
      (rank₀ := paddedEvenRank₀ q n) (rank₁ := paddedEvenRank₁ q n))
    (rankedTriggerSwitchChoice_qAcceptant (q := q)
      (τ := fun X : Finset (Fin (q + n + 1)) => paddedEvenZ q n ∈ X)
      (rank₀ := paddedEvenRank₀ q n) (rank₁ := paddedEvenRank₁ q n))
    (paddedEven_base_card_ge q n)
    (paddedEven_fresh_not_mem_base q n)]
  have hnot :
      paddedEvenZ q n ∉
        paddedEvenChoice q n
          (insert (paddedEvenZ q n) (paddedEvenBase q n)) := by
    have hafter :
        paddedEvenZ q n ∈ insert (paddedEvenZ q n) (paddedEvenBase q n) := by
      simp
    simpa [paddedEvenChoice, rankedTriggerSwitchChoice, triggerSwitchChoice, hafter] using
      paddedEven_fresh_not_chosen_after (q := q) (n := n) hnq
  have hloss :
      (paddedEvenChoice q n (paddedEvenBase q n) \
        paddedEvenChoice q n
          (insert (paddedEvenZ q n) (paddedEvenBase q n))).card = n := by
    have hbefore :
        ¬ paddedEvenZ q n ∈ paddedEvenBase q n :=
      paddedEven_fresh_not_mem_base q n
    have hafter :
        paddedEvenZ q n ∈ insert (paddedEvenZ q n) (paddedEvenBase q n) := by
      simp
    simpa [paddedEvenChoice, rankedTriggerSwitchChoice, triggerSwitchChoice, hbefore, hafter]
      using paddedEven_loss_card (q := q) (n := n) hnq
  simp [hnot, hloss]

end PaddedEven

/-! ## Padded lower-odd witness construction -/

section PaddedOdd

/-- Fresh trigger applicant for the lower-odd padded construction. -/
noncomputable def paddedOddZ (q n : ℕ) : Fin (q + n + 1) :=
  ⟨q + n, by omega⟩

@[simp] theorem paddedOddZ_val (q n : ℕ) :
    (paddedOddZ q n).1 = q + n := rfl

/-- Witness pool: every applicant except the trigger. -/
noncomputable def paddedOddBase (q n : ℕ) : Finset (Fin (q + n + 1)) :=
  Finset.univ.erase (paddedOddZ q n)

/-- Before-trigger rank: the first q applicants are the top q. -/
def paddedOddRank₀ (q n : ℕ) (i : Fin (q + n + 1)) : ℕ :=
  if i.1 < q then 0 else 3

/--
After-trigger rank: padding remains first, the promoted old block plus the
fresh trigger move above the demoted block.
-/
noncomputable def paddedOddRank₁ (q n : ℕ) (i : Fin (q + n + 1)) : ℕ :=
  if i.1 < q - n then 0
  else if (q ≤ i.1 ∧ i.1 < q + n - 1) ∨ i = paddedOddZ q n then 1
  else if i.1 < q then 2
  else 3

/-- The q applicants chosen before the odd trigger fires. -/
def paddedOddBeforeChoiceSet (q n : ℕ) : Finset (Fin (q + n + 1)) :=
  Finset.univ.filter (fun i => i.1 < q)

/-- The q applicants chosen after the odd trigger fires. -/
noncomputable def paddedOddAfterChoiceSet (q n : ℕ) : Finset (Fin (q + n + 1)) :=
  Finset.univ.filter
    (fun i => i.1 < q - n ∨ (q ≤ i.1 ∧ i.1 < q + n - 1) ∨ i = paddedOddZ q n)

/-- Applicants that outrank the fresh trigger after the odd trigger fires. -/
noncomputable def paddedOddOutrankers (q n : ℕ) : Finset (Fin (q + n + 1)) :=
  Finset.univ.filter
    (fun i => i.1 < q - n ∨ (q ≤ i.1 ∧ i.1 < q + n - 1))

/-- The after-only promoted block, including the fresh trigger. -/
noncomputable def paddedOddPromotedTriggerBlock (q n : ℕ) :
    Finset (Fin (q + n + 1)) :=
  Finset.univ.filter
    (fun i => (q ≤ i.1 ∧ i.1 < q + n - 1) ∨ i = paddedOddZ q n)

/-- The padded lower-odd trigger-switch rule. -/
noncomputable def paddedOddChoice (q n : ℕ) : ChoiceRule (Fin (q + n + 1)) :=
  rankedTriggerSwitchChoice q
    (fun X : Finset (Fin (q + n + 1)) => paddedOddZ q n ∈ X)
    (paddedOddRank₀ q n)
    (paddedOddRank₁ q n)

theorem paddedOddBeforeChoiceSet_card (q n : ℕ) :
    (paddedOddBeforeChoiceSet q n).card = q := by
  unfold paddedOddBeforeChoiceSet
  rw [Fin.card_filter_val_lt]
  omega

theorem paddedOddAfterChoiceSet_card {q n : ℕ} (hnpos : 0 < n) (hnq : n ≤ q) :
    (paddedOddAfterChoiceSet q n).card = q := by
  classical
  let P : Finset (Fin (q + n + 1)) :=
    Finset.univ.filter (fun i => i.1 < q - n)
  let B : Finset (Fin (q + n + 1)) :=
    Finset.univ.filter (fun i => q ≤ i.1 ∧ i.1 < q + n - 1)
  let Z : Finset (Fin (q + n + 1)) := {paddedOddZ q n}
  have hfilter : paddedOddAfterChoiceSet q n = P ∪ B ∪ Z := by
    ext i
    simp [paddedOddAfterChoiceSet, P, B, Z]
    tauto
  rw [hfilter]
  have hdisjPB : Disjoint P B := by
    rw [Finset.disjoint_left]
    intro i hiP hiB
    simp [P] at hiP
    simp [B] at hiB
    omega
  have hz_not_PB : paddedOddZ q n ∉ P ∪ B := by
    simp [P, B, paddedOddZ]
    omega
  rw [Finset.card_union_of_disjoint]
  · rw [Finset.card_singleton]
    rw [Finset.card_union_of_disjoint hdisjPB]
    have hP : P.card = q - n := by
      simp [P, Fin.card_filter_val_lt]
      omega
    have hB : B.card = n - 1 := by
      let High : Finset (Fin (q + n + 1)) :=
        Finset.univ.filter (fun i => i.1 < q + n - 1)
      let Low : Finset (Fin (q + n + 1)) :=
        Finset.univ.filter (fun i => i.1 < q)
      have hB_eq : B = High \ Low := by
        ext i
        simp [B, High, Low]
        omega
      have hLowSub : Low ⊆ High := by
        intro i hi
        simp [Low] at hi
        simp [High]
        omega
      rw [hB_eq, Finset.card_sdiff_of_subset hLowSub]
      have hHigh : High.card = q + n - 1 := by
        simp [High, Fin.card_filter_val_lt]
        omega
      have hLow : Low.card = q := by
        simp [Low, Fin.card_filter_val_lt]
        omega
      rw [hHigh, hLow]
      omega
    omega
  · rw [Finset.disjoint_left]
    intro i hiPB hiZ
    simp [Z] at hiZ
    subst i
    exact hz_not_PB hiPB

theorem paddedOddOutrankers_card {q n : ℕ} (hnpos : 0 < n) (hnq : n ≤ q) :
    (paddedOddOutrankers q n).card = q - 1 := by
  classical
  unfold paddedOddOutrankers
  let P : Finset (Fin (q + n + 1)) :=
    Finset.univ.filter (fun i => i.1 < q - n)
  let B : Finset (Fin (q + n + 1)) :=
    Finset.univ.filter (fun i => q ≤ i.1 ∧ i.1 < q + n - 1)
  have hfilter : Finset.univ.filter
      (fun i : Fin (q + n + 1) =>
        i.1 < q - n ∨ (q ≤ i.1 ∧ i.1 < q + n - 1)) = P ∪ B := by
    ext i
    simp [P, B]
  rw [hfilter]
  have hdisj : Disjoint P B := by
    rw [Finset.disjoint_left]
    intro i hiP hiB
    simp [P] at hiP
    simp [B] at hiB
    omega
  rw [Finset.card_union_of_disjoint hdisj]
  have hP : P.card = q - n := by
    simp [P, Fin.card_filter_val_lt]
    omega
  have hB : B.card = n - 1 := by
    let High : Finset (Fin (q + n + 1)) :=
      Finset.univ.filter (fun i => i.1 < q + n - 1)
    let Low : Finset (Fin (q + n + 1)) :=
      Finset.univ.filter (fun i => i.1 < q)
    have hB_eq : B = High \ Low := by
      ext i
      simp [B, High, Low]
      omega
    have hLowSub : Low ⊆ High := by
      intro i hi
      simp [Low] at hi
      simp [High]
      omega
    rw [hB_eq, Finset.card_sdiff_of_subset hLowSub]
    have hHigh : High.card = q + n - 1 := by
      simp [High, Fin.card_filter_val_lt]
      omega
    have hLow : Low.card = q := by
      simp [Low, Fin.card_filter_val_lt]
      omega
    rw [hHigh, hLow]
    omega
  rw [hP, hB]
  omega

theorem paddedOddPromotedTriggerBlock_card {q n : ℕ} (hnpos : 0 < n) :
    (paddedOddPromotedTriggerBlock q n).card = n := by
  classical
  let B : Finset (Fin (q + n + 1)) :=
    Finset.univ.filter (fun i => q ≤ i.1 ∧ i.1 < q + n - 1)
  let Z : Finset (Fin (q + n + 1)) := {paddedOddZ q n}
  have hfilter : paddedOddPromotedTriggerBlock q n = B ∪ Z := by
    ext i
    simp [paddedOddPromotedTriggerBlock, B, Z]
    tauto
  rw [hfilter]
  have hz_not_B : paddedOddZ q n ∉ B := by
    simp [B, paddedOddZ]
  rw [Finset.card_union_of_disjoint]
  · rw [Finset.card_singleton]
    have hB : B.card = n - 1 := by
      let High : Finset (Fin (q + n + 1)) :=
        Finset.univ.filter (fun i => i.1 < q + n - 1)
      let Low : Finset (Fin (q + n + 1)) :=
        Finset.univ.filter (fun i => i.1 < q)
      have hB_eq : B = High \ Low := by
        ext i
        simp [B, High, Low]
        omega
      have hLowSub : Low ⊆ High := by
        intro i hi
        simp [Low] at hi
        simp [High]
        omega
      rw [hB_eq, Finset.card_sdiff_of_subset hLowSub]
      have hHigh : High.card = q + n - 1 := by
        simp [High, Fin.card_filter_val_lt]
        omega
      have hLow : Low.card = q := by
        simp [Low, Fin.card_filter_val_lt]
        omega
      rw [hHigh, hLow]
      omega
    omega
  · rw [Finset.disjoint_left]
    intro i hiB hiZ
    simp [Z] at hiZ
    subst i
    exact hz_not_B hiB

theorem paddedOddBeforeChoiceSet_subset_base (q n : ℕ) :
    paddedOddBeforeChoiceSet q n ⊆ paddedOddBase q n := by
  intro i hi
  simp [paddedOddBeforeChoiceSet] at hi
  simp [paddedOddBase, paddedOddZ]
  intro hiz
  have hval := congrArg Fin.val hiz
  simp at hval
  omega

theorem paddedOddBefore_choice_eq (q n : ℕ) :
    rankedTopQChoice q (paddedOddRank₀ q n) (paddedOddBase q n) =
      paddedOddBeforeChoiceSet q n := by
  classical
  unfold rankedTopQChoice
  letI : LinearOrder (Fin (q + n + 1)) := orderByRank (paddedOddRank₀ q n)
  exact linearTopQChoice_eq_of_card_of_forall_lt
    (α := Fin (q + n + 1))
    (paddedOddBeforeChoiceSet_subset_base q n)
    (paddedOddBeforeChoiceSet_card q n)
    (by
      intro s hs y _hyBase hyNot
      change (toLex (paddedOddRank₀ q n s, s) : Lex (ℕ × Fin (q + n + 1))) <
        toLex (paddedOddRank₀ q n y, y)
      apply Prod.Lex.left
      have hsRank : paddedOddRank₀ q n s = 0 := by
        simp [paddedOddRank₀, paddedOddBeforeChoiceSet] at hs ⊢
        exact hs
      have hyRank : paddedOddRank₀ q n y = 3 := by
        have hyge : ¬ y.1 < q := by
          intro hylt
          exact hyNot (by simp [paddedOddBeforeChoiceSet, hylt])
        simp [paddedOddRank₀, hyge]
      rw [hsRank, hyRank]
      omega)

theorem paddedOdd_insert_base_eq_univ (q n : ℕ) :
    insert (paddedOddZ q n) (paddedOddBase q n) =
      (Finset.univ : Finset (Fin (q + n + 1))) := by
  ext i
  by_cases hiz : i = paddedOddZ q n
  · subst i
    simp [paddedOddBase]
  · simp [paddedOddBase]

theorem paddedOddAfter_choice_eq {q n : ℕ} (hnpos : 0 < n) (hnq : n ≤ q) :
    rankedTopQChoice q (paddedOddRank₁ q n)
        (insert (paddedOddZ q n) (paddedOddBase q n)) =
      paddedOddAfterChoiceSet q n := by
  classical
  rw [paddedOdd_insert_base_eq_univ]
  unfold rankedTopQChoice
  letI : LinearOrder (Fin (q + n + 1)) := orderByRank (paddedOddRank₁ q n)
  exact linearTopQChoice_eq_of_card_of_forall_lt
    (α := Fin (q + n + 1))
    (by intro i _hi; simp)
    (paddedOddAfterChoiceSet_card hnpos hnq)
    (by
      intro s hs y _hyUniv hyNot
      change (toLex (paddedOddRank₁ q n s, s) : Lex (ℕ × Fin (q + n + 1))) <
        toLex (paddedOddRank₁ q n y, y)
      apply Prod.Lex.left
      have hsCond :
          s.1 < q - n ∨ (q ≤ s.1 ∧ s.1 < q + n - 1) ∨
            s = paddedOddZ q n := by
        simpa [paddedOddAfterChoiceSet] using hs
      have hyNotCond :
          ¬ (y.1 < q - n ∨ (q ≤ y.1 ∧ y.1 < q + n - 1) ∨
            y = paddedOddZ q n) := by
        intro hyCond
        exact hyNot (by simpa [paddedOddAfterChoiceSet] using hyCond)
      have hsRank : paddedOddRank₁ q n s ≤ 1 := by
        rcases hsCond with hsP | hsBZ
        · simp [paddedOddRank₁, hsP]
        · rcases hsBZ with hsB | hsZ
          · by_cases hsP : s.1 < q - n
            · simp [paddedOddRank₁, hsP]
            · simp [paddedOddRank₁, hsP, hsB]
          · by_cases hsP : s.1 < q - n
            · simp [paddedOddRank₁, hsP]
            · have hsPromoted :
                  (q ≤ s.1 ∧ s.1 < q + n - 1) ∨ s = paddedOddZ q n :=
                Or.inr hsZ
              simp [paddedOddRank₁, hsP, hsPromoted]
      have hyRank : 2 ≤ paddedOddRank₁ q n y := by
        have hyNotP : ¬ y.1 < q - n := by
          intro hyP
          exact hyNotCond (Or.inl hyP)
        have hyNotB : ¬ (q ≤ y.1 ∧ y.1 < q + n - 1) := by
          intro hyB
          exact hyNotCond (Or.inr (Or.inl hyB))
        have hyNotZ : ¬ y = paddedOddZ q n := by
          intro hyZ
          exact hyNotCond (Or.inr (Or.inr hyZ))
        have hyNotPromoted :
            ¬ ((q ≤ y.1 ∧ y.1 < q + n - 1) ∨ y = paddedOddZ q n) := by
          intro h
          rcases h with hyB | hyZ
          · exact hyNotB hyB
          · exact hyNotZ hyZ
        simp [paddedOddRank₁, hyNotP, hyNotPromoted]
        by_cases hyq : y.1 < q <;> simp [hyq]
      omega)

theorem paddedOdd_fresh_chosen_after {q n : ℕ} (hnpos : 0 < n) (hnq : n ≤ q) :
    paddedOddZ q n ∈
      rankedTopQChoice q (paddedOddRank₁ q n)
        (insert (paddedOddZ q n) (paddedOddBase q n)) := by
  rw [paddedOddAfter_choice_eq hnpos hnq]
  simp [paddedOddAfterChoiceSet]

theorem paddedOdd_rank₁_z_eq_one (q n : ℕ) :
    paddedOddRank₁ q n (paddedOddZ q n) = 1 := by
  classical
  unfold paddedOddRank₁
  rw [if_neg]
  · rw [if_pos]
    exact Or.inr rfl
  · simp [paddedOddZ]
    omega

theorem paddedOdd_lt_z_mem_outrankers {q n : ℕ}
    {y : Fin (q + n + 1)}
    (hylt :
      @LT.lt (Fin (q + n + 1)) (orderByRank (paddedOddRank₁ q n)).toLT
        y (paddedOddZ q n)) :
    y ∈ paddedOddOutrankers q n := by
  classical
  have hylt' :
      (toLex (paddedOddRank₁ q n y, y) : Lex (ℕ × Fin (q + n + 1))) <
        toLex (paddedOddRank₁ q n (paddedOddZ q n), paddedOddZ q n) :=
    hylt
  rw [paddedOdd_rank₁_z_eq_one] at hylt'
  have hcases := Prod.Lex.toLex_lt_toLex.mp hylt'
  rcases hcases with hrank | hpair
  · have hyrank0 : paddedOddRank₁ q n y = 0 := by omega
    have hyP : y.1 < q - n := by
      unfold paddedOddRank₁ at hyrank0
      by_cases hP : y.1 < q - n
      · exact hP
      · rw [if_neg hP] at hyrank0
        by_cases hPromoted :
            (q ≤ y.1 ∧ y.1 < q + n - 1) ∨ y = paddedOddZ q n
        · rw [if_pos hPromoted] at hyrank0
          omega
        · rw [if_neg hPromoted] at hyrank0
          by_cases hQ : y.1 < q
          · rw [if_pos hQ] at hyrank0
            omega
          · rw [if_neg hQ] at hyrank0
            omega
    simp [paddedOddOutrankers, hyP]
  · rcases hpair with ⟨hrankEq, hyTie⟩
    have hyrank1 : paddedOddRank₁ q n y = 1 := by
      simpa using hrankEq
    have hyNotZ : y ≠ paddedOddZ q n :=
      ne_of_lt hyTie
    have hyPromoted :
        (q ≤ y.1 ∧ y.1 < q + n - 1) ∨ y = paddedOddZ q n := by
      unfold paddedOddRank₁ at hyrank1
      by_cases hP : y.1 < q - n
      · rw [if_pos hP] at hyrank1
        omega
      · rw [if_neg hP] at hyrank1
        by_cases hPromoted :
            (q ≤ y.1 ∧ y.1 < q + n - 1) ∨ y = paddedOddZ q n
        · exact hPromoted
        · rw [if_neg hPromoted] at hyrank1
          by_cases hQ : y.1 < q
          · rw [if_pos hQ] at hyrank1
            omega
          · rw [if_neg hQ] at hyrank1
            omega
    rcases hyPromoted with hyB | hyZ
    · simp [paddedOddOutrankers, hyB]
    · exact False.elim (hyNotZ hyZ)

theorem paddedOdd_fresh_chosen_after_of_insert {q n : ℕ}
    (hnpos : 0 < n) (hnq : n ≤ q)
    {X : Finset (Fin (q + n + 1))} (hzX : paddedOddZ q n ∉ X) :
    paddedOddZ q n ∈
      rankedTopQChoice q (paddedOddRank₁ q n) (insert (paddedOddZ q n) X) := by
  classical
  let Y : Finset (Fin (q + n + 1)) := insert (paddedOddZ q n) X
  let C : Finset (Fin (q + n + 1)) :=
    rankedTopQChoice q (paddedOddRank₁ q n) Y
  have hzY : paddedOddZ q n ∈ Y := by
    simp [Y, hzX]
  by_contra hzNot
  have hCsubY : C ⊆ Y := by
    intro a ha
    exact rankedTopQChoice_feasible (α := Fin (q + n + 1))
      q (paddedOddRank₁ q n) Y ha
  have hCsubOut : C ⊆ paddedOddOutrankers q n := by
    intro y hyC
    have hylt :=
      rankedTopQChoice_priority (α := Fin (q + n + 1))
        q (paddedOddRank₁ q n) (X := Y) (x := y) (y := paddedOddZ q n)
        hyC hzY hzNot
    exact paddedOdd_lt_z_mem_outrankers (q := q) (n := n) hylt
  have hCcard : C.card = min q Y.card := by
    exact rankedTopQChoice_qAcceptant (α := Fin (q + n + 1))
      q (paddedOddRank₁ q n) Y
  by_cases hqY : q ≤ Y.card
  · have hCcardq : C.card = q := by
      rw [hCcard, Nat.min_eq_left hqY]
    have hleCard : C.card ≤ (paddedOddOutrankers q n).card :=
      Finset.card_le_card hCsubOut
    have hle : q ≤ q - 1 := by
      rw [hCcardq, paddedOddOutrankers_card hnpos hnq] at hleCard
      exact hleCard
    omega
  · have hCeqY : C = Y := by
      have hCcardY : C.card = Y.card := by
        rw [hCcard, Nat.min_eq_right (Nat.le_of_not_ge hqY)]
      exact Finset.eq_of_subset_of_card_le hCsubY (by rw [hCcardY])
    have hzC : paddedOddZ q n ∈ C := by
      rw [hCeqY]
      exact hzY
    exact hzNot (by simpa [C, Y] using hzC)

theorem paddedOdd_cross_chosen_of_false_to_true {q n : ℕ}
    (hnpos : 0 < n) (hnq : n ≤ q)
    {X : Finset (Fin (q + n + 1))} {x : Fin (q + n + 1)}
    (hxX : x ∉ X)
    (hbefore : ¬ paddedOddZ q n ∈ X)
    (hafter : paddedOddZ q n ∈ insert x X) :
    x ∈ rankedTopQChoice q (paddedOddRank₁ q n) (insert x X) := by
  classical
  have hxz : x = paddedOddZ q n := by
    rw [Finset.mem_insert] at hafter
    rcases hafter with hxz | hzX
    · exact hxz.symm
    · exact False.elim (hbefore hzX)
  subst x
  exact paddedOdd_fresh_chosen_after_of_insert (q := q) (n := n) hnpos hnq hbefore

theorem paddedOdd_loss_card {q n : ℕ} (hnpos : 0 < n) (hnq : n ≤ q) :
    (rankedTopQChoice q (paddedOddRank₀ q n) (paddedOddBase q n) \
      rankedTopQChoice q (paddedOddRank₁ q n)
        (insert (paddedOddZ q n) (paddedOddBase q n))).card = n := by
  classical
  rw [paddedOddBefore_choice_eq, paddedOddAfter_choice_eq hnpos hnq]
  let A : Finset (Fin (q + n + 1)) :=
    Finset.univ.filter (fun i => q - n ≤ i.1 ∧ i.1 < q)
  have hsdiff : paddedOddBeforeChoiceSet q n \
      paddedOddAfterChoiceSet q n = A := by
    ext i
    by_cases hiz : i = paddedOddZ q n
    · subst i
      simp [paddedOddBeforeChoiceSet, paddedOddAfterChoiceSet, A, paddedOddZ]
    · have hizVal : i.1 ≠ q + n := by
        intro hval
        apply hiz
        ext
        exact hval
      have hizLit : i ≠ (⟨q + n, by omega⟩ : Fin (q + n + 1)) := by
        intro h
        apply hiz
        ext
        exact congrArg Fin.val h
      simp [paddedOddBeforeChoiceSet, paddedOddAfterChoiceSet, A, paddedOddZ, hizLit]
      omega
  rw [hsdiff]
  let High : Finset (Fin (q + n + 1)) :=
    Finset.univ.filter (fun i => i.1 < q)
  let Low : Finset (Fin (q + n + 1)) :=
    Finset.univ.filter (fun i => i.1 < q - n)
  have hA_eq : A = High \ Low := by
    ext i
    simp [A, High, Low]
    omega
  have hLowSub : Low ⊆ High := by
    intro i hi
    simp [Low] at hi
    simp [High]
    omega
  rw [hA_eq, Finset.card_sdiff_of_subset hLowSub]
  have hHigh : High.card = q := by
    simp [High, Fin.card_filter_val_lt]
    omega
  have hLow : Low.card = q - n := by
    simp [Low, Fin.card_filter_val_lt]
    omega
  rw [hHigh, hLow]
  omega

theorem paddedOdd_rank₁_le_three {q n : ℕ} {i : Fin (q + n + 1)} :
    paddedOddRank₁ q n i ≤ 3 := by
  classical
  unfold paddedOddRank₁
  split_ifs with hP hB hA
  · omega
  · omega
  · omega
  · omega

theorem paddedOdd_gain_subset_promoted
    {q n : ℕ} (hnpos : 0 < n) {X : Finset (Fin (q + n + 1))}
    (hzX : paddedOddZ q n ∉ X) :
    rankedTopQChoice q (paddedOddRank₁ q n) (insert (paddedOddZ q n) X) \
      rankedTopQChoice q (paddedOddRank₀ q n) X ⊆
        paddedOddPromotedTriggerBlock q n := by
  classical
  intro y hyGain
  rcases Finset.mem_sdiff.mp hyGain with ⟨hyC1, hyNotC0⟩
  by_cases hsmall : X.card < q
  · have hXle : X.card ≤ q := le_of_lt hsmall
    have hC0 : rankedTopQChoice q (paddedOddRank₀ q n) X = X :=
      QAcceptant.eq_of_card_le
        (rankedTopQChoice_feasible (α := Fin (q + n + 1)) q (paddedOddRank₀ q n))
        (rankedTopQChoice_qAcceptant (α := Fin (q + n + 1)) q (paddedOddRank₀ q n))
        hXle
    have hyOfferInsert : y ∈ insert (paddedOddZ q n) X :=
      rankedTopQChoice_feasible (α := Fin (q + n + 1)) q (paddedOddRank₁ q n)
        (insert (paddedOddZ q n) X) hyC1
    rw [Finset.mem_insert] at hyOfferInsert
    rcases hyOfferInsert with hyz | hyX
    · subst y
      simp [paddedOddPromotedTriggerBlock]
    · exact False.elim (hyNotC0 (by simpa [hC0] using hyX))
  · have hcard : q ≤ X.card := Nat.le_of_not_gt hsmall
    by_contra hyNotBlock
    let C0 : Finset (Fin (q + n + 1)) :=
      rankedTopQChoice q (paddedOddRank₀ q n) X
    let C1 : Finset (Fin (q + n + 1)) :=
      rankedTopQChoice q (paddedOddRank₁ q n) (insert (paddedOddZ q n) X)
    have hyC1' : y ∈ C1 := hyC1
    have hyNotC0' : y ∉ C0 := hyNotC0
    have hC0card : C0.card = q := by
      dsimp [C0]
      rw [rankedTopQChoice_qAcceptant (α := Fin (q + n + 1)) q (paddedOddRank₀ q n)]
      exact Nat.min_eq_left hcard
    have hC1card : C1.card = q := by
      dsimp [C1]
      rw [rankedTopQChoice_qAcceptant (α := Fin (q + n + 1)) q (paddedOddRank₁ q n)]
      have hqInsert : q ≤ (insert (paddedOddZ q n) X).card :=
        hcard.trans (Finset.card_le_card (by
          intro a ha
          exact Finset.mem_insert_of_mem ha))
      exact Nat.min_eq_left hqInsert
    have hcardEq : C0.card = C1.card := by rw [hC0card, hC1card]
    have hy_sdiff : y ∈ C1 \ C0 :=
      Finset.mem_sdiff.mpr ⟨hyC1', hyNotC0'⟩
    rcases exists_mem_sdiff_of_card_eq_of_mem_sdiff
        (A := C0) (B := C1) hcardEq hy_sdiff with ⟨v, hv_sdiff⟩
    rcases Finset.mem_sdiff.mp hv_sdiff with ⟨hvC0, hvNotC1⟩
    have hyOfferInsert : y ∈ insert (paddedOddZ q n) X :=
      rankedTopQChoice_feasible (α := Fin (q + n + 1)) q (paddedOddRank₁ q n)
        (insert (paddedOddZ q n) X) hyC1'
    have hyNotZ : y ≠ paddedOddZ q n := by
      intro hyz
      apply hyNotBlock
      subst y
      simp [paddedOddPromotedTriggerBlock]
    have hyX : y ∈ X := by
      rw [Finset.mem_insert] at hyOfferInsert
      rcases hyOfferInsert with hyz | hyx
      · exact False.elim (hyNotZ hyz)
      · exact hyx
    have hvX : v ∈ X :=
      rankedTopQChoice_feasible (α := Fin (q + n + 1)) q (paddedOddRank₀ q n)
        X hvC0
    have hvInsert : v ∈ insert (paddedOddZ q n) X :=
      Finset.mem_insert_of_mem hvX
    have h0 :=
      rankedTopQChoice_priority
        (α := Fin (q + n + 1)) q (paddedOddRank₀ q n)
        (X := X) hvC0 hyX hyNotC0'
    have h1 :=
      rankedTopQChoice_priority
        (α := Fin (q + n + 1)) q (paddedOddRank₁ q n)
        (X := insert (paddedOddZ q n) X) hyC1' hvInsert hvNotC1
    have h0lex :
        (toLex (paddedOddRank₀ q n v, v) : Lex (ℕ × Fin (q + n + 1))) <
          toLex (paddedOddRank₀ q n y, y) := by
      simpa using h0
    have h1lex :
        (toLex (paddedOddRank₁ q n y, y) : Lex (ℕ × Fin (q + n + 1))) <
          toLex (paddedOddRank₁ q n v, v) := by
      simpa using h1
    have h0cases := Prod.Lex.toLex_lt_toLex.mp h0lex
    have h1cases := Prod.Lex.toLex_lt_toLex.mp h1lex
    clear h0 h1
    have hyNotBlock' :
        ¬ ((q ≤ y.1 ∧ y.1 < q + n - 1) ∨ y = paddedOddZ q n) := by
      simpa [paddedOddPromotedTriggerBlock] using hyNotBlock
    have hyBound : y.1 < q - n ∨
        (q - n ≤ y.1 ∧ y.1 < q) ∨
        (y.1 = q + n - 1) := by
      have hyUniverse : y.1 < q + n + 1 := y.2
      have hyNotZVal : y.1 ≠ q + n := by
        intro hval
        apply hyNotZ
        ext
        exact hval
      have hyNotPromoted : ¬ (q ≤ y.1 ∧ y.1 < q + n - 1) := by
        intro h
        exact hyNotBlock' (Or.inl h)
      omega
    rcases hyBound with hyP | hyRest
    · have hyR0 : paddedOddRank₀ q n y = 0 := by
        unfold paddedOddRank₀
        rw [if_pos (by omega)]
      have hyR1 : paddedOddRank₁ q n y = 0 := by
        unfold paddedOddRank₁
        rw [if_pos hyP]
      rw [hyR0] at h0cases
      rcases h0cases with hlt | heq
      · omega
      · have hvR1zero : paddedOddRank₁ q n v = 0 := by
          have hvlt : v.1 < q - n := by
            have hvltq : v.1 < q := by
              have hvR0eq0 : paddedOddRank₀ q n v = 0 := heq.1
              by_contra hvnot
              have hvnot' : ¬ v.1 < q := hvnot
              unfold paddedOddRank₀ at hvR0eq0
              rw [if_neg hvnot'] at hvR0eq0
              omega
            have hv_lt_y : v < y := heq.2
            have hv_val_lt_y : v.1 < y.1 := Fin.lt_def.mp hv_lt_y
            exact lt_of_lt_of_le hv_val_lt_y (le_of_lt hyP)
          unfold paddedOddRank₁
          rw [if_pos hvlt]
        rw [hyR1, hvR1zero] at h1cases
        rcases h1cases with hlt | heq1
        · omega
        · exact (not_lt_of_gt heq1.2) heq.2
    · rcases hyRest with hyA | hyTail
      · have hyR0 : paddedOddRank₀ q n y = 0 := by
          unfold paddedOddRank₀
          rw [if_pos (by omega)]
        have hyR1 : paddedOddRank₁ q n y = 2 := by
          have hyNotP : ¬ y.1 < q - n := by omega
          have hyNotPromoted :
              ¬ ((q ≤ y.1 ∧ y.1 < q + n - 1) ∨ y = paddedOddZ q n) :=
            hyNotBlock'
          unfold paddedOddRank₁
          rw [if_neg hyNotP]
          rw [if_neg hyNotPromoted]
          rw [if_pos (by omega)]
        rw [hyR0] at h0cases
        rcases h0cases with hlt | heq
        · omega
        · have hvltq : v.1 < q := by
            have hvR0eq0 : paddedOddRank₀ q n v = 0 := heq.1
            by_contra hvnot
            have hvnot' : ¬ v.1 < q := hvnot
            unfold paddedOddRank₀ at hvR0eq0
            rw [if_neg hvnot'] at hvR0eq0
            omega
          by_cases hvP : v.1 < q - n
          · have hvR1 : paddedOddRank₁ q n v = 0 := by
              unfold paddedOddRank₁
              rw [if_pos hvP]
            rw [hyR1, hvR1] at h1cases
            rcases h1cases with hlt | heq1
            · omega
            · omega
          · have hvA : q - n ≤ v.1 ∧ v.1 < q := by omega
            have hvNotPromoted :
                ¬ ((q ≤ v.1 ∧ v.1 < q + n - 1) ∨ v = paddedOddZ q n) := by
              intro h
              rcases h with hvProm | hvz
              · omega
              · subst v
                exact hzX hvX
            have hvR1 : paddedOddRank₁ q n v = 2 := by
              unfold paddedOddRank₁
              rw [if_neg hvP]
              rw [if_neg hvNotPromoted]
              rw [if_pos hvA.2]
            rw [hyR1, hvR1] at h1cases
            rcases h1cases with hlt | heq1
            · omega
            · exact (not_lt_of_gt heq1.2) heq.2
      · have hyR0 : paddedOddRank₀ q n y = 3 := by
          unfold paddedOddRank₀
          rw [if_neg (by omega)]
        have hyR1 : paddedOddRank₁ q n y = 3 := by
          have hyNotP : ¬ y.1 < q - n := by omega
          have hyNotPromoted :
              ¬ ((q ≤ y.1 ∧ y.1 < q + n - 1) ∨ y = paddedOddZ q n) :=
            hyNotBlock'
          have hyNotQ : ¬ y.1 < q := by omega
          unfold paddedOddRank₁
          rw [if_neg hyNotP]
          rw [if_neg hyNotPromoted]
          rw [if_neg hyNotQ]
        have hvNotZ : v ≠ paddedOddZ q n := by
          intro hvz
          subst v
          exact hzX hvX
        rw [hyR0] at h0cases
        rcases h0cases with hlt | heq
        · have hvltq : v.1 < q := by
            by_contra hvnot
            have hvnot' : ¬ v.1 < q := hvnot
            have hvR0 : paddedOddRank₀ q n v = 3 := by
              unfold paddedOddRank₀
              rw [if_neg hvnot']
            rw [hvR0] at hlt
            omega
          have hvR1le2 : paddedOddRank₁ q n v ≤ 2 := by
            by_cases hvP : v.1 < q - n
            · unfold paddedOddRank₁
              rw [if_pos hvP]
              omega
            · have hvNotPromoted :
                ¬ ((q ≤ v.1 ∧ v.1 < q + n - 1) ∨ v = paddedOddZ q n) := by
                intro h
                rcases h with hvProm | hvz
                · omega
                · exact hvNotZ hvz
              unfold paddedOddRank₁
              rw [if_neg hvP]
              rw [if_neg hvNotPromoted]
              rw [if_pos hvltq]
          rw [hyR1] at h1cases
          rcases h1cases with hlt1 | heq1
          · omega
          · omega
        · have hvR0eq_lt : paddedOddRank₀ q n v = 3 ∧ v < y := by
            exact ⟨heq.1, heq.2⟩
          have hvR1le : paddedOddRank₁ q n v ≤ 3 :=
            paddedOdd_rank₁_le_three
          rw [hyR1] at h1cases
          rcases h1cases with hlt | heq1
          · omega
          · exact (not_lt_of_gt heq1.2) hvR0eq_lt.2

theorem paddedOdd_cross_loss_bound {q n : ℕ} (hnpos : 0 < n) :
    ∀ X x, x ∉ X → ¬ paddedOddZ q n ∈ X →
      paddedOddZ q n ∈ insert x X →
        (rankedTopQChoice q (paddedOddRank₀ q n) X \
          rankedTopQChoice q (paddedOddRank₁ q n) (insert x X)).card ≤ n := by
  intro X x hx hbefore hafter
  have hxz : x = paddedOddZ q n := by
    rw [Finset.mem_insert] at hafter
    rcases hafter with hz_eq_x | hzX
    · exact hz_eq_x.symm
    · exact False.elim (hbefore hzX)
  subst x
  by_cases hsmall : X.card < q
  · have hXle : X.card ≤ q := le_of_lt hsmall
    have hInsertLe : (insert (paddedOddZ q n) X).card ≤ q := by
      rw [Finset.card_insert_of_notMem hbefore]
      omega
    have hC0 : rankedTopQChoice q (paddedOddRank₀ q n) X = X :=
      QAcceptant.eq_of_card_le
        (rankedTopQChoice_feasible (α := Fin (q + n + 1)) q (paddedOddRank₀ q n))
        (rankedTopQChoice_qAcceptant (α := Fin (q + n + 1)) q (paddedOddRank₀ q n))
        hXle
    have hC1 : rankedTopQChoice q (paddedOddRank₁ q n)
        (insert (paddedOddZ q n) X) = insert (paddedOddZ q n) X :=
      QAcceptant.eq_of_card_le
        (rankedTopQChoice_feasible (α := Fin (q + n + 1)) q (paddedOddRank₁ q n))
        (rankedTopQChoice_qAcceptant (α := Fin (q + n + 1)) q (paddedOddRank₁ q n))
        hInsertLe
    rw [hC0, hC1]
    have hsdiff : X \ insert (paddedOddZ q n) X = (∅ : Finset (Fin (q + n + 1))) := by
      rw [Finset.sdiff_eq_empty_iff_subset]
      intro y hy
      exact Finset.mem_insert_of_mem hy
    rw [hsdiff]
    simp
  · have hcard : q ≤ X.card := Nat.le_of_not_gt hsmall
    let C0 : Finset (Fin (q + n + 1)) :=
      rankedTopQChoice q (paddedOddRank₀ q n) X
    let C1 : Finset (Fin (q + n + 1)) :=
      rankedTopQChoice q (paddedOddRank₁ q n) (insert (paddedOddZ q n) X)
    have hC0card : C0.card = q := by
      dsimp [C0]
      rw [rankedTopQChoice_qAcceptant (α := Fin (q + n + 1)) q (paddedOddRank₀ q n)]
      exact Nat.min_eq_left hcard
    have hC1card : C1.card = q := by
      dsimp [C1]
      rw [rankedTopQChoice_qAcceptant (α := Fin (q + n + 1)) q (paddedOddRank₁ q n)]
      have hqInsert : q ≤ (insert (paddedOddZ q n) X).card :=
        hcard.trans (Finset.card_le_card (by
          intro a ha
          exact Finset.mem_insert_of_mem ha))
      exact Nat.min_eq_left hqInsert
    have hcardEq : C0.card = C1.card := by rw [hC0card, hC1card]
    have hgainSubset :
        C1 \ C0 ⊆ paddedOddPromotedTriggerBlock q n :=
      paddedOdd_gain_subset_promoted (q := q) (n := n) hnpos hbefore
    have hgainCard : (C1 \ C0).card ≤ n := by
      have hle := Finset.card_le_card hgainSubset
      rw [paddedOddPromotedTriggerBlock_card (q := q) (n := n) hnpos] at hle
      exact hle
    have hlossEq : (C0 \ C1).card = (C1 \ C0).card := by
      exact Finset.card_sdiff_comm hcardEq
    dsimp [C0, C1] at hgainCard hlossEq
    rw [hlossEq]
    exact hgainCard

theorem paddedOdd_base_card_ge (q n : ℕ) :
    q ≤ (paddedOddBase q n).card := by
  have hsub := paddedOddBeforeChoiceSet_subset_base q n
  have hcard := Finset.card_le_card hsub
  rw [paddedOddBeforeChoiceSet_card q n] at hcard
  exact hcard

theorem paddedOdd_fresh_not_mem_base (q n : ℕ) :
    paddedOddZ q n ∉ paddedOddBase q n := by
  simp [paddedOddBase]

theorem paddedOdd_tightlyDUnstable {q n : ℕ} (hnpos : 0 < n) (hnq : n ≤ q) :
    TightlyDUnstable (2 * n - 1) (paddedOddChoice q n) := by
  classical
  exact rankedTriggerSwitchChoice_tightly_odd
    (β := Fin (q + n + 1)) (q := q) (n := n) hnpos
    (τ := fun X : Finset (Fin (q + n + 1)) => paddedOddZ q n ∈ X)
    (rank₀ := paddedOddRank₀ q n) (rank₁ := paddedOddRank₁ q n)
    (by
      intro X x hx hτX
      exact Finset.mem_insert_of_mem hτX)
    (by
      intro X x hx hbefore hafter
      exact paddedOdd_cross_loss_bound (q := q) (n := n) hnpos
        X x hx hbefore hafter)
    (by
      intro X x hx hbefore hafter
      exact paddedOdd_cross_chosen_of_false_to_true
        (q := q) (n := n) hnpos hnq hx hbefore hafter)
    (X₀ := paddedOddBase q n) (z := paddedOddZ q n)
    (paddedOdd_fresh_not_mem_base q n)
    (paddedOdd_base_card_ge q n)
    (paddedOdd_fresh_not_mem_base q n)
    (by simp)
    (paddedOdd_fresh_chosen_after (q := q) (n := n) hnpos hnq)
    (paddedOdd_loss_card (q := q) (n := n) hnpos hnq)

/-- The padded lower-odd construction has an exact one-step distance `2*n - 1` witness. -/
theorem paddedOdd_choiceDistance_witness {q n : ℕ} (hnpos : 0 < n) (hnq : n ≤ q) :
    choiceDistance (paddedOddChoice q n) (paddedOddBase q n)
      (insert (paddedOddZ q n) (paddedOddBase q n)) = 2 * n - 1 := by
  classical
  rw [choiceDistance_insert_eq_if_mem
    (C := paddedOddChoice q n) (q := q)
    (rankedTriggerSwitchChoice_feasible (q := q)
      (τ := fun X : Finset (Fin (q + n + 1)) => paddedOddZ q n ∈ X)
      (rank₀ := paddedOddRank₀ q n) (rank₁ := paddedOddRank₁ q n))
    (rankedTriggerSwitchChoice_qAcceptant (q := q)
      (τ := fun X : Finset (Fin (q + n + 1)) => paddedOddZ q n ∈ X)
      (rank₀ := paddedOddRank₀ q n) (rank₁ := paddedOddRank₁ q n))
    (paddedOdd_base_card_ge q n)
    (paddedOdd_fresh_not_mem_base q n)]
  have hchosen :
      paddedOddZ q n ∈
        paddedOddChoice q n
          (insert (paddedOddZ q n) (paddedOddBase q n)) := by
    have hafter :
        paddedOddZ q n ∈ insert (paddedOddZ q n) (paddedOddBase q n) := by
      simp
    simpa [paddedOddChoice, rankedTriggerSwitchChoice, triggerSwitchChoice, hafter] using
      paddedOdd_fresh_chosen_after (q := q) (n := n) hnpos hnq
  have hloss :
      (paddedOddChoice q n (paddedOddBase q n) \
        paddedOddChoice q n
          (insert (paddedOddZ q n) (paddedOddBase q n))).card = n := by
    have hbefore :
        ¬ paddedOddZ q n ∈ paddedOddBase q n :=
      paddedOdd_fresh_not_mem_base q n
    have hafter :
        paddedOddZ q n ∈ insert (paddedOddZ q n) (paddedOddBase q n) := by
      simp
    simpa [paddedOddChoice, rankedTriggerSwitchChoice, triggerSwitchChoice, hbefore, hafter]
      using paddedOdd_loss_card (q := q) (n := n) hnpos hnq
  simp [hchosen, hloss]

end PaddedOdd

/-! ## A generic tight `2q` switch construction -/

section SwitchEven

variable {β : Type*} [DecidableEq β]

/--
A q-acceptant switch rule.  Small pools accept everyone.  Large pools
containing the trigger `z` and the block `B` choose `B`; otherwise large pools
containing `A` choose `A`; all other large pools choose an arbitrary q-subset.
-/
noncomputable def switchEvenChoice (q : ℕ)
    (A B : Finset β) (z : β) : ChoiceRule β :=
  fun X =>
    if hsmall : X.card ≤ q then
      X
    else if z ∈ X ∧ B ⊆ X then
      B
    else if A ⊆ X then
      A
    else
      Classical.choose
        (Finset.exists_subset_card_eq
          (show q ≤ X.card from le_of_lt (Nat.lt_of_not_ge hsmall)))

theorem switchEvenChoice_feasible
    {q : ℕ} {A B : Finset β} {z : β}
    (_hAcard : A.card = q) (_hBcard : B.card = q) :
    Feasible (switchEvenChoice q A B z) := by
  classical
  intro X x hx
  unfold switchEvenChoice at hx
  split_ifs at hx with hsmall htrigger hAsub
  · exact hx
  · exact htrigger.2 hx
  · exact hAsub hx
  · exact
      (Classical.choose_spec
        (Finset.exists_subset_card_eq
          (show q ≤ X.card from le_of_lt (Nat.lt_of_not_ge hsmall)))).1 hx

theorem switchEvenChoice_qAcceptant
    {q : ℕ} {A B : Finset β} {z : β}
    (hAcard : A.card = q) (hBcard : B.card = q) :
    QAcceptant q (switchEvenChoice q A B z) := by
  classical
  intro X
  unfold switchEvenChoice
  split_ifs with hsmall htrigger hAsub
  · simp [Nat.min_eq_right hsmall]
  · rw [hBcard]
    exact (Nat.min_eq_left (le_of_lt (Nat.lt_of_not_ge hsmall))).symm
  · rw [hAcard]
    exact (Nat.min_eq_left (le_of_lt (Nat.lt_of_not_ge hsmall))).symm
  · have hchoose :=
      (Classical.choose_spec
        (Finset.exists_subset_card_eq
          (show q ≤ X.card from le_of_lt (Nat.lt_of_not_ge hsmall)))).2
    rw [hchoose]
    exact (Nat.min_eq_left (le_of_lt (Nat.lt_of_not_ge hsmall))).symm

theorem switchEvenChoice_base_eq
    {q : ℕ} {A B : Finset β} {z : β}
    (hqpos : 0 < q) (hAcard : A.card = q) (hBcard : B.card = q)
    (hdisj : Disjoint A B) (hzA : z ∉ A) (hzB : z ∉ B) :
    switchEvenChoice q A B z (A ∪ B) = A := by
  classical
  unfold switchEvenChoice
  have hcard_base : (A ∪ B).card = q + q := by
    rw [Finset.card_union_of_disjoint hdisj]
    omega
  have hnot_small : ¬ (A ∪ B).card ≤ q := by
    rw [hcard_base]
    omega
  have hnot_trigger : ¬ (z ∈ A ∪ B ∧ B ⊆ A ∪ B) := by
    intro h
    rcases Finset.mem_union.mp h.1 with hzA' | hzB'
    · exact hzA hzA'
    · exact hzB hzB'
  have hAsub : A ⊆ A ∪ B := by
    intro x hx
    exact Finset.mem_union_left B hx
  rw [dif_neg hnot_small]
  rw [if_neg hnot_trigger]
  rw [if_pos hAsub]

theorem switchEvenChoice_insert_base_eq
    {q : ℕ} {A B : Finset β} {z : β}
    (hqpos : 0 < q) (hAcard : A.card = q) (hBcard : B.card = q)
    (hdisj : Disjoint A B) (hzA : z ∉ A) (hzB : z ∉ B) :
    switchEvenChoice q A B z (insert z (A ∪ B)) = B := by
  classical
  unfold switchEvenChoice
  have hcard_base : (A ∪ B).card = q + q := by
    rw [Finset.card_union_of_disjoint hdisj]
    omega
  have hzbase : z ∉ A ∪ B := by
    intro hz
    rcases Finset.mem_union.mp hz with hzA' | hzB'
    · exact hzA hzA'
    · exact hzB hzB'
  have hcard_insert : (insert z (A ∪ B)).card = q + q + 1 := by
    rw [Finset.card_insert_of_notMem hzbase, hcard_base]
  have hnot_small : ¬ (insert z (A ∪ B)).card ≤ q := by
    rw [hcard_insert]
    omega
  have htrigger : z ∈ insert z (A ∪ B) ∧ B ⊆ insert z (A ∪ B) := by
    constructor
    · exact Finset.mem_insert_self z (A ∪ B)
    · intro x hx
      exact Finset.mem_insert_of_mem (Finset.mem_union_right A hx)
  simp [hnot_small, htrigger]

theorem switchEvenChoice_loss_card_witness
    {q : ℕ} {A B : Finset β} {z : β}
    (hqpos : 0 < q) (hAcard : A.card = q) (hBcard : B.card = q)
    (hdisj : Disjoint A B) (hzA : z ∉ A) (hzB : z ∉ B) :
    (switchEvenChoice q A B z (A ∪ B) \
      switchEvenChoice q A B z (insert z (A ∪ B))).card = q := by
  rw [switchEvenChoice_base_eq hqpos hAcard hBcard hdisj hzA hzB,
    switchEvenChoice_insert_base_eq hqpos hAcard hBcard hdisj hzA hzB]
  have hsubset_empty : A ∩ B = ∅ := by
    exact Finset.disjoint_iff_inter_eq_empty.mp hdisj
  have hsdiff : A \ B = A := by
    apply Finset.Subset.antisymm
    · intro x hx
      exact (Finset.mem_sdiff.mp hx).1
    · intro x hxA
      exact Finset.mem_sdiff.mpr
        ⟨hxA, by
          intro hxB
          have hxInter : x ∈ A ∩ B := Finset.mem_inter.mpr ⟨hxA, hxB⟩
          simp [hsubset_empty] at hxInter⟩
  simp [hsdiff, hAcard]

theorem switchEvenChoice_choiceDistance_witness
    {q : ℕ} {A B : Finset β} {z : β}
    (hqpos : 0 < q) (hAcard : A.card = q) (hBcard : B.card = q)
    (hdisj : Disjoint A B) (hzA : z ∉ A) (hzB : z ∉ B) :
    choiceDistance (switchEvenChoice q A B z) (A ∪ B)
      (insert z (A ∪ B)) = 2 * q := by
  have hfeasible : Feasible (switchEvenChoice q A B z) :=
    switchEvenChoice_feasible hAcard hBcard
  have haccept : QAcceptant q (switchEvenChoice q A B z) :=
    switchEvenChoice_qAcceptant hAcard hBcard
  have hzbase : z ∉ A ∪ B := by
    intro hz
    rcases Finset.mem_union.mp hz with hzA' | hzB'
    · exact hzA hzA'
    · exact hzB hzB'
  have hcard_base : q ≤ (A ∪ B).card := by
    rw [Finset.card_union_of_disjoint hdisj, hAcard, hBcard]
    omega
  have hz_not_chosen :
      z ∉ switchEvenChoice q A B z (insert z (A ∪ B)) := by
    rw [switchEvenChoice_insert_base_eq hqpos hAcard hBcard hdisj hzA hzB]
    exact hzB
  rw [choiceDistance_insert_eq_if_mem
    (C := switchEvenChoice q A B z) (q := q)
    hfeasible haccept hcard_base hzbase]
  simp [hz_not_chosen,
    switchEvenChoice_loss_card_witness hqpos hAcard hBcard hdisj hzA hzB]

theorem switchEvenChoice_tightlyDUnstable_two_mul
    {q : ℕ} {A B : Finset β} {z : β}
    (hqpos : 0 < q) (hAcard : A.card = q) (hBcard : B.card = q)
    (hdisj : Disjoint A B) (hzA : z ∉ A) (hzB : z ∉ B) :
    TightlyDUnstable (2 * q) (switchEvenChoice q A B z) := by
  constructor
  · exact dUnstable_two_mul_of_qAcceptant
      (switchEvenChoice_qAcceptant hAcard hBcard)
  · intro k hk hunstable
    have hdist := hunstable (A ∪ B) z (by
      intro hz
      rcases Finset.mem_union.mp hz with hzA' | hzB'
      · exact hzA hzA'
      · exact hzB hzB')
    have hle : 2 * q ≤ k := by
      simpa [switchEvenChoice_choiceDistance_witness
        hqpos hAcard hBcard hdisj hzA hzB] using hdist
    omega

end SwitchEven

/-! ## A generic tight odd switch construction -/

section SwitchOdd

variable {β : Type*} [DecidableEq β]

/--
A complementary-group odd-distance switch.  The rule normally follows a
fallback q-acceptant rule `F`, but if the trigger `z` and block `B` are both
present, it chooses the complementary group `insert z B`.
-/
noncomputable def switchOddChoice (_q : ℕ)
    (B : Finset β) (z : β) (F : ChoiceRule β) : ChoiceRule β :=
  fun X =>
    if z ∈ X ∧ B ⊆ X then
      insert z B
    else
      F X

set_option linter.unusedVariables false in
theorem switchOddChoice_feasible
    {q : ℕ} {B : Finset β} {z : β} {F : ChoiceRule β}
    (hFfeasible : Feasible F) :
    Feasible (switchOddChoice q B z F) := by
  classical
  intro X x hx
  unfold switchOddChoice at hx
  split_ifs at hx with htrigger
  · rcases Finset.mem_insert.mp hx with rfl | hxB
    · exact htrigger.1
    · exact htrigger.2 hxB
  · exact hFfeasible X hx

theorem switchOddChoice_qAcceptant
    {q : ℕ} {B : Finset β} {z : β} {F : ChoiceRule β}
    (htrigger_card : (insert z B).card = q)
    (hFaccept : QAcceptant q F) :
    QAcceptant q (switchOddChoice q B z F) := by
  classical
  intro X
  unfold switchOddChoice
  split_ifs with htrigger
  · rw [htrigger_card]
    have hsubset : insert z B ⊆ X := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hxB
      · exact htrigger.1
      · exact htrigger.2 hxB
    exact (Nat.min_eq_left (by
      rw [← htrigger_card]
      exact Finset.card_le_card hsubset)).symm
  · exact hFaccept X

/--
For the odd switch, any one-step insertion that does not choose the fresh
applicant leaves the choice unchanged.
-/
theorem switchOddChoice_insert_eq_self_of_fresh_not_chosen
    {q : ℕ} {B : Finset β} {z : β} {F : ChoiceRule β}
    (hFfeasible : Feasible F) (hFconsistent : Consistent F)
    {X : Finset β} {x : β} (_hxX : x ∉ X)
    (hxNotChosen : x ∉ switchOddChoice q B z F (insert x X)) :
    switchOddChoice q B z F (insert x X) =
      switchOddChoice q B z F X := by
  classical
  by_cases hafter : z ∈ insert x X ∧ B ⊆ insert x X
  · have hxNotTrigger : x ∉ insert z B := by
      rw [switchOddChoice, if_pos hafter] at hxNotChosen
      exact hxNotChosen
    have hzX : z ∈ X := by
      rcases Finset.mem_insert.mp hafter.1 with hzx | hzX
      · subst z
        exact False.elim (hxNotTrigger (Finset.mem_insert_self x B))
      · exact hzX
    have hBsubX : B ⊆ X := by
      intro b hb
      have hbInsert : b ∈ insert x X := hafter.2 hb
      rcases Finset.mem_insert.mp hbInsert with hbx | hbX
      · subst b
        exact False.elim
          (hxNotTrigger (Finset.mem_insert_of_mem hb))
      · exact hbX
    have hbefore : z ∈ X ∧ B ⊆ X := ⟨hzX, hBsubX⟩
    rw [switchOddChoice, if_pos hafter, switchOddChoice, if_pos hbefore]
  · have hbefore : ¬ (z ∈ X ∧ B ⊆ X) := by
      intro h
      exact hafter
        ⟨Finset.mem_insert_of_mem h.1,
          by
            intro b hb
            exact Finset.mem_insert_of_mem (h.2 hb)⟩
    have hxNotF : x ∉ F (insert x X) := by
      rw [switchOddChoice, if_neg hafter] at hxNotChosen
      exact hxNotChosen
    have hsameF : F (insert x X) = F X :=
      choice_insert_eq_self_of_consistent_of_fresh_not_chosen
        hFfeasible hFconsistent hxNotF
    rw [switchOddChoice, if_neg hafter, switchOddChoice, if_neg hbefore, hsameF]

theorem switchOddChoice_dUnstable_two_mul_sub_one
    {q : ℕ} {B : Finset β} {z : β} {F : ChoiceRule β}
    (htrigger_card : (insert z B).card = q)
    (hFfeasible : Feasible F) (hFaccept : QAcceptant q F)
    (hFconsistent : Consistent F) :
    DUnstable (2 * q - 1) (switchOddChoice q B z F) := by
  exact
    dUnstable_two_mul_sub_one_of_feasible_of_qAcceptant_of_not_chosen_eq_self
      (C := switchOddChoice q B z F)
      (switchOddChoice_feasible (q := q) hFfeasible)
      (switchOddChoice_qAcceptant htrigger_card hFaccept)
      (by
        intro X x hxX hxNot
        exact switchOddChoice_insert_eq_self_of_fresh_not_chosen
          (q := q) hFfeasible hFconsistent hxX hxNot)

theorem switchOddChoice_base_eq
    {q : ℕ} {A B : Finset β} {z : β} {F : ChoiceRule β}
    (hFbase : F (A ∪ B) = A) (hzA : z ∉ A) (hzB : z ∉ B) :
    switchOddChoice q B z F (A ∪ B) = A := by
  classical
  have hnot : ¬ (z ∈ A ∪ B ∧ B ⊆ A ∪ B) := by
    intro h
    rcases Finset.mem_union.mp h.1 with hzA' | hzB'
    · exact hzA hzA'
    · exact hzB hzB'
  rw [switchOddChoice, if_neg hnot, hFbase]

theorem switchOddChoice_insert_base_eq
    {q : ℕ} {A B : Finset β} {z : β} {F : ChoiceRule β} :
    switchOddChoice q B z F (insert z (A ∪ B)) = insert z B := by
  classical
  have htrigger : z ∈ insert z (A ∪ B) ∧ B ⊆ insert z (A ∪ B) := by
    constructor
    · exact Finset.mem_insert_self z (A ∪ B)
    · intro b hb
      exact Finset.mem_insert_of_mem (Finset.mem_union_right A hb)
  simp [switchOddChoice, htrigger]

theorem switchOddChoice_choiceDistance_witness
    {q : ℕ} {A B : Finset β} {z : β} {F : ChoiceRule β}
    (hAcard : A.card = q)
    (htrigger_card : (insert z B).card = q)
    (hdisj : Disjoint A (insert z B))
    (hFfeasible : Feasible F) (hFaccept : QAcceptant q F)
    (hFbase : F (A ∪ B) = A) (hzA : z ∉ A) (hzB : z ∉ B) :
    choiceDistance (switchOddChoice q B z F) (A ∪ B)
      (insert z (A ∪ B)) = 2 * q - 1 := by
  classical
  have hfeasible : Feasible (switchOddChoice q B z F) :=
    switchOddChoice_feasible (q := q) hFfeasible
  have haccept : QAcceptant q (switchOddChoice q B z F) :=
    switchOddChoice_qAcceptant htrigger_card hFaccept
  have hzbase : z ∉ A ∪ B := by
    intro hz
    rcases Finset.mem_union.mp hz with hzA' | hzB'
    · exact hzA hzA'
    · exact hzB hzB'
  have hcard_base : q ≤ (A ∪ B).card := by
    rw [← hAcard]
    exact Finset.card_le_card (by
      intro a ha
      exact Finset.mem_union_left B ha)
  have hzChosen :
      z ∈ switchOddChoice q B z F (insert z (A ∪ B)) := by
    rw [switchOddChoice_insert_base_eq]
    exact Finset.mem_insert_self z B
  rw [choiceDistance_insert_eq_if_mem
    (C := switchOddChoice q B z F) (q := q)
    hfeasible haccept hcard_base hzbase]
  simp [switchOddChoice_base_eq hFbase hzA hzB,
    switchOddChoice_insert_base_eq]
  have hsdiff : A \ insert z B = A := by
    apply Finset.Subset.antisymm
    · intro a ha
      exact (Finset.mem_sdiff.mp ha).1
    · intro a haA
      exact Finset.mem_sdiff.mpr
        ⟨haA, by
          intro haTrigger
          exact Finset.disjoint_left.mp hdisj haA haTrigger⟩
  simp [hsdiff, hAcard]

theorem switchOddChoice_tightlyDUnstable_two_mul_sub_one
    {q : ℕ} {A B : Finset β} {z : β} {F : ChoiceRule β}
    (hAcard : A.card = q)
    (htrigger_card : (insert z B).card = q)
    (hdisj : Disjoint A (insert z B))
    (hFfeasible : Feasible F) (hFaccept : QAcceptant q F)
    (hFconsistent : Consistent F)
    (hFbase : F (A ∪ B) = A) (hzA : z ∉ A) (hzB : z ∉ B) :
    TightlyDUnstable (2 * q - 1) (switchOddChoice q B z F) := by
  constructor
  · exact switchOddChoice_dUnstable_two_mul_sub_one
      htrigger_card hFfeasible hFaccept hFconsistent
  · intro k hk hunstable
    have hle : 2 * q - 1 ≤ k := by
      have hdist := hunstable (A ∪ B) z (by
        intro hz
        rcases Finset.mem_union.mp hz with hzA' | hzB'
        · exact hzA hzA'
        · exact hzB hzB')
      simpa [switchOddChoice_choiceDistance_witness
        hAcard htrigger_card hdisj hFfeasible hFaccept hFbase hzA hzB]
        using hdist
    omega

end SwitchOdd

/-! ## A tight 1-instability example -/

/-- A `q = 1` priority rule on `Fin 2`: applicant `0` beats applicant `1`. -/
def tightOneChoice : ChoiceRule (Fin 2) :=
  fun X =>
    if (0 : Fin 2) ∈ X then
      {(0 : Fin 2)}
    else
      X

/-- The singleton pool used to witness nonzero one-step instability. -/
def tightOneBase : Finset (Fin 2) :=
  {(1 : Fin 2)}

/-- The fresh high-priority applicant for the tight-1 witness. -/
def tightOneFresh : Fin 2 :=
  (0 : Fin 2)

theorem tightOne_feasible :
    Feasible tightOneChoice := by
  intro X
  fin_cases X <;> decide

theorem tightOne_qAcceptant :
    QAcceptant 1 tightOneChoice := by
  intro X
  fin_cases X <;> decide

theorem tightOne_dUnstable_one :
    DUnstable 1 tightOneChoice := by
  intro X x _hx
  fin_cases X <;> fin_cases x <;> decide

theorem tightOne_fresh_not_mem_base :
    tightOneFresh ∉ tightOneBase := by
  decide

theorem tightOne_choiceDistance_witness :
    choiceDistance tightOneChoice tightOneBase
      (insert tightOneFresh tightOneBase) = 1 := by
  decide

theorem tightOne_tightlyDUnstable_one :
    TightlyDUnstable 1 tightOneChoice := by
  constructor
  · exact tightOne_dUnstable_one
  · intro k hk hunstable
    have hle : 1 ≤ k := by
      have hdist := hunstable tightOneBase tightOneFresh
        tightOne_fresh_not_mem_base
      simpa [tightOne_choiceDistance_witness] using hdist
    omega

/-! ## Tight even-instability examples -/

/--
A `q = 1` rule on `Fin 3` with tight instability `2`.

On the pool `{0, 2}`, adding applicant `1` switches the chosen applicant from
`0` to `2`, while the fresh applicant is rejected.
-/
def tightTwoChoice : ChoiceRule (Fin 3) :=
  fun X =>
    if X.card ≤ 1 then
      X
    else if (1 : Fin 3) ∈ X ∧ (2 : Fin 3) ∈ X then
      {(2 : Fin 3)}
    else if (0 : Fin 3) ∈ X then
      {(0 : Fin 3)}
    else
      X

/-- The pool whose one-step expansion attains distance `2`. -/
def tightTwoBase : Finset (Fin 3) :=
  {(0 : Fin 3), (2 : Fin 3)}

/-- The fresh applicant for the tight-2 witness. -/
def tightTwoFresh : Fin 3 :=
  (1 : Fin 3)

theorem tightTwo_feasible :
    Feasible tightTwoChoice := by
  intro X
  fin_cases X <;> decide

theorem tightTwo_qAcceptant :
    QAcceptant 1 tightTwoChoice := by
  intro X
  fin_cases X <;> decide

theorem tightTwo_dUnstable_two :
    DUnstable 2 tightTwoChoice := by
  simpa using
    (dUnstable_two_mul_of_qAcceptant
      (q := 1) (C := tightTwoChoice) tightTwo_qAcceptant)

theorem tightTwo_base_card_ge :
    1 ≤ tightTwoBase.card := by
  decide

theorem tightTwo_fresh_not_mem_base :
    tightTwoFresh ∉ tightTwoBase := by
  decide

theorem tightTwo_fresh_not_chosen_after_insert :
    tightTwoFresh ∉ tightTwoChoice (insert tightTwoFresh tightTwoBase) := by
  decide

theorem tightTwo_loss_card_witness :
    (tightTwoChoice tightTwoBase \
      tightTwoChoice (insert tightTwoFresh tightTwoBase)).card = 1 := by
  decide

theorem tightTwo_choiceDistance_witness :
    choiceDistance tightTwoChoice tightTwoBase
      (insert tightTwoFresh tightTwoBase) = 2 := by
  rw [choiceDistance_insert_eq_if_mem
    (C := tightTwoChoice) (q := 1)
    tightTwo_feasible tightTwo_qAcceptant
    tightTwo_base_card_ge tightTwo_fresh_not_mem_base]
  simp [tightTwo_fresh_not_chosen_after_insert,
    tightTwo_loss_card_witness]

theorem tightTwo_tightlyDUnstable_two :
    TightlyDUnstable 2 tightTwoChoice := by
  constructor
  · exact tightTwo_dUnstable_two
  · intro k hk hunstable
    have hle : 2 ≤ k := by
      have hdist := hunstable tightTwoBase tightTwoFresh
        tightTwo_fresh_not_mem_base
      simpa [tightTwo_choiceDistance_witness] using hdist
    omega

/-! ## A tight odd higher-instability example -/

/--
A grouped/complementary `q = 2` rule on `Fin 4`.

For pools of size at most two it accepts everyone.  For larger pools, the
presence of both applicants `2` and `3` triggers the complementary group
`{2, 3}`; otherwise the rule chooses `{0, 1}`.  On the pool `{0, 1, 3}`,
adding `2` switches the accepted pair from `{0, 1}` to `{2, 3}`.
-/
def tightThreeChoice : ChoiceRule (Fin 4) :=
  fun X =>
    if X.card ≤ 2 then
      X
    else if (2 : Fin 4) ∈ X ∧ (3 : Fin 4) ∈ X then
      {(2 : Fin 4), (3 : Fin 4)}
    else
      {(0 : Fin 4), (1 : Fin 4)}

/-- The pool whose one-step expansion attains distance `3`. -/
def tightThreeBase : Finset (Fin 4) :=
  {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)}

/-- The fresh applicant that triggers the complementary group. -/
def tightThreeFresh : Fin 4 :=
  (2 : Fin 4)

theorem tightThree_feasible :
    Feasible tightThreeChoice := by
  intro X
  fin_cases X <;> decide

theorem tightThree_qAcceptant :
    QAcceptant 2 tightThreeChoice := by
  intro X
  fin_cases X <;> decide

theorem tightThree_dUnstable_three :
    DUnstable 3 tightThreeChoice := by
  intro X x _hx
  fin_cases X <;> fin_cases x <;> decide

theorem tightThree_base_card_ge :
    2 ≤ tightThreeBase.card := by
  decide

theorem tightThree_fresh_not_mem_base :
    tightThreeFresh ∉ tightThreeBase := by
  decide

theorem tightThree_fresh_chosen_after_insert :
    tightThreeFresh ∈ tightThreeChoice
      (insert tightThreeFresh tightThreeBase) := by
  decide

theorem tightThree_loss_card_witness :
    (tightThreeChoice tightThreeBase \
      tightThreeChoice (insert tightThreeFresh tightThreeBase)).card = 2 := by
  decide

/--
The nontrivial one-step calculation, using the library's insert-distance
formula.  Since the fresh applicant is chosen and both old choices are lost,
the distance is `2 * 2 - 1 = 3`.
-/
theorem tightThree_choiceDistance_witness :
    choiceDistance tightThreeChoice tightThreeBase
      (insert tightThreeFresh tightThreeBase) = 3 := by
  rw [choiceDistance_insert_eq_if_mem
    (C := tightThreeChoice) (q := 2)
    tightThree_feasible tightThree_qAcceptant
    tightThree_base_card_ge tightThree_fresh_not_mem_base]
  simp [tightThree_fresh_chosen_after_insert,
    tightThree_loss_card_witness]

theorem tightThree_tightlyDUnstable_three :
    TightlyDUnstable 3 tightThreeChoice := by
  constructor
  · exact tightThree_dUnstable_three
  · intro k hk hunstable
    have hle : 3 ≤ k := by
      have hdist := hunstable tightThreeBase tightThreeFresh
        tightThree_fresh_not_mem_base
      simpa [tightThree_choiceDistance_witness] using hdist
    omega

/-! ## Another tight even-instability example -/

/-- Baseline priority fallback for the tight-4 construction. -/
def tightFourPriorityChoice (X : Finset (Fin 5)) : Finset (Fin 5) :=
  (([(0 : Fin 5), (1 : Fin 5), (2 : Fin 5), (3 : Fin 5),
      (4 : Fin 5)].filter fun a => a ∈ X).take 2).toFinset

/--
A grouped/complementary `q = 2` rule on `Fin 5` with tight instability `4`.

For pools of size at most two it accepts everyone.  For larger pools, the
presence of all applicants `2`, `3`, and `4` triggers the complementary group
`{3, 4}`; otherwise the rule chooses the top two available applicants in the
fixed fallback priority order.  On the pool `{0, 1, 3, 4}`, adding `2`
switches the accepted pair from `{0, 1}` to `{3, 4}`, while `2` is rejected.
-/
def tightFourChoice : ChoiceRule (Fin 5) :=
  fun X =>
    if X.card ≤ 2 then
      X
    else if (2 : Fin 5) ∈ X ∧ (3 : Fin 5) ∈ X ∧ (4 : Fin 5) ∈ X then
      {(3 : Fin 5), (4 : Fin 5)}
    else
      tightFourPriorityChoice X

/-- The pool whose one-step expansion attains distance `4`. -/
def tightFourBase : Finset (Fin 5) :=
  {(0 : Fin 5), (1 : Fin 5), (3 : Fin 5), (4 : Fin 5)}

/-- The fresh applicant that triggers the complementary group. -/
def tightFourFresh : Fin 5 :=
  (2 : Fin 5)

theorem tightFour_feasible :
    Feasible tightFourChoice := by
  intro X
  fin_cases X <;> decide

theorem tightFour_qAcceptant :
    QAcceptant 2 tightFourChoice := by
  intro X
  fin_cases X <;> decide

theorem tightFour_dUnstable_four :
    DUnstable 4 tightFourChoice := by
  simpa using
    (dUnstable_two_mul_of_qAcceptant
      (q := 2) (C := tightFourChoice) tightFour_qAcceptant)

theorem tightFour_base_card_ge :
    2 ≤ tightFourBase.card := by
  decide

theorem tightFour_fresh_not_mem_base :
    tightFourFresh ∉ tightFourBase := by
  decide

theorem tightFour_fresh_not_chosen_after_insert :
    tightFourFresh ∉ tightFourChoice (insert tightFourFresh tightFourBase) := by
  decide

theorem tightFour_loss_card_witness :
    (tightFourChoice tightFourBase \
      tightFourChoice (insert tightFourFresh tightFourBase)).card = 2 := by
  decide

theorem tightFour_choiceDistance_witness :
    choiceDistance tightFourChoice tightFourBase
      (insert tightFourFresh tightFourBase) = 4 := by
  rw [choiceDistance_insert_eq_if_mem
    (C := tightFourChoice) (q := 2)
    tightFour_feasible tightFour_qAcceptant
    tightFour_base_card_ge tightFour_fresh_not_mem_base]
  simp [tightFour_fresh_not_chosen_after_insert,
    tightFour_loss_card_witness]

theorem tightFour_tightlyDUnstable_four :
    TightlyDUnstable 4 tightFourChoice := by
  constructor
  · exact tightFour_dUnstable_four
  · intro k hk hunstable
    have hle : 4 ≤ k := by
      have hdist := hunstable tightFourBase tightFourFresh
        tightFour_fresh_not_mem_base
      simpa [tightFour_choiceDistance_witness] using hdist
    omega

/-! ## A tight 5-instability example -/

/-- Baseline priority fallback for the tight-5 construction. -/
def tightFivePriorityChoice (X : Finset (Fin 6)) : Finset (Fin 6) :=
  (([(0 : Fin 6), (1 : Fin 6), (2 : Fin 6), (3 : Fin 6), (4 : Fin 6),
      (5 : Fin 6)].filter fun a => a ∈ X).take 3).toFinset

/--
A grouped/complementary `q = 3` rule on `Fin 6`.

For pools of size at most three it accepts everyone.  For larger pools, the
presence of all applicants `3`, `4`, and `5` triggers the complementary group
`{3, 4, 5}`; otherwise the rule chooses the top three available applicants in
the fixed fallback priority order.  On the pool `{0, 1, 2, 4, 5}`, adding `3`
switches the accepted triple from `{0, 1, 2}` to `{3, 4, 5}`.
-/
def tightFiveChoice : ChoiceRule (Fin 6) :=
  fun X =>
    if X.card ≤ 3 then
      X
    else if (3 : Fin 6) ∈ X ∧ (4 : Fin 6) ∈ X ∧ (5 : Fin 6) ∈ X then
      {(3 : Fin 6), (4 : Fin 6), (5 : Fin 6)}
    else
      tightFivePriorityChoice X

/-- The pool whose one-step expansion attains distance `5`. -/
def tightFiveBase : Finset (Fin 6) :=
  {(0 : Fin 6), (1 : Fin 6), (2 : Fin 6), (4 : Fin 6), (5 : Fin 6)}

/-- The fresh applicant that triggers the complementary group. -/
def tightFiveFresh : Fin 6 :=
  (3 : Fin 6)

theorem tightFive_feasible :
    Feasible tightFiveChoice := by
  intro X
  fin_cases X <;> decide

theorem tightFive_qAcceptant :
    QAcceptant 3 tightFiveChoice := by
  intro X
  fin_cases X <;> decide

theorem tightFive_dUnstable_five :
    DUnstable 5 tightFiveChoice := by
  intro X x _hx
  fin_cases X <;> fin_cases x <;> decide

theorem tightFive_base_card_ge :
    3 ≤ tightFiveBase.card := by
  decide

theorem tightFive_fresh_not_mem_base :
    tightFiveFresh ∉ tightFiveBase := by
  decide

theorem tightFive_fresh_chosen_after_insert :
    tightFiveFresh ∈ tightFiveChoice
      (insert tightFiveFresh tightFiveBase) := by
  decide

theorem tightFive_loss_card_witness :
    (tightFiveChoice tightFiveBase \
      tightFiveChoice (insert tightFiveFresh tightFiveBase)).card = 3 := by
  decide

/--
The nontrivial one-step calculation, using the library's insert-distance
formula.  Since the fresh applicant is chosen and three old choices are lost,
the distance is `2 * 3 - 1 = 5`.
-/
theorem tightFive_choiceDistance_witness :
    choiceDistance tightFiveChoice tightFiveBase
      (insert tightFiveFresh tightFiveBase) = 5 := by
  rw [choiceDistance_insert_eq_if_mem
    (C := tightFiveChoice) (q := 3)
    tightFive_feasible tightFive_qAcceptant
    tightFive_base_card_ge tightFive_fresh_not_mem_base]
  simp [tightFive_fresh_chosen_after_insert,
    tightFive_loss_card_witness]

theorem tightFive_tightlyDUnstable_five :
    TightlyDUnstable 5 tightFiveChoice := by
  constructor
  · exact tightFive_dUnstable_five
  · intro k hk hunstable
    have hle : 5 ≤ k := by
      have hdist := hunstable tightFiveBase tightFiveFresh
        tightFive_fresh_not_mem_base
      simpa [tightFive_choiceDistance_witness] using hdist
    omega

end DGD26AdmissionsPredictability
