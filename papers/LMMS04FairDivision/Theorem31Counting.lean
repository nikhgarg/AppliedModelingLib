import LMMS04FairDivision.Theorem31QueryLowerBound
import Mathlib.Data.Fintype.BigOperators

open AppliedModelingLib.FairDivision

namespace LMMS04FairDivision
namespace Theorem31

/-!
# Counting layer for LMMS Theorem 3.1

The source proof counts hard functions by making one binary choice for every
middle-layer complement pair.  This file packages exactly that finite
combinatorial seam: if the middle layer is presented as `Pair × Bool`, with
complement toggling the Boolean coordinate, then every orientation of the
pairs gives a distinct `LMMS31HardFunction`.
-/

/--
A source-shaped certificate that the middle layer `|S| = k` has been split
into complement pairs.  `decode (p, false)` and `decode (p, true)` are the two
members of pair `p`, and complementing a middle-layer set flips the Boolean
orientation.
-/
structure LMMS31MiddleComplementPairs
    (Item : Type*) [Fintype Item] [DecidableEq Item] (k : ℕ) where
  Pair : Type*
  [pairFintype : Fintype Pair]
  decode : Pair × Bool ≃ {S : Finset Item // S.card = k}
  complement_decode :
    ∀ p b, (decode (p, !b)).1 = (decode (p, b)).1ᶜ

attribute [instance] LMMS31MiddleComplementPairs.pairFintype

namespace LMMS31MiddleComplementPairs

variable {Item : Type*} [Fintype Item] [DecidableEq Item] {k : ℕ}
variable (C : LMMS31MiddleComplementPairs Item k)

/-- The `0/1` middle-layer value induced by an orientation of complement pairs. -/
noncomputable def middleChoiceValue
    (choice : C.Pair → Bool) (S : Finset Item) (hS : S.card = k) : ℝ :=
  if choice (C.decode.symm ⟨S, hS⟩).1 = (C.decode.symm ⟨S, hS⟩).2 then 1 else 0

theorem middleChoiceValue_binary
    (choice : C.Pair → Bool) (S : Finset Item) (hS : S.card = k) :
    C.middleChoiceValue choice S hS = 0 ∨
      C.middleChoiceValue choice S hS = 1 := by
  classical
  unfold middleChoiceValue
  by_cases h :
      choice (C.decode.symm ⟨S, hS⟩).1 = (C.decode.symm ⟨S, hS⟩).2
  · right
    simp [h]
  · left
    simp [h]

theorem decode_symm_compl
    (S : Finset Item) (hS : S.card = k) (hcomp : Sᶜ.card = k) :
    C.decode.symm ⟨Sᶜ, hcomp⟩ =
      ((C.decode.symm ⟨S, hS⟩).1, !(C.decode.symm ⟨S, hS⟩).2) := by
  classical
  let q := C.decode.symm ⟨S, hS⟩
  have hq : C.decode q = ⟨S, hS⟩ := by
    simp [q]
  have hq_val : (C.decode q).1 = S := by
    exact congrArg Subtype.val hq
  have hdecode_comp : C.decode (q.1, !q.2) = ⟨Sᶜ, hcomp⟩ := by
    apply Subtype.ext
    simpa [hq_val] using C.complement_decode q.1 q.2
  have := congrArg C.decode.symm hdecode_comp
  simpa [q] using this.symm

theorem middleChoiceValue_compl
    (choice : C.Pair → Bool) (S : Finset Item)
    (hS : S.card = k) (hcomp : Sᶜ.card = k) :
    C.middleChoiceValue choice S hS +
      C.middleChoiceValue choice Sᶜ hcomp = 1 := by
  classical
  let q := C.decode.symm ⟨S, hS⟩
  have hsymm :
      C.decode.symm ⟨Sᶜ, hcomp⟩ = (q.1, !q.2) := by
    simpa [q] using C.decode_symm_compl S hS hcomp
  cases hq2 : q.2 <;>
    cases hchoice : choice q.1 <;>
      simp [middleChoiceValue, q, hsymm, hq2, hchoice]

/--
The hard function obtained by choosing one orientation from every middle-layer
complement pair.
-/
noncomputable def hardFunctionOfMiddleChoice
    (choice : C.Pair → Bool) : LMMS31HardFunction Item k where
  val S :=
    if hlt : S.card < k then 0
    else if hgt : k < S.card then 1
    else
      C.middleChoiceValue choice S (by omega)
  zero_of_card_lt S hlt := by
    simp [hlt]
  one_of_card_gt S hgt := by
    have hnot_lt : ¬ S.card < k := by omega
    simp [hnot_lt, hgt]
  complement_sum_of_card_eq S hS := by
    classical
    have hnot_lt : ¬ S.card < k := by omega
    have hnot_gt : ¬ k < S.card := by omega
    have hcomp : Sᶜ.card = k := by
      let q := C.decode.symm ⟨S, hS⟩
      have hq : C.decode q = ⟨S, hS⟩ := by
        simp [q]
      have hq_val : (C.decode q).1 = S := by
        exact congrArg Subtype.val hq
      have hcomp_val : (C.decode (q.1, !q.2)).1 = Sᶜ := by
        simpa [hq_val] using C.complement_decode q.1 q.2
      have hcard : ((C.decode (q.1, !q.2)).1).card = k :=
        (C.decode (q.1, !q.2)).2
      simpa [hcomp_val] using hcard
    have hcomp_sdiff : ((Finset.univ : Finset Item) \ S).card = k := by
      simpa [Finset.compl_eq_univ_sdiff] using hcomp
    have hcomp_not_lt : ¬ ((Finset.univ : Finset Item) \ S).card < k := by omega
    have hcomp_not_gt : ¬ k < ((Finset.univ : Finset Item) \ S).card := by omega
    simp [hnot_lt, hnot_gt, hcomp_not_lt, hcomp_not_gt]
    simpa [Finset.compl_eq_univ_sdiff] using
      C.middleChoiceValue_compl choice S hS hcomp
  binary_of_card_eq S hS := by
    classical
    have hnot_lt : ¬ S.card < k := by omega
    have hnot_gt : ¬ k < S.card := by omega
    simpa [hnot_lt, hnot_gt] using C.middleChoiceValue_binary choice S hS

theorem hardFunctionOfMiddleChoice_middle
    (choice : C.Pair → Bool) (S : Finset Item) (hS : S.card = k) :
    (C.hardFunctionOfMiddleChoice choice).val S =
      C.middleChoiceValue choice S hS := by
  classical
  have hnot_lt : ¬ S.card < k := by omega
  have hnot_gt : ¬ k < S.card := by omega
  simp [hardFunctionOfMiddleChoice, hnot_lt, hnot_gt]

theorem hardFunctionOfMiddleChoice_decode_true
    (choice : C.Pair → Bool) (p : C.Pair) :
    (C.hardFunctionOfMiddleChoice choice).val ((C.decode (p, true)).1) =
      if choice p = true then 1 else 0 := by
  classical
  have hcard : ((C.decode (p, true)).1).card = k :=
    (C.decode (p, true)).2
  have hsymm :
      C.decode.symm ⟨(C.decode (p, true)).1, hcard⟩ = (p, true) := by
    simp
  simp [C.hardFunctionOfMiddleChoice_middle choice ((C.decode (p, true)).1) hcard,
    middleChoiceValue, hsymm]

/--
Different middle-pair orientations yield an ordered middle-layer disagreement:
after possibly swapping the two generated hard functions, one gives value `1`
and the other gives value `0` on a middle-layer set.
-/
theorem exists_ordered_middle_disagreement_of_choice_ne
    {choice₁ choice₂ : C.Pair → Bool} (hne : choice₁ ≠ choice₂) :
    (∃ S : Finset Item, S.card = k ∧
      (C.hardFunctionOfMiddleChoice choice₁).val S = 1 ∧
      (C.hardFunctionOfMiddleChoice choice₂).val S = 0) ∨
    (∃ S : Finset Item, S.card = k ∧
      (C.hardFunctionOfMiddleChoice choice₂).val S = 1 ∧
      (C.hardFunctionOfMiddleChoice choice₁).val S = 0) := by
  classical
  have hnot_forall : ¬ ∀ p : C.Pair, choice₁ p = choice₂ p := by
    intro hforall
    exact hne (funext hforall)
  push Not at hnot_forall
  rcases hnot_forall with ⟨p, hp_ne⟩
  have hcard : ((C.decode (p, true)).1).card = k :=
    (C.decode (p, true)).2
  cases h₁ : choice₁ p <;> cases h₂ : choice₂ p
  · exact False.elim (hp_ne (by simp [h₁, h₂]))
  · right
    refine ⟨(C.decode (p, true)).1, hcard, ?_, ?_⟩
    · simpa [h₂] using C.hardFunctionOfMiddleChoice_decode_true choice₂ p
    · simpa [h₁] using C.hardFunctionOfMiddleChoice_decode_true choice₁ p
  · left
    refine ⟨(C.decode (p, true)).1, hcard, ?_, ?_⟩
    · simpa [h₁] using C.hardFunctionOfMiddleChoice_decode_true choice₁ p
    · simpa [h₂] using C.hardFunctionOfMiddleChoice_decode_true choice₂ p
  · exact False.elim (hp_ne (by simp [h₁, h₂]))

/-- Different pair orientations give different hard functions. -/
theorem hardFunctionOfMiddleChoice_injective :
    Function.Injective C.hardFunctionOfMiddleChoice := by
  classical
  intro choice₁ choice₂ hfun
  funext p
  have hval :
      (C.hardFunctionOfMiddleChoice choice₁).val ((C.decode (p, true)).1) =
        (C.hardFunctionOfMiddleChoice choice₂).val ((C.decode (p, true)).1) := by
    simpa using congrArg
      (fun H : LMMS31HardFunction Item k => H.val ((C.decode (p, true)).1)) hfun
  rw [C.hardFunctionOfMiddleChoice_decode_true choice₁ p,
    C.hardFunctionOfMiddleChoice_decode_true choice₂ p] at hval
  cases h₁ : choice₁ p <;> cases h₂ : choice₂ p <;> simp [h₁, h₂] at hval ⊢

/-- The finite hard family generated by all middle-layer pair orientations. -/
noncomputable def hardFunctionFamily : Finset (LMMS31HardFunction Item k) := by
  classical
  exact Finset.univ.image C.hardFunctionOfMiddleChoice

/--
Counting lemma for the hard family: the source complement-pair certificate
produces exactly `2 ^ #pairs` distinct hard functions.
-/
theorem hardFunctionFamily_card :
    (hardFunctionFamily C).card = 2 ^ Fintype.card C.Pair := by
  classical
  rw [hardFunctionFamily, Finset.card_image_of_injective]
  · rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool]
  · exact C.hardFunctionOfMiddleChoice_injective

/--
Source-shaped counting certificate for Theorem 3.1.  If the algorithm's finite
transcript space is smaller than the finite hard family generated by the
middle-layer complement pairs, then it is smaller than `2 ^ #pairs`.
-/
theorem transcript_card_lt_hardFunctionFamily_card_iff
    {Transcript : Type*} [Fintype Transcript]
    (hlt : Fintype.card Transcript < 2 ^ Fintype.card C.Pair) :
    Fintype.card Transcript < (hardFunctionFamily C).card := by
  simpa [C.hardFunctionFamily_card] using hlt

/--
Finite Theorem 3.1 assembly from the source counting step.  If identical
profiles indexed by middle-pair orientations have fewer transcripts than
orientations, and equal identical-profile transcripts imply equal swapped
cross-profile transcripts, then a deterministic output cannot be a
minimum-envy allocation for every crossed hard profile.
-/
theorem minimum_envy_lower_bound_from_middle_pair_count
    {Transcript : Type*} [Fintype Transcript]
    (hcard_items : Fintype.card Item = 2 * k)
    (identicalTranscript : (C.Pair → Bool) → Transcript)
    (crossTranscript : (C.Pair → Bool) → (C.Pair → Bool) → Transcript)
    (output : Transcript → Allocation LMMS31Agent Item)
    (htranscript_bound : Fintype.card Transcript < 2 ^ Fintype.card C.Pair)
    (hcross_same :
      ∀ choice₁ choice₂,
        identicalTranscript choice₁ = identicalTranscript choice₂ →
          crossTranscript choice₁ choice₂ =
            crossTranscript choice₂ choice₁) :
    ¬ ∀ choice₁ choice₂,
      MinimumReportEnvyAllocation
        (lmms31CrossReport
          (C.hardFunctionOfMiddleChoice choice₁)
          (C.hardFunctionOfMiddleChoice choice₂))
        (Finset.univ : Finset Item)
        (output (crossTranscript choice₁ choice₂)) := by
  classical
  have hcard_choices :
      Fintype.card Transcript < Fintype.card (C.Pair → Bool) := by
    simpa [Fintype.card_fun, Fintype.card_bool] using htranscript_bound
  rcases exists_collision_of_card_lt identicalTranscript hcard_choices with
    ⟨choice₁, choice₂, hchoice_ne, hsame_identical⟩
  have hsame_cross := hcross_same choice₁ choice₂ hsame_identical
  intro hcorrect
  rcases C.exists_ordered_middle_disagreement_of_choice_ne hchoice_ne with
    hdisagree | hdisagree
  · let pairTranscript : LMMS31Agent → Transcript :=
      fun inst => if inst = (0 : LMMS31Agent) then
        crossTranscript choice₁ choice₂
      else
        crossTranscript choice₂ choice₁
    have hpair_same :
        pairTranscript (0 : LMMS31Agent) =
          pairTranscript (1 : LMMS31Agent) := by
      simpa [pairTranscript] using hsame_cross
    have hnot :=
      lmms31_minimum_envy_query_lower_bound_of_swapped_cross_pair
        hcard_items
        (C.hardFunctionOfMiddleChoice choice₁)
        (C.hardFunctionOfMiddleChoice choice₂)
        hdisagree pairTranscript output hpair_same
    exact hnot (by
      intro inst
      fin_cases inst
      · simpa [pairTranscript, lmms31SwappedCrossReport] using
          hcorrect choice₁ choice₂
      · simpa [pairTranscript, lmms31SwappedCrossReport] using
          hcorrect choice₂ choice₁)
  · let pairTranscript : LMMS31Agent → Transcript :=
      fun inst => if inst = (0 : LMMS31Agent) then
        crossTranscript choice₂ choice₁
      else
        crossTranscript choice₁ choice₂
    have hpair_same :
        pairTranscript (0 : LMMS31Agent) =
          pairTranscript (1 : LMMS31Agent) := by
      simpa [pairTranscript] using hsame_cross.symm
    have hnot :=
      lmms31_minimum_envy_query_lower_bound_of_swapped_cross_pair
        hcard_items
        (C.hardFunctionOfMiddleChoice choice₂)
        (C.hardFunctionOfMiddleChoice choice₁)
        hdisagree pairTranscript output hpair_same
    exact hnot (by
      intro inst
      fin_cases inst
      · simpa [pairTranscript, lmms31SwappedCrossReport] using
          hcorrect choice₂ choice₁
      · simpa [pairTranscript, lmms31SwappedCrossReport] using
          hcorrect choice₁ choice₂)

/--
Finite Theorem 3.1 envy-ratio assembly from the same source counting step.
The multiplicative ratio objective is expressed without division; since every
crossed hard profile has an envy-free allocation, a minimum-ratio output must
be envy-free, so the swapped-pair obstruction applies.
-/
theorem minimum_envy_ratio_lower_bound_from_middle_pair_count
    {Transcript : Type*} [Fintype Transcript]
    (hcard_items : Fintype.card Item = 2 * k)
    (identicalTranscript : (C.Pair → Bool) → Transcript)
    (crossTranscript : (C.Pair → Bool) → (C.Pair → Bool) → Transcript)
    (output : Transcript → Allocation LMMS31Agent Item)
    (htranscript_bound : Fintype.card Transcript < 2 ^ Fintype.card C.Pair)
    (hcross_same :
      ∀ choice₁ choice₂,
        identicalTranscript choice₁ = identicalTranscript choice₂ →
          crossTranscript choice₁ choice₂ =
            crossTranscript choice₂ choice₁) :
    ¬ ∀ choice₁ choice₂,
      MinimumReportEnvyRatioAllocation
        (lmms31CrossReport
          (C.hardFunctionOfMiddleChoice choice₁)
          (C.hardFunctionOfMiddleChoice choice₂))
        (Finset.univ : Finset Item)
        (output (crossTranscript choice₁ choice₂)) := by
  classical
  have hcard_choices :
      Fintype.card Transcript < Fintype.card (C.Pair → Bool) := by
    simpa [Fintype.card_fun, Fintype.card_bool] using htranscript_bound
  rcases exists_collision_of_card_lt identicalTranscript hcard_choices with
    ⟨choice₁, choice₂, hchoice_ne, hsame_identical⟩
  have hsame_cross := hcross_same choice₁ choice₂ hsame_identical
  intro hcorrect
  rcases C.exists_ordered_middle_disagreement_of_choice_ne hchoice_ne with
    hdisagree | hdisagree
  · let pairTranscript : LMMS31Agent → Transcript :=
      fun inst => if inst = (0 : LMMS31Agent) then
        crossTranscript choice₁ choice₂
      else
        crossTranscript choice₂ choice₁
    have hpair_same :
        pairTranscript (0 : LMMS31Agent) =
          pairTranscript (1 : LMMS31Agent) := by
      simpa [pairTranscript] using hsame_cross
    have hnot :=
      lmms31_minimum_envy_ratio_query_lower_bound_of_swapped_cross_pair
        hcard_items
        (C.hardFunctionOfMiddleChoice choice₁)
        (C.hardFunctionOfMiddleChoice choice₂)
        hdisagree pairTranscript output hpair_same
    exact hnot (by
      intro inst
      fin_cases inst
      · simpa [pairTranscript, lmms31SwappedCrossReport] using
          hcorrect choice₁ choice₂
      · simpa [pairTranscript, lmms31SwappedCrossReport] using
          hcorrect choice₂ choice₁)
  · let pairTranscript : LMMS31Agent → Transcript :=
      fun inst => if inst = (0 : LMMS31Agent) then
        crossTranscript choice₂ choice₁
      else
        crossTranscript choice₁ choice₂
    have hpair_same :
        pairTranscript (0 : LMMS31Agent) =
          pairTranscript (1 : LMMS31Agent) := by
      simpa [pairTranscript] using hsame_cross.symm
    have hnot :=
      lmms31_minimum_envy_ratio_query_lower_bound_of_swapped_cross_pair
        hcard_items
        (C.hardFunctionOfMiddleChoice choice₂)
        (C.hardFunctionOfMiddleChoice choice₁)
        hdisagree pairTranscript output hpair_same
    exact hnot (by
      intro inst
      fin_cases inst
      · simpa [pairTranscript, lmms31SwappedCrossReport] using
          hcorrect choice₂ choice₁
      · simpa [pairTranscript, lmms31SwappedCrossReport] using
          hcorrect choice₁ choice₂)

end LMMS31MiddleComplementPairs

end Theorem31
end LMMS04FairDivision
