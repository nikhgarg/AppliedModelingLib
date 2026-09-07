import LMMS04FairDivision.Theorem31Counting

open AppliedModelingLib.FairDivision

namespace LMMS04FairDivision
namespace Theorem31

/-!
# LMMS Theorem 3.1: finite query transcript counting

This file closes the finite transcript-count seam used by the source
exponential lower-bound proof.  A deterministic algorithm that makes `q`
queries and receives answers from a finite alphabet has at most
`|Answer|^q` possible transcripts.  When that number is smaller than the
middle-layer hard family, the existing collision argument rules out correctness
on all crossed hard profiles.
-/

/-- Transcript type for `q` deterministic queries with answers in `Answer`. -/
abbrev QueryTranscript (Answer : Type*) (q : ℕ) :=
  Fin q → Answer

theorem queryTranscript_card (Answer : Type*) [Fintype Answer] (q : ℕ) :
    Fintype.card (QueryTranscript Answer q) =
      Fintype.card Answer ^ q := by
  simp [QueryTranscript]

theorem twoBitQueryTranscript_card (q : ℕ) :
    Fintype.card (QueryTranscript (Bool × Bool) q) = 4 ^ q := by
  simp [Fintype.card_prod]

/-- Booleanized value answer for a source hard function. -/
noncomputable def hardFunctionBoolAnswer
    {Item : Type*} [Fintype Item] [DecidableEq Item] {k : ℕ}
    (f : LMMS31HardFunction Item k) (S : Finset Item) : Bool :=
  decide (f.val S = 1)

/-- Transcript of fixed two-player value queries with Booleanized answers. -/
noncomputable def twoPlayerHardFunctionQueryTranscript
    {Item : Type*} [Fintype Item] [DecidableEq Item] {k q : ℕ}
    (queries : Fin q → Finset Item)
    (u v : LMMS31HardFunction Item k) : QueryTranscript (Bool × Bool) q :=
  fun t => (hardFunctionBoolAnswer u (queries t),
    hardFunctionBoolAnswer v (queries t))

/--
For fixed nonadaptive value queries, equality of identical-profile transcripts
implies the crossed transcripts agree after swapping players.
-/
theorem twoPlayerHardFunctionQueryTranscript_swap_eq_of_identical_eq
    {Item : Type*} [Fintype Item] [DecidableEq Item] {k q : ℕ}
    (queries : Fin q → Finset Item)
    (u v : LMMS31HardFunction Item k)
    (hidentical :
      twoPlayerHardFunctionQueryTranscript queries u u =
        twoPlayerHardFunctionQueryTranscript queries v v) :
    twoPlayerHardFunctionQueryTranscript queries u v =
      twoPlayerHardFunctionQueryTranscript queries v u := by
  funext t
  have ht := congrFun hidentical t
  have hanswer :
      hardFunctionBoolAnswer u (queries t) =
        hardFunctionBoolAnswer v (queries t) :=
    congrArg Prod.fst ht
  simp [twoPlayerHardFunctionQueryTranscript, hanswer]

namespace LMMS31MiddleComplementPairs

variable {Item : Type*} [Fintype Item] [DecidableEq Item] {k : ℕ}
variable (C : LMMS31MiddleComplementPairs Item k)

theorem queryTranscript_card_lt_hard_family_card
    {Answer : Type*} [Fintype Answer] {q : ℕ}
    (hlt : Fintype.card Answer ^ q < 2 ^ Fintype.card C.Pair) :
    Fintype.card (QueryTranscript Answer q) < (hardFunctionFamily C).card := by
  simpa [queryTranscript_card, C.hardFunctionFamily_card] using hlt

theorem twoBitQueryTranscript_card_lt_hard_family_card
    {q : ℕ} (hlt : 4 ^ q < 2 ^ Fintype.card C.Pair) :
    Fintype.card (QueryTranscript (Bool × Bool) q) <
      (hardFunctionFamily C).card := by
  simpa [twoBitQueryTranscript_card, C.hardFunctionFamily_card] using hlt

/--
Two-bit query transcript bound in source scale: if twice the number of queries
is smaller than the number of middle complement pairs, then the two-bit
transcript space is smaller than the hard family.
-/
theorem twoBitQueryTranscript_card_lt_hard_family_card_of_two_mul_lt
    {q : ℕ} (hlt : 2 * q < Fintype.card C.Pair) :
    Fintype.card (QueryTranscript (Bool × Bool) q) <
      (hardFunctionFamily C).card := by
  have hpow : 4 ^ q = 2 ^ (2 * q) := by
    rw [show 4 = 2 ^ 2 by norm_num, pow_mul]
  rw [twoBitQueryTranscript_card, C.hardFunctionFamily_card, hpow]
  exact Nat.pow_lt_pow_right (by norm_num : 1 < (2 : ℕ)) hlt

theorem minimum_envy_lower_bound_from_query_transcript_count
    {Answer : Type*} [Fintype Answer] {q : ℕ}
    (hcard_items : Fintype.card Item = 2 * k)
    (identicalTranscript : (C.Pair → Bool) → QueryTranscript Answer q)
    (crossTranscript :
      (C.Pair → Bool) → (C.Pair → Bool) → QueryTranscript Answer q)
    (output : QueryTranscript Answer q → Allocation LMMS31Agent Item)
    (hquery_bound : Fintype.card Answer ^ q < 2 ^ Fintype.card C.Pair)
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
  exact
    C.minimum_envy_lower_bound_from_middle_pair_count
      hcard_items identicalTranscript crossTranscript output
      (by simpa [queryTranscript_card] using hquery_bound)
      hcross_same

theorem minimum_envy_ratio_lower_bound_from_query_transcript_count
    {Answer : Type*} [Fintype Answer] {q : ℕ}
    (hcard_items : Fintype.card Item = 2 * k)
    (identicalTranscript : (C.Pair → Bool) → QueryTranscript Answer q)
    (crossTranscript :
      (C.Pair → Bool) → (C.Pair → Bool) → QueryTranscript Answer q)
    (output : QueryTranscript Answer q → Allocation LMMS31Agent Item)
    (hquery_bound : Fintype.card Answer ^ q < 2 ^ Fintype.card C.Pair)
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
  exact
    C.minimum_envy_ratio_lower_bound_from_middle_pair_count
      hcard_items identicalTranscript crossTranscript output
      (by simpa [queryTranscript_card] using hquery_bound)
      hcross_same

theorem minimum_envy_lower_bound_from_twoBit_query_transcript_count
    {q : ℕ}
    (hcard_items : Fintype.card Item = 2 * k)
    (identicalTranscript : (C.Pair → Bool) → QueryTranscript (Bool × Bool) q)
    (crossTranscript :
      (C.Pair → Bool) → (C.Pair → Bool) → QueryTranscript (Bool × Bool) q)
    (output : QueryTranscript (Bool × Bool) q → Allocation LMMS31Agent Item)
    (hquery_bound : 4 ^ q < 2 ^ Fintype.card C.Pair)
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
  exact
    C.minimum_envy_lower_bound_from_query_transcript_count
      hcard_items identicalTranscript crossTranscript output
      (by simpa using hquery_bound) hcross_same

theorem minimum_envy_lower_bound_from_twoBit_query_count_of_two_mul_lt
    {q : ℕ}
    (hcard_items : Fintype.card Item = 2 * k)
    (identicalTranscript : (C.Pair → Bool) → QueryTranscript (Bool × Bool) q)
    (crossTranscript :
      (C.Pair → Bool) → (C.Pair → Bool) → QueryTranscript (Bool × Bool) q)
    (output : QueryTranscript (Bool × Bool) q → Allocation LMMS31Agent Item)
    (hquery_bound : 2 * q < Fintype.card C.Pair)
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
  exact
    C.minimum_envy_lower_bound_from_twoBit_query_transcript_count
      hcard_items identicalTranscript crossTranscript output
      (by
        have hpow : 4 ^ q = 2 ^ (2 * q) := by
          rw [show 4 = 2 ^ 2 by norm_num, pow_mul]
        rw [hpow]
        exact Nat.pow_lt_pow_right (by norm_num : 1 < (2 : ℕ)) hquery_bound)
      hcross_same

theorem minimum_envy_lower_bound_from_twoBit_fixed_queries_of_two_mul_lt
    {q : ℕ}
    (hcard_items : Fintype.card Item = 2 * k)
    (queries : Fin q → Finset Item)
    (output : QueryTranscript (Bool × Bool) q → Allocation LMMS31Agent Item)
    (hquery_bound : 2 * q < Fintype.card C.Pair) :
    ¬ ∀ choice₁ choice₂,
      MinimumReportEnvyAllocation
        (lmms31CrossReport
          (C.hardFunctionOfMiddleChoice choice₁)
          (C.hardFunctionOfMiddleChoice choice₂))
        (Finset.univ : Finset Item)
        (output
          (twoPlayerHardFunctionQueryTranscript queries
            (C.hardFunctionOfMiddleChoice choice₁)
            (C.hardFunctionOfMiddleChoice choice₂))) := by
  exact
    C.minimum_envy_lower_bound_from_twoBit_query_count_of_two_mul_lt
      hcard_items
      (fun choice =>
        twoPlayerHardFunctionQueryTranscript queries
          (C.hardFunctionOfMiddleChoice choice)
          (C.hardFunctionOfMiddleChoice choice))
      (fun choice₁ choice₂ =>
        twoPlayerHardFunctionQueryTranscript queries
          (C.hardFunctionOfMiddleChoice choice₁)
          (C.hardFunctionOfMiddleChoice choice₂))
      output hquery_bound
      (by
        intro choice₁ choice₂ hidentical
        exact
          twoPlayerHardFunctionQueryTranscript_swap_eq_of_identical_eq
            queries
            (C.hardFunctionOfMiddleChoice choice₁)
            (C.hardFunctionOfMiddleChoice choice₂)
            hidentical)

theorem minimum_envy_ratio_lower_bound_from_twoBit_query_transcript_count
    {q : ℕ}
    (hcard_items : Fintype.card Item = 2 * k)
    (identicalTranscript : (C.Pair → Bool) → QueryTranscript (Bool × Bool) q)
    (crossTranscript :
      (C.Pair → Bool) → (C.Pair → Bool) → QueryTranscript (Bool × Bool) q)
    (output : QueryTranscript (Bool × Bool) q → Allocation LMMS31Agent Item)
    (hquery_bound : 4 ^ q < 2 ^ Fintype.card C.Pair)
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
  exact
    C.minimum_envy_ratio_lower_bound_from_query_transcript_count
      hcard_items identicalTranscript crossTranscript output
      (by simpa using hquery_bound) hcross_same

theorem minimum_envy_ratio_lower_bound_from_twoBit_query_count_of_two_mul_lt
    {q : ℕ}
    (hcard_items : Fintype.card Item = 2 * k)
    (identicalTranscript : (C.Pair → Bool) → QueryTranscript (Bool × Bool) q)
    (crossTranscript :
      (C.Pair → Bool) → (C.Pair → Bool) → QueryTranscript (Bool × Bool) q)
    (output : QueryTranscript (Bool × Bool) q → Allocation LMMS31Agent Item)
    (hquery_bound : 2 * q < Fintype.card C.Pair)
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
  exact
    C.minimum_envy_ratio_lower_bound_from_twoBit_query_transcript_count
      hcard_items identicalTranscript crossTranscript output
      (by
        have hpow : 4 ^ q = 2 ^ (2 * q) := by
          rw [show 4 = 2 ^ 2 by norm_num, pow_mul]
        rw [hpow]
        exact Nat.pow_lt_pow_right (by norm_num : 1 < (2 : ℕ)) hquery_bound)
      hcross_same

theorem minimum_envy_ratio_lower_bound_from_twoBit_fixed_queries_of_two_mul_lt
    {q : ℕ}
    (hcard_items : Fintype.card Item = 2 * k)
    (queries : Fin q → Finset Item)
    (output : QueryTranscript (Bool × Bool) q → Allocation LMMS31Agent Item)
    (hquery_bound : 2 * q < Fintype.card C.Pair) :
    ¬ ∀ choice₁ choice₂,
      MinimumReportEnvyRatioAllocation
        (lmms31CrossReport
          (C.hardFunctionOfMiddleChoice choice₁)
          (C.hardFunctionOfMiddleChoice choice₂))
        (Finset.univ : Finset Item)
        (output
          (twoPlayerHardFunctionQueryTranscript queries
            (C.hardFunctionOfMiddleChoice choice₁)
            (C.hardFunctionOfMiddleChoice choice₂))) := by
  exact
    C.minimum_envy_ratio_lower_bound_from_twoBit_query_count_of_two_mul_lt
      hcard_items
      (fun choice =>
        twoPlayerHardFunctionQueryTranscript queries
          (C.hardFunctionOfMiddleChoice choice)
          (C.hardFunctionOfMiddleChoice choice))
      (fun choice₁ choice₂ =>
        twoPlayerHardFunctionQueryTranscript queries
          (C.hardFunctionOfMiddleChoice choice₁)
          (C.hardFunctionOfMiddleChoice choice₂))
      output hquery_bound
      (by
        intro choice₁ choice₂ hidentical
        exact
          twoPlayerHardFunctionQueryTranscript_swap_eq_of_identical_eq
            queries
            (C.hardFunctionOfMiddleChoice choice₁)
            (C.hardFunctionOfMiddleChoice choice₂)
            hidentical)

end LMMS31MiddleComplementPairs

end Theorem31
end LMMS04FairDivision
