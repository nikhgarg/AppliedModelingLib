import KR21Monoculture.AppendixEFormulaShapes
import KR21Monoculture.AppendixFSourceFormula

/-!
# KR21 literal Mallows source surface

This module gives direct endpoints for the paper's `phi`-parameterized
Mallows model.  The finite development internally uses `q = phi⁻¹`, while
the paper declares `phi > 1` and sets `theta = phi - 1`.  Keeping both
relations in the public theorem statements prevents an audit from crediting a
`q`-only theorem as Equation (8).

For Appendix E, `Candidate n` has `n + 2` elements.  Thus `0 < n` is exactly
the repaired source-cardinality condition `N >= 3`, which is necessary for
the source's strict witnesses.
-/

open scoped BigOperators
open AppliedModelingLib

namespace KR21Monoculture

/--
Equation (8) at the source parameter surface.  With `phi > 1` and
`theta = phi - 1`, the concrete finite law has `q = phi⁻¹` and the normalized
mass `phi^{-d(center, pi)}` appearing in the paper.
-/
theorem source_equation8_concrete_mallows_probability
    {n : ℕ} (center : Ranking n) (phi theta : ℝ)
    (hphi : 1 < phi) (htheta : theta = phi - 1) (pi : Ranking n) :
    let M := concreteMallowsSpec center theta
    M.q = phi⁻¹ ∧
      (M.law pi).toReal =
        phi⁻¹ ^ kendallTau center pi /
          (∑ tau : Ranking n, phi⁻¹ ^ kendallTau center tau) := by
  let M := concreteMallowsSpec center theta
  have htheta_pos : 0 < theta := by
    rw [htheta]
    linarith
  have hq : M.q = phi⁻¹ := by
    change mallowsAccuracyQ theta = phi⁻¹
    rw [mallowsAccuracyQ_eq_of_pos htheta_pos]
    unfold mallowsInverseAccuracyQ
    congr 1
    linarith
  refine ⟨hq, ?_⟩
  rw [M.law_apply_toReal, M.partition_eq_sum, hq]
  rfl

/--
Appendix E (E.2) at the source `phi` surface.  Besides every weak
center-ordered comparison, this supplies the strict source witness.  The
explicit `0 < n` condition means that the source has at least three
candidates; it is not an incidental implementation precondition.
-/
theorem source_appendixE2_concrete_mallows_phi
    {n : ℕ} (center : Ranking n) (phi theta : ℝ)
    (hphi : 1 < phi) (htheta : theta = phi - 1) (hn : 0 < n) :
    let M := concreteMallowsSpec center theta
    (∀ c d : Candidate n, rankOf M.center c < rankOf M.center d →
      AppliedModelingLib.pmfPairConditionalExp M.law M.law disagreementEvent
          (fun pair =>
            if d = firstChoice pair.1 ∧ c = secondChoice pair.1 then (1 : ℝ) else 0) ≤
        AppliedModelingLib.pmfPairConditionalExp M.law M.law disagreementEvent
          (fun pair =>
            if c = firstChoice pair.1 ∧ d = secondChoice pair.1 then (1 : ℝ) else 0)) ∧
      ∃ c d : Candidate n, rankOf M.center c < rankOf M.center d ∧
        AppliedModelingLib.pmfPairConditionalExp M.law M.law disagreementEvent
            (fun pair =>
              if d = firstChoice pair.1 ∧ c = secondChoice pair.1 then (1 : ℝ) else 0) <
          AppliedModelingLib.pmfPairConditionalExp M.law M.law disagreementEvent
            (fun pair =>
              if c = firstChoice pair.1 ∧ d = secondChoice pair.1 then (1 : ℝ) else 0) := by
  let M := concreteMallowsSpec center theta
  have htheta_pos : 0 < theta := by
    rw [htheta]
    linarith
  have hq_lt_one : M.q < 1 := by
    change mallowsAccuracyQ theta < 1
    exact mallowsAccuracyQ_lt_one htheta_pos
  have hE2 : M.AppendixE2PairwiseComparison :=
    M.appendixE2PairwiseComparison_of_rankFactorization
      M.rankFactorization (le_of_lt hq_lt_one)
  have hwitness : M.AppendixE2StrictWitness :=
    M.appendixE2StrictWitness_of_rankFactorization
      M.rankFactorization hn hq_lt_one
  exact ⟨by
      simpa [MallowsSpec.AppendixE2PairwiseComparison,
        MallowsSpec.appendixE2ConditionalTopTwoProbability] using hE2,
    by
      simpa [MallowsSpec.AppendixE2StrictWitness,
        MallowsSpec.appendixE2ConditionalTopTwoProbability] using hwitness⟩

/--
Appendix E (E.3) at the source `phi` surface.  It proves the literal
denominator-cleared product inequality for every ordered pair and derives its
strict source witness from the concrete finite Mallows law, under the same
necessary source-cardinality condition `N >= 3`.
-/
theorem source_appendixE3_concrete_mallows_phi
    {n : ℕ} (center : Ranking n) (phi theta : ℝ)
    (hphi : 1 < phi) (htheta : theta = phi - 1) (hn : 0 < n) :
    let M := concreteMallowsSpec center theta
    (∀ c d : Candidate n, rankOf M.center c < rankOf M.center d →
      0 ≤ M.firstSecondChoiceProb c d * firstChoiceMissProb M.law c -
        M.firstSecondChoiceProb d c * firstChoiceMissProb M.law d) ∧
      ∃ c d : Candidate n, rankOf M.center c < rankOf M.center d ∧
        0 < M.firstSecondChoiceProb c d * firstChoiceMissProb M.law c -
          M.firstSecondChoiceProb d c * firstChoiceMissProb M.law d := by
  let M := concreteMallowsSpec center theta
  have htheta_pos : 0 < theta := by
    rw [htheta]
    linarith
  have hq_lt_one : M.q < 1 := by
    change mallowsAccuracyQ theta < 1
    exact mallowsAccuracyQ_lt_one htheta_pos
  have hE3 : M.AppendixE3PairwiseCrossInequality := by
    intro c d hcd
    exact M.appendixE3CrossDifference_nonneg_of_rankFactorization
      M.rankFactorization (le_of_lt hq_lt_one) hcd
  have hwitness : 0 < M.appendixE3CrossDifference M.centerFirst M.centerSecond :=
    M.appendixE3CrossDifference_centerTopTwo_pos_of_rankFactorization
      M.rankFactorization hn hq_lt_one
  refine ⟨?_, ?_⟩
  · simpa [MallowsSpec.AppendixE3PairwiseCrossInequality,
      MallowsSpec.appendixE3CrossDifference] using hE3
  · refine ⟨M.centerFirst, M.centerSecond, ?_, ?_⟩
    · change
        rankOf (concreteMallowsSpec center theta).center
            (firstChoice (concreteMallowsSpec center theta).center) <
          rankOf (concreteMallowsSpec center theta).center
            (secondChoice (concreteMallowsSpec center theta).center)
      exact rankOf_center_first_lt_second _
    · simpa [MallowsSpec.appendixE3CrossDifference] using hwitness

/--
All three Appendix E source endpoints under the paper's parameter convention.
This combines the literal E.1 conditional gain, E.2 weak comparisons plus a
strict witness, and E.3 product inequalities plus a strict witness without
taking either strict comparison as an assumption.
-/
theorem source_appendixE_concrete_mallows_phi
    {n : ℕ} (center : Ranking n) (phi theta : ℝ)
    (hphi : 1 < phi) (htheta : theta = phi - 1) (hn : 0 < n)
    {value : Candidate n → ℝ} (hvalue : StrictlyOrderedBy center value) :
    let M := concreteMallowsSpec center theta
    0 < AppliedModelingLib.pmfPairConditionalExp M.law M.law disagreementEvent
      (fun pair => value (firstChoice pair.1) - value (secondChoice pair.1)) ∧
    (∀ c d : Candidate n, rankOf M.center c < rankOf M.center d →
      AppliedModelingLib.pmfPairConditionalExp M.law M.law disagreementEvent
          (fun pair =>
            if d = firstChoice pair.1 ∧ c = secondChoice pair.1 then (1 : ℝ) else 0) ≤
        AppliedModelingLib.pmfPairConditionalExp M.law M.law disagreementEvent
          (fun pair =>
            if c = firstChoice pair.1 ∧ d = secondChoice pair.1 then (1 : ℝ) else 0)) ∧
    (∃ c d : Candidate n, rankOf M.center c < rankOf M.center d ∧
      AppliedModelingLib.pmfPairConditionalExp M.law M.law disagreementEvent
          (fun pair =>
            if d = firstChoice pair.1 ∧ c = secondChoice pair.1 then (1 : ℝ) else 0) <
        AppliedModelingLib.pmfPairConditionalExp M.law M.law disagreementEvent
          (fun pair =>
            if c = firstChoice pair.1 ∧ d = secondChoice pair.1 then (1 : ℝ) else 0)) ∧
    (∀ c d : Candidate n, rankOf M.center c < rankOf M.center d →
      0 ≤ M.firstSecondChoiceProb c d * firstChoiceMissProb M.law c -
        M.firstSecondChoiceProb d c * firstChoiceMissProb M.law d) ∧
    ∃ c d : Candidate n, rankOf M.center c < rankOf M.center d ∧
      0 < M.firstSecondChoiceProb c d * firstChoiceMissProb M.law c -
        M.firstSecondChoiceProb d c * firstChoiceMissProb M.law d := by
  let M := concreteMallowsSpec center theta
  have htheta_pos : 0 < theta := by
    rw [htheta]
    linarith
  have hE1 : 0 < M.appendixE1SourceGap value :=
    M.appendixE1SourceGap_pos_of_rankFactorization
      M.rankFactorization hn (mallowsAccuracyQ_lt_one htheta_pos) hvalue
  have hE2 := source_appendixE2_concrete_mallows_phi center phi theta
    hphi htheta hn
  have hE3 := source_appendixE3_concrete_mallows_phi center phi theta
    hphi htheta hn
  refine ⟨?_, hE2.1, hE2.2, hE3.1, hE3.2⟩
  simpa [MallowsSpec.appendixE1SourceGap] using hE1

end KR21Monoculture
