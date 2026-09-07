import KR21Monoculture.RUM
import AppliedModelingLib.Foundations.Probability.Weighted

open AppliedModelingLib

namespace KR21Monoculture

/-!
# Appendix B: exact finite RUM counterexamples

This file records exact finite specializations of the two three-candidate
counterexamples in Appendix B of Kleinberg--Raghavan (2021).

The paper presents the examples as iid discrete-noise RUMs and observes that
their atoms may be replaced by tightly concentrated Gaussian components.  The
definitions below instantiate the one-coordinate noise laws at `delta = 1/10`,
form the three-coordinate iid product weights, rank the resulting realized
scores, and prove that the exact pushforward masses are the six ranking weights
used in the utility calculations.  Thus the counterexamples are checked from
the source RUM primitives rather than assumed as ranking-law certificates.

The discrete laws intentionally do not satisfy Definition 1.  This file does
not formalize the source's separate smoothing remark.
-/

/-- The six possible rankings of three candidates, named in one-line notation. -/
inductive AppendixBRankingAtom where
  | r012
  | r021
  | r102
  | r120
  | r201
  | r210
  deriving DecidableEq, Fintype

namespace AppendixBRankingAtom

/-- Interpret an Appendix B atom as the corresponding three-candidate ranking. -/
def toRanking : AppendixBRankingAtom → Ranking 1
  | r012 => rum3Ranking012
  | r021 => rum3Ranking021
  | r102 => rum3Ranking102
  | r120 => rum3Ranking120
  | r201 => rum3Ranking201
  | r210 => rum3Ranking210

/-- Expand a finite sum over the six named ranking atoms. -/
theorem sum_six (f : AppendixBRankingAtom → ℝ) :
    (∑ a : AppendixBRankingAtom, f a) =
      f r012 + f r021 + f r102 + f r120 + f r201 + f r210 := by
  classical
  have huniv :
      (Finset.univ : Finset AppendixBRankingAtom) =
        {r012, r021, r102, r120, r201, r210} := by
    ext a
    cases a <;> simp
  simp [huniv, add_assoc]

/- Constructor disequalities are named explicitly so the large exact
pushforward reductions do not repeatedly invoke generic no-confusion. -/
@[simp] theorem r012_ne_r021 : r012 ≠ r021 := by decide
@[simp] theorem r021_ne_r012 : r021 ≠ r012 := by decide
@[simp] theorem r012_ne_r102 : r012 ≠ r102 := by decide
@[simp] theorem r102_ne_r012 : r102 ≠ r012 := by decide
@[simp] theorem r012_ne_r120 : r012 ≠ r120 := by decide
@[simp] theorem r120_ne_r012 : r120 ≠ r012 := by decide
@[simp] theorem r012_ne_r201 : r012 ≠ r201 := by decide
@[simp] theorem r201_ne_r012 : r201 ≠ r012 := by decide
@[simp] theorem r012_ne_r210 : r012 ≠ r210 := by decide
@[simp] theorem r210_ne_r012 : r210 ≠ r012 := by decide
@[simp] theorem r021_ne_r102 : r021 ≠ r102 := by decide
@[simp] theorem r102_ne_r021 : r102 ≠ r021 := by decide
@[simp] theorem r021_ne_r120 : r021 ≠ r120 := by decide
@[simp] theorem r120_ne_r021 : r120 ≠ r021 := by decide
@[simp] theorem r021_ne_r201 : r021 ≠ r201 := by decide
@[simp] theorem r201_ne_r021 : r201 ≠ r021 := by decide
@[simp] theorem r021_ne_r210 : r021 ≠ r210 := by decide
@[simp] theorem r210_ne_r021 : r210 ≠ r021 := by decide
@[simp] theorem r102_ne_r120 : r102 ≠ r120 := by decide
@[simp] theorem r120_ne_r102 : r120 ≠ r102 := by decide
@[simp] theorem r102_ne_r201 : r102 ≠ r201 := by decide
@[simp] theorem r201_ne_r102 : r201 ≠ r102 := by decide
@[simp] theorem r102_ne_r210 : r102 ≠ r210 := by decide
@[simp] theorem r210_ne_r102 : r210 ≠ r102 := by decide
@[simp] theorem r120_ne_r201 : r120 ≠ r201 := by decide
@[simp] theorem r201_ne_r120 : r201 ≠ r120 := by decide
@[simp] theorem r120_ne_r210 : r120 ≠ r210 := by decide
@[simp] theorem r210_ne_r120 : r210 ≠ r120 := by decide
@[simp] theorem r201_ne_r210 : r201 ≠ r210 := by decide
@[simp] theorem r210_ne_r201 : r210 ≠ r201 := by decide

end AppendixBRankingAtom

open AppendixBRankingAtom

/-!
## A transparent three-score pushforward

`appendixBRankingAtomOfScores` is the six-valued version of
`rum3RankByScores`.  Keeping this map transparent lets the exact iid product
enumerations reduce without taking an unproved ranking-law table as input.
-/

/-- Classify three realized scores by their weakly decreasing ranking. -/
noncomputable def appendixBRankingAtomOfScores
    (s0 s1 s2 : ℝ) : AppendixBRankingAtom :=
  if s1 ≤ s0 ∧ s2 ≤ s0 then
    if s2 ≤ s1 then .r012 else .r021
  else if s0 < s1 ∧ s2 ≤ s1 then
    if s2 ≤ s0 then .r102 else .r120
  else
    if s1 ≤ s0 then .r201 else .r210

/-- The transparent atom classifier is exactly the paper's score ranking. -/
theorem appendixBRankingAtomOfScores_toRanking
    (s0 s1 s2 : ℝ) :
    (appendixBRankingAtomOfScores s0 s1 s2).toRanking =
      rum3RankByScores s0 s1 s2 := by
  unfold appendixBRankingAtomOfScores rum3RankByScores
    AppliedModelingLib.SocialChoice.Ranking.rum3RankByScores
  split_ifs <;> rfl

/-! ## Appendix B.1: violation of Definition 2 -/

/-- The three atoms of the Appendix B.1 one-coordinate noise law. -/
inductive AppendixB1NoiseAtom where
  | plusOne
  | zero
  | minusOne
  deriving DecidableEq, Fintype

namespace AppendixB1NoiseAtom

/-- Expand a finite sum over the three B.1 noise atoms. -/
theorem sum_three (f : AppendixB1NoiseAtom → ℝ) :
    (∑ e : AppendixB1NoiseAtom, f e) =
      f plusOne + f zero + f minusOne := by
  classical
  have huniv :
      (Finset.univ : Finset AppendixB1NoiseAtom) =
        {plusOne, zero, minusOne} := by
    ext e
    cases e <;> simp
  simp [huniv, add_assoc]

end AppendixB1NoiseAtom

/-- The source's scaled noise values `epsilon/theta` in Appendix B.1. -/
def appendixB1NoiseValue : AppendixB1NoiseAtom → ℝ
  | .plusOne => 1
  | .zero => 0
  | .minusOne => -1

/-- The source masses at `delta=1/10`: `delta/2, 1-delta, delta/2`. -/
noncomputable def appendixB1NoiseWeight : AppendixB1NoiseAtom → ℝ
  | .plusOne => 1 / 20
  | .zero => 9 / 10
  | .minusOne => 1 / 20

theorem appendixB1NoiseWeight_sum :
    (∑ e : AppendixB1NoiseAtom, appendixB1NoiseWeight e) = 1 := by
  rw [AppendixB1NoiseAtom.sum_three]
  norm_num [appendixB1NoiseWeight]

/--
The iid product mass pushed through the source's realized-score ranking.
Candidate values are `(7/4,1/2,0)` and every coordinate uses the same noise
law.
-/
noncomputable def appendixB1IIDRUMRankingWeight
    (a : AppendixBRankingAtom) : ℝ :=
  ∑ e0 : AppendixB1NoiseAtom,
    ∑ e1 : AppendixB1NoiseAtom,
      ∑ e2 : AppendixB1NoiseAtom,
        if appendixBRankingAtomOfScores
            (7 / 4 + appendixB1NoiseValue e0)
            (1 / 2 + appendixB1NoiseValue e1)
            (appendixB1NoiseValue e2) = a then
          appendixB1NoiseWeight e0 * appendixB1NoiseWeight e1 *
            appendixB1NoiseWeight e2
        else 0

/--
The exact ranking masses induced by Appendix B.1 at
`(x₁,x₂,x₃) = (7/4,1/2,0)` and `delta = 1/10`.

The underlying scaled-noise atoms are `1, 0, -1` with respective masses
`delta/2, 1-delta, delta/2`.  The omitted ranking `210` has zero mass.
-/
noncomputable def appendixB1RankingWeight : AppendixBRankingAtom → ℝ
  | r012 => 181 / 200
  | r021 => 721 / 8000
  | r102 => 19 / 8000
  | r120 => 1 / 8000
  | r201 => 19 / 8000
  | r210 => 0

/--
The displayed B.1 ranking table is the exact pushforward of three iid source
noise draws through the realized-score ranking.
-/
theorem appendixB1RankingWeight_eq_iid_rum_pushforward
    (a : AppendixBRankingAtom) :
    appendixB1RankingWeight a = appendixB1IIDRUMRankingWeight a := by
  cases a <;>
    simp [appendixB1IIDRUMRankingWeight, AppendixB1NoiseAtom.sum_three,
      appendixBRankingAtomOfScores, appendixB1NoiseValue,
      appendixB1NoiseWeight, appendixB1RankingWeight] <;>
    norm_num [Fin.ext_iff]

private theorem appendixB1RankingWeight_nonneg
    (a : AppendixBRankingAtom) : 0 ≤ appendixB1RankingWeight a := by
  cases a <;> norm_num [appendixB1RankingWeight]

theorem appendixB1RankingWeight_sum :
    (∑ a : AppendixBRankingAtom, appendixB1RankingWeight a) = 1 := by
  rw [AppendixBRankingAtom.sum_six]
  norm_num [appendixB1RankingWeight]

private theorem appendixB1RankingWeight_sum_pos :
    0 < ∑ a : AppendixBRankingAtom, appendixB1RankingWeight a := by
  rw [appendixB1RankingWeight_sum]
  norm_num

/-- The six-atom source enumeration before mapping atoms to rankings. -/
noncomputable def appendixB1AtomPMF : PMF AppendixBRankingAtom :=
  AppliedModelingLib.finiteWeightedPMF
    appendixB1RankingWeight appendixB1RankingWeight_nonneg
    appendixB1RankingWeight_sum_pos

/-- The exact three-candidate ranking PMF for the Appendix B.1 witness. -/
noncomputable def appendixB1RankingPMF : PMF (Ranking 1) :=
  appendixB1AtomPMF.map AppendixBRankingAtom.toRanking

/-- The paper's concrete candidate values `(7/4, 1/2, 0)`. -/
noncomputable def appendixB1Value (c : Candidate 1) : ℝ :=
  if c = 0 then 7 / 4 else if c = 1 then 1 / 2 else 0

/-- Exact utility of the second mover when the ranking draw is shared. -/
theorem appendixB1_expectedSecondMoverShared_eq :
    expectedSecondMoverShared appendixB1RankingPMF appendixB1Value =
      7373 / 16000 := by
  unfold expectedSecondMoverShared appendixB1RankingPMF
  rw [AppliedModelingLib.pmfExp_map]
  unfold appendixB1AtomPMF
  rw [AppliedModelingLib.finiteWeightedPMF_pmfExp_eq_sum_div]
  simp_rw [AppendixBRankingAtom.sum_six]
  norm_num [appendixB1RankingWeight, AppendixBRankingAtom.toRanking,
    appendixB1Value, secondChoice, Fin.ext_iff]

/-- Exact utility of the second mover under an independent reranking. -/
theorem appendixB1_expectedSecondMoverIndependent_eq :
    expectedSecondMoverIndependent
        appendixB1RankingPMF appendixB1RankingPMF appendixB1Value =
      5888651 / 12800000 := by
  unfold expectedSecondMoverIndependent pmfPairExp appendixB1RankingPMF
  rw [AppliedModelingLib.pmfExp_map]
  simp_rw [AppliedModelingLib.pmfExp_map]
  unfold appendixB1AtomPMF
  simp_rw [AppliedModelingLib.finiteWeightedPMF_pmfExp_eq_sum_div]
  simp_rw [AppendixBRankingAtom.sum_six]
  norm_num [appendixB1RankingWeight, AppendixBRankingAtom.toRanking,
    appendixB1Value, secondMoverUtility, bestRemainingAfter, firstChoice,
    secondChoice, Fin.ext_iff]

/--
Appendix B.1 exact sign reversal.  Independent reranking lowers the second
mover's utility by `9749 / 12800000`, matching the paper's decimal `-0.00076`.
-/
theorem appendixB1_definition2_reversal_exact :
    expectedSecondMoverIndependent
          appendixB1RankingPMF appendixB1RankingPMF appendixB1Value -
        expectedSecondMoverShared appendixB1RankingPMF appendixB1Value =
      -(9749 / 12800000 : ℝ) := by
  rw [appendixB1_expectedSecondMoverIndependent_eq,
    appendixB1_expectedSecondMoverShared_eq]
  norm_num

/-- The concrete Appendix B.1 ranking law violates Definition 2. -/
theorem appendixB1_not_prefersIndependentReranking :
    ¬ Model.PrefersIndependentReranking
      appendixB1RankingPMF appendixB1Value := by
  intro h
  unfold Model.PrefersIndependentReranking
    AppliedModelingLib.SocialChoice.Ranking.PrefersIndependentReranking at h
  rw [appendixB1_expectedSecondMoverShared_eq,
    appendixB1_expectedSecondMoverIndependent_eq] at h
  norm_num at h

/-! ## Appendix B.2: violation of Definition 3 -/

/-- The four atoms of the Appendix B.2 one-coordinate base noise law. -/
inductive AppendixB2NoiseAtom where
  | plusOne
  | minusOne
  | plusTen
  | minusTen
  deriving DecidableEq, Fintype

namespace AppendixB2NoiseAtom

/-- Expand a finite sum over the four B.2 noise atoms. -/
theorem sum_four (f : AppendixB2NoiseAtom → ℝ) :
    (∑ e : AppendixB2NoiseAtom, f e) =
      f plusOne + f minusOne + f plusTen + f minusTen := by
  classical
  have huniv :
      (Finset.univ : Finset AppendixB2NoiseAtom) =
        {plusOne, minusOne, plusTen, minusTen} := by
    ext e
    cases e <;> simp
  simp [huniv, add_assoc]

end AppendixB2NoiseAtom

/-- The source's four base values of `epsilon/theta`. -/
def appendixB2NoiseValue : AppendixB2NoiseAtom → ℝ
  | .plusOne => 1
  | .minusOne => -1
  | .plusTen => 10
  | .minusTen => -10

/-- The source masses at `delta=1/10`. -/
noncomputable def appendixB2NoiseWeight : AppendixB2NoiseAtom → ℝ
  | .plusOne => 9 / 20
  | .minusOne => 9 / 20
  | .plusTen => 1 / 20
  | .minusTen => 1 / 20

theorem appendixB2NoiseWeight_sum :
    (∑ e : AppendixB2NoiseAtom, appendixB2NoiseWeight e) = 1 := by
  rw [AppendixB2NoiseAtom.sum_four]
  norm_num [appendixB2NoiseWeight]

/--
The iid B.2 product mass under the algorithmic accuracy
`theta_A = 1.1 theta`.  Hence a base draw `epsilon/theta` is multiplied by
`10/11` in the realized score.
-/
noncomputable def appendixB2AlgorithmIIDRUMRankingWeight
    (a : AppendixBRankingAtom) : ℝ :=
  ∑ e0 : AppendixB2NoiseAtom,
    ∑ e1 : AppendixB2NoiseAtom,
      ∑ e2 : AppendixB2NoiseAtom,
        if appendixBRankingAtomOfScores
            (3 + (10 / 11) * appendixB2NoiseValue e0)
            (2 + (10 / 11) * appendixB2NoiseValue e1)
            ((10 / 11) * appendixB2NoiseValue e2) = a then
          appendixB2NoiseWeight e0 * appendixB2NoiseWeight e1 *
            appendixB2NoiseWeight e2
        else 0

/--
The iid B.2 product mass under the human accuracy `theta_H = 0.9 theta`.
Hence a base draw `epsilon/theta` is multiplied by `10/9`.
-/
noncomputable def appendixB2HumanIIDRUMRankingWeight
    (a : AppendixBRankingAtom) : ℝ :=
  ∑ e0 : AppendixB2NoiseAtom,
    ∑ e1 : AppendixB2NoiseAtom,
      ∑ e2 : AppendixB2NoiseAtom,
        if appendixBRankingAtomOfScores
            (3 + (10 / 9) * appendixB2NoiseValue e0)
            (2 + (10 / 9) * appendixB2NoiseValue e1)
            ((10 / 9) * appendixB2NoiseValue e2) = a then
          appendixB2NoiseWeight e0 * appendixB2NoiseWeight e1 *
            appendixB2NoiseWeight e2
        else 0

/--
The algorithmic ranking masses in Appendix B.2 for `delta = 1/10` and
`theta_A = 1.1 theta`.
-/
noncomputable def appendixB2AlgorithmRankingWeight : AppendixBRankingAtom → ℝ
  | r012 => 4999 / 8000
  | r021 => 361 / 8000
  | r102 => 19 / 80
  | r120 => 361 / 8000
  | r201 => 7 / 200
  | r210 => 99 / 8000

/--
The human ranking masses in Appendix B.2 for `delta = 1/10` and
`theta_H = 0.9 theta`.
-/
noncomputable def appendixB2HumanRankingWeight : AppendixBRankingAtom → ℝ
  | r012 => 173 / 400
  | r021 => 19 / 80
  | r102 => 19 / 80
  | r120 => 7 / 200
  | r201 => 7 / 200
  | r210 => 9 / 400

/-- The algorithmic B.2 ranking table is its exact iid-RUM pushforward. -/
theorem appendixB2AlgorithmRankingWeight_eq_iid_rum_pushforward
    (a : AppendixBRankingAtom) :
    appendixB2AlgorithmRankingWeight a =
      appendixB2AlgorithmIIDRUMRankingWeight a := by
  cases a <;>
    simp [appendixB2AlgorithmIIDRUMRankingWeight,
      AppendixB2NoiseAtom.sum_four, appendixBRankingAtomOfScores,
      appendixB2NoiseValue, appendixB2NoiseWeight,
      appendixB2AlgorithmRankingWeight] <;>
    norm_num [Fin.ext_iff]

/-- The human B.2 ranking table is its exact iid-RUM pushforward. -/
theorem appendixB2HumanRankingWeight_eq_iid_rum_pushforward
    (a : AppendixBRankingAtom) :
    appendixB2HumanRankingWeight a =
      appendixB2HumanIIDRUMRankingWeight a := by
  cases a <;>
    simp [appendixB2HumanIIDRUMRankingWeight,
      AppendixB2NoiseAtom.sum_four, appendixBRankingAtomOfScores,
      appendixB2NoiseValue, appendixB2NoiseWeight,
      appendixB2HumanRankingWeight] <;>
    norm_num [Fin.ext_iff]

private theorem appendixB2AlgorithmRankingWeight_nonneg
    (a : AppendixBRankingAtom) : 0 ≤ appendixB2AlgorithmRankingWeight a := by
  cases a <;> norm_num [appendixB2AlgorithmRankingWeight]

private theorem appendixB2HumanRankingWeight_nonneg
    (a : AppendixBRankingAtom) : 0 ≤ appendixB2HumanRankingWeight a := by
  cases a <;> norm_num [appendixB2HumanRankingWeight]

theorem appendixB2AlgorithmRankingWeight_sum :
    (∑ a : AppendixBRankingAtom, appendixB2AlgorithmRankingWeight a) = 1 := by
  rw [AppendixBRankingAtom.sum_six]
  norm_num [appendixB2AlgorithmRankingWeight]

theorem appendixB2HumanRankingWeight_sum :
    (∑ a : AppendixBRankingAtom, appendixB2HumanRankingWeight a) = 1 := by
  rw [AppendixBRankingAtom.sum_six]
  norm_num [appendixB2HumanRankingWeight]

private theorem appendixB2AlgorithmRankingWeight_sum_pos :
    0 < ∑ a : AppendixBRankingAtom, appendixB2AlgorithmRankingWeight a := by
  rw [appendixB2AlgorithmRankingWeight_sum]
  norm_num

private theorem appendixB2HumanRankingWeight_sum_pos :
    0 < ∑ a : AppendixBRankingAtom, appendixB2HumanRankingWeight a := by
  rw [appendixB2HumanRankingWeight_sum]
  norm_num

noncomputable def appendixB2AlgorithmAtomPMF : PMF AppendixBRankingAtom :=
  AppliedModelingLib.finiteWeightedPMF
    appendixB2AlgorithmRankingWeight appendixB2AlgorithmRankingWeight_nonneg
    appendixB2AlgorithmRankingWeight_sum_pos

noncomputable def appendixB2HumanAtomPMF : PMF AppendixBRankingAtom :=
  AppliedModelingLib.finiteWeightedPMF
    appendixB2HumanRankingWeight appendixB2HumanRankingWeight_nonneg
    appendixB2HumanRankingWeight_sum_pos

/-- The more accurate (`theta_A`) ranking law in the Appendix B.2 witness. -/
noncomputable def appendixB2AlgorithmRankingPMF : PMF (Ranking 1) :=
  appendixB2AlgorithmAtomPMF.map AppendixBRankingAtom.toRanking

/-- The less accurate (`theta_H`) ranking law in the Appendix B.2 witness. -/
noncomputable def appendixB2HumanRankingPMF : PMF (Ranking 1) :=
  appendixB2HumanAtomPMF.map AppendixBRankingAtom.toRanking

/-- The paper's concrete candidate values `(3, 2, 0)`. -/
def appendixB2Value (c : Candidate 1) : ℝ :=
  if c = 0 then 3 else if c = 1 then 2 else 0

theorem appendixB2_algorithm_firstChoice_x1_eq :
    firstChoiceProb appendixB2AlgorithmRankingPMF (0 : Candidate 1) =
      67 / 100 := by
  unfold firstChoiceProb AppliedModelingLib.SocialChoice.Ranking.firstChoiceProb
    AppliedModelingLib.pmfProb appendixB2AlgorithmRankingPMF
  rw [AppliedModelingLib.pmfExp_map]
  unfold appendixB2AlgorithmAtomPMF
  rw [AppliedModelingLib.finiteWeightedPMF_pmfExp_eq_sum_div]
  simp_rw [AppendixBRankingAtom.sum_six]
  norm_num [appendixB2AlgorithmRankingWeight,
    AppendixBRankingAtom.toRanking, firstChoice, Fin.ext_iff]

theorem appendixB2_human_firstChoice_x1_eq :
    firstChoiceProb appendixB2HumanRankingPMF (0 : Candidate 1) =
      67 / 100 := by
  unfold firstChoiceProb AppliedModelingLib.SocialChoice.Ranking.firstChoiceProb
    AppliedModelingLib.pmfProb appendixB2HumanRankingPMF
  rw [AppliedModelingLib.pmfExp_map]
  unfold appendixB2HumanAtomPMF
  rw [AppliedModelingLib.finiteWeightedPMF_pmfExp_eq_sum_div]
  simp_rw [AppendixBRankingAtom.sum_six]
  norm_num [appendixB2HumanRankingWeight,
    AppendixBRankingAtom.toRanking, firstChoice, Fin.ext_iff]

/-- Equation (B.1): the two laws choose `x₁` first with equal probability. -/
theorem appendixB2_equation_B1 :
    firstChoiceProb appendixB2AlgorithmRankingPMF (0 : Candidate 1) =
      firstChoiceProb appendixB2HumanRankingPMF (0 : Candidate 1) := by
  rw [appendixB2_algorithm_firstChoice_x1_eq,
    appendixB2_human_firstChoice_x1_eq]

theorem appendixB2_algorithm_firstChoice_x2_eq :
    firstChoiceProb appendixB2AlgorithmRankingPMF (1 : Candidate 1) =
      2261 / 8000 := by
  unfold firstChoiceProb AppliedModelingLib.SocialChoice.Ranking.firstChoiceProb
    AppliedModelingLib.pmfProb appendixB2AlgorithmRankingPMF
  rw [AppliedModelingLib.pmfExp_map]
  unfold appendixB2AlgorithmAtomPMF
  rw [AppliedModelingLib.finiteWeightedPMF_pmfExp_eq_sum_div]
  simp_rw [AppendixBRankingAtom.sum_six]
  norm_num [appendixB2AlgorithmRankingWeight,
    AppendixBRankingAtom.toRanking, firstChoice, Fin.ext_iff]

theorem appendixB2_human_firstChoice_x2_eq :
    firstChoiceProb appendixB2HumanRankingPMF (1 : Candidate 1) =
      109 / 400 := by
  unfold firstChoiceProb AppliedModelingLib.SocialChoice.Ranking.firstChoiceProb
    AppliedModelingLib.pmfProb appendixB2HumanRankingPMF
  rw [AppliedModelingLib.pmfExp_map]
  unfold appendixB2HumanAtomPMF
  rw [AppliedModelingLib.finiteWeightedPMF_pmfExp_eq_sum_div]
  simp_rw [AppendixBRankingAtom.sum_six]
  norm_num [appendixB2HumanRankingWeight,
    AppendixBRankingAtom.toRanking, firstChoice, Fin.ext_iff]

/-- Equation (B.2): the more accurate law chooses `x₂` first more often. -/
theorem appendixB2_equation_B2 :
    firstChoiceProb appendixB2HumanRankingPMF (1 : Candidate 1) <
      firstChoiceProb appendixB2AlgorithmRankingPMF (1 : Candidate 1) := by
  rw [appendixB2_human_firstChoice_x2_eq,
    appendixB2_algorithm_firstChoice_x2_eq]
  norm_num

/--
The source's `u_{-2}`: exact human utility when candidate `x₂` is unavailable.
-/
theorem appendixB2_human_expectedBestAfter_x2_eq :
    AccuracyFamily.expectedBestAfterRemoval
        appendixB2HumanRankingPMF appendixB2Value (1 : Candidate 1) =
      1089 / 400 := by
  unfold AccuracyFamily.expectedBestAfterRemoval appendixB2HumanRankingPMF
  rw [AppliedModelingLib.pmfExp_map]
  unfold appendixB2HumanAtomPMF
  rw [AppliedModelingLib.finiteWeightedPMF_pmfExp_eq_sum_div]
  simp_rw [AppendixBRankingAtom.sum_six]
  norm_num [appendixB2HumanRankingWeight, AppendixBRankingAtom.toRanking,
    appendixB2Value, bestRemainingAfter, Fin.ext_iff]

/--
The source's `u_{-3}`: exact human utility when candidate `x₃` is unavailable.
-/
theorem appendixB2_human_expectedBestAfter_x3_eq :
    AccuracyFamily.expectedBestAfterRemoval
        appendixB2HumanRankingPMF appendixB2Value (2 : Candidate 1) =
      541 / 200 := by
  unfold AccuracyFamily.expectedBestAfterRemoval appendixB2HumanRankingPMF
  rw [AppliedModelingLib.pmfExp_map]
  unfold appendixB2HumanAtomPMF
  rw [AppliedModelingLib.finiteWeightedPMF_pmfExp_eq_sum_div]
  simp_rw [AppendixBRankingAtom.sum_six]
  norm_num [appendixB2HumanRankingWeight, AppendixBRankingAtom.toRanking,
    appendixB2Value, bestRemainingAfter, Fin.ext_iff]

/-- The exact source comparison `u_{-2} - u_{-3} = 7/400 > 0`. -/
theorem appendixB2_human_prefers_x2_unavailable_exact :
    AccuracyFamily.expectedBestAfterRemoval
          appendixB2HumanRankingPMF appendixB2Value (1 : Candidate 1) -
        AccuracyFamily.expectedBestAfterRemoval
          appendixB2HumanRankingPMF appendixB2Value (2 : Candidate 1) =
      7 / 400 := by
  rw [appendixB2_human_expectedBestAfter_x2_eq,
    appendixB2_human_expectedBestAfter_x3_eq]
  norm_num

theorem appendixB2_human_prefers_x2_unavailable :
    AccuracyFamily.expectedBestAfterRemoval
        appendixB2HumanRankingPMF appendixB2Value (2 : Candidate 1) <
      AccuracyFamily.expectedBestAfterRemoval
        appendixB2HumanRankingPMF appendixB2Value (1 : Candidate 1) := by
  rw [appendixB2_human_expectedBestAfter_x2_eq,
    appendixB2_human_expectedBestAfter_x3_eq]
  norm_num

/-- Exact human utility when the first mover also uses the human law. -/
theorem appendixB2_expectedSecondMover_human_human_eq :
    expectedSecondMoverIndependent
        appendixB2HumanRankingPMF appendixB2HumanRankingPMF appendixB2Value =
      294739 / 160000 := by
  unfold expectedSecondMoverIndependent pmfPairExp
    appendixB2HumanRankingPMF
  rw [AppliedModelingLib.pmfExp_map]
  simp_rw [AppliedModelingLib.pmfExp_map]
  unfold appendixB2HumanAtomPMF
  simp_rw [AppliedModelingLib.finiteWeightedPMF_pmfExp_eq_sum_div]
  simp_rw [AppendixBRankingAtom.sum_six]
  norm_num [appendixB2HumanRankingWeight, AppendixBRankingAtom.toRanking,
    appendixB2Value, secondMoverUtility, bestRemainingAfter, firstChoice,
    secondChoice, Fin.ext_iff]

/-- Exact human utility when the first mover uses the algorithmic law. -/
theorem appendixB2_expectedSecondMover_human_algorithm_eq :
    expectedSecondMoverIndependent
        appendixB2HumanRankingPMF appendixB2AlgorithmRankingPMF appendixB2Value =
      5895347 / 3200000 := by
  unfold expectedSecondMoverIndependent pmfPairExp
    appendixB2HumanRankingPMF appendixB2AlgorithmRankingPMF
  rw [AppliedModelingLib.pmfExp_map]
  simp_rw [AppliedModelingLib.pmfExp_map]
  unfold appendixB2HumanAtomPMF appendixB2AlgorithmAtomPMF
  simp_rw [AppliedModelingLib.finiteWeightedPMF_pmfExp_eq_sum_div]
  simp_rw [AppendixBRankingAtom.sum_six]
  norm_num [appendixB2HumanRankingWeight, appendixB2AlgorithmRankingWeight,
    AppendixBRankingAtom.toRanking, appendixB2Value, secondMoverUtility,
    bestRemainingAfter, firstChoice, secondChoice, Fin.ext_iff]

/--
Appendix B.2 exact sign reversal: facing the more accurate first mover raises
the human second mover's utility by `567 / 3200000`.
-/
theorem appendixB2_definition3_reversal_exact :
    expectedSecondMoverIndependent
          appendixB2HumanRankingPMF appendixB2AlgorithmRankingPMF appendixB2Value -
        expectedSecondMoverIndependent
          appendixB2HumanRankingPMF appendixB2HumanRankingPMF appendixB2Value =
      567 / 3200000 := by
  rw [appendixB2_expectedSecondMover_human_algorithm_eq,
    appendixB2_expectedSecondMover_human_human_eq]
  norm_num

/-- The concrete Appendix B.2 ranking laws violate Definition 3. -/
theorem appendixB2_not_prefersWeakerCompetition :
    ¬ Model.PrefersWeakerCompetition
      appendixB2AlgorithmRankingPMF appendixB2HumanRankingPMF appendixB2Value := by
  intro h
  unfold Model.PrefersWeakerCompetition
    AppliedModelingLib.SocialChoice.Ranking.PrefersWeakerCompetition at h
  rw [appendixB2_expectedSecondMover_human_algorithm_eq,
    appendixB2_expectedSecondMover_human_human_eq] at h
  norm_num at h

end KR21Monoculture
