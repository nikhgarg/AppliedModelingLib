import KR21Monoculture.Kendall
import KR21Monoculture.WelfareDecomposition
import Mathlib.Tactic.NormNum

open AppliedModelingLib

namespace KR21Monoculture

/-!
# Rank-reduced three-firm witness arithmetic

This file evaluates a finite rank-mean reduction motivated by the paper's
three-firm computational example (`n = 4`, `k = 3`, `phi_A = 2`, and
`phi_H = 7/4`). It fixes named ranking tables, inverse Mallows parameters, and
a uniform law over six named firm orders.

The order-statistic means and the equality between this reduced evaluator and
the paper's Uniform-value experiment are pending source-model bridges. The
results below therefore certify collapsed finite arithmetic, not the source
experiment itself.
-/

/-! ## Executable finite model -/

abbrev SourceFourCandidate := Fin 4
abbrev SourceThreeFirm := Fin 3

/-- The 24 four-candidate rankings, represented without proof-bearing
permutation records so exact kernel evaluation remains reducible. -/
inductive SourceFourRanking where
  | r0123 | r0132 | r0213 | r0231 | r0312 | r0321
  | r1023 | r1032 | r1203 | r1230 | r1302 | r1320
  | r2013 | r2031 | r2103 | r2130 | r2301 | r2310
  | r3012 | r3021 | r3102 | r3120 | r3201 | r3210
  deriving DecidableEq, Fintype

/-- Candidate in a given slot of a named four-candidate ranking. -/
def sourceFourRankingAt : SourceFourRanking → SourceFourCandidate → SourceFourCandidate
  | .r0123 => ![0, 1, 2, 3]
  | .r0132 => ![0, 1, 3, 2]
  | .r0213 => ![0, 2, 1, 3]
  | .r0231 => ![0, 2, 3, 1]
  | .r0312 => ![0, 3, 1, 2]
  | .r0321 => ![0, 3, 2, 1]
  | .r1023 => ![1, 0, 2, 3]
  | .r1032 => ![1, 0, 3, 2]
  | .r1203 => ![1, 2, 0, 3]
  | .r1230 => ![1, 2, 3, 0]
  | .r1302 => ![1, 3, 0, 2]
  | .r1320 => ![1, 3, 2, 0]
  | .r2013 => ![2, 0, 1, 3]
  | .r2031 => ![2, 0, 3, 1]
  | .r2103 => ![2, 1, 0, 3]
  | .r2130 => ![2, 1, 3, 0]
  | .r2301 => ![2, 3, 0, 1]
  | .r2310 => ![2, 3, 1, 0]
  | .r3012 => ![3, 0, 1, 2]
  | .r3021 => ![3, 0, 2, 1]
  | .r3102 => ![3, 1, 0, 2]
  | .r3120 => ![3, 1, 2, 0]
  | .r3201 => ![3, 2, 0, 1]
  | .r3210 => ![3, 2, 1, 0]

instance : CoeFun SourceFourRanking
    (fun _ => SourceFourCandidate → SourceFourCandidate) :=
  ⟨sourceFourRankingAt⟩

namespace SourceFourRanking

/-- Expand a finite sum over the 24 named four-candidate rankings. -/
theorem sum_twenty_four (f : SourceFourRanking → ℚ) :
    (∑ pi : SourceFourRanking, f pi) =
      f .r0123 + f .r0132 + f .r0213 + f .r0231 + f .r0312 + f .r0321 +
      f .r1023 + f .r1032 + f .r1203 + f .r1230 + f .r1302 + f .r1320 +
      f .r2013 + f .r2031 + f .r2103 + f .r2130 + f .r2301 + f .r2310 +
      f .r3012 + f .r3021 + f .r3102 + f .r3120 + f .r3201 + f .r3210 := by
  classical
  have huniv :
      (Finset.univ : Finset SourceFourRanking) =
        {.r0123, .r0132, .r0213, .r0231, .r0312, .r0321,
          .r1023, .r1032, .r1203, .r1230, .r1302, .r1320,
          .r2013, .r2031, .r2103, .r2130, .r2301, .r2310,
          .r3012, .r3021, .r3102, .r3120, .r3201, .r3210} := by
    ext pi
    cases pi <;> simp
  simp [huniv, add_assoc]

end SourceFourRanking

/-- The six possible orders of the three firms. -/
inductive SourceFirmOrder where
  | f012 | f021 | f102 | f120 | f201 | f210
  deriving DecidableEq, Fintype

def sourceFirmOrderAt : SourceFirmOrder → SourceThreeFirm → SourceThreeFirm
  | .f012 => ![0, 1, 2]
  | .f021 => ![0, 2, 1]
  | .f102 => ![1, 0, 2]
  | .f120 => ![1, 2, 0]
  | .f201 => ![2, 0, 1]
  | .f210 => ![2, 1, 0]

instance : CoeFun SourceFirmOrder
    (fun _ => SourceThreeFirm → SourceThreeFirm) :=
  ⟨sourceFirmOrderAt⟩

namespace SourceFirmOrder

/-- Expand a finite sum over the six named firm orders. -/
theorem sum_six (f : SourceFirmOrder → ℚ) :
    (∑ order : SourceFirmOrder, f order) =
      f .f012 + f .f021 + f .f102 + f .f120 + f .f201 + f .f210 := by
  classical
  have huniv :
      (Finset.univ : Finset SourceFirmOrder) =
        {.f012, .f021, .f102, .f120, .f201, .f210} := by
    ext order
    cases order <;> simp
  simp [huniv, add_assoc]

end SourceFirmOrder

/-- Pair-enumeration definition of Kendall inversions relative to the identity ranking. -/
def sourceExecutableInversionCountByPairs (pi : SourceFourRanking) : ℕ :=
  ((Finset.univ : Finset (SourceFourCandidate × SourceFourCandidate)).filter
    (fun ij => ij.1 < ij.2 ∧ pi ij.2 < pi ij.1)).card

/-- Transparent inversion-count table for the 24 named rankings. -/
def sourceExecutableInversionCount : SourceFourRanking → ℕ
  | .r0123 => 0
  | .r0132 => 1
  | .r0213 => 1
  | .r0231 => 2
  | .r0312 => 2
  | .r0321 => 3
  | .r1023 => 1
  | .r1032 => 2
  | .r1203 => 2
  | .r1230 => 3
  | .r1302 => 3
  | .r1320 => 4
  | .r2013 => 2
  | .r2031 => 3
  | .r2103 => 3
  | .r2130 => 4
  | .r2301 => 4
  | .r2310 => 5
  | .r3012 => 3
  | .r3021 => 4
  | .r3102 => 4
  | .r3120 => 5
  | .r3201 => 5
  | .r3210 => 6

/-- The transparent table is exactly the pair-count definition of Kendall inversions. -/
theorem sourceExecutableInversionCount_eq_byPairs (pi : SourceFourRanking) :
    sourceExecutableInversionCount pi =
      sourceExecutableInversionCountByPairs pi := by
  cases pi <;> decide

/-- Exact Mallows partition function on four candidates. -/
def sourceExecutableMallowsPartition (q : ℚ) : ℚ :=
  ∑ pi : SourceFourRanking, q ^ sourceExecutableInversionCount pi

/-- Exact normalized Mallows atom mass. -/
def sourceExecutableMallowsMass (q : ℚ) (pi : SourceFourRanking) : ℚ :=
  q ^ sourceExecutableInversionCount pi /
    sourceExecutableMallowsPartition q

/-- Inverse Mallows parameters for `phi_A=2` and `phi_H=7/4`. -/
def sourceAlgorithmQ : ℚ := 1 / 2
def sourceHumanQ : ℚ := 4 / 7

/-!
The next two tables are the normalized Mallows masses used by the finite
evaluator.  Keeping the 24 masses transparent prevents every nested expectation
from recomputing the same partition function.  The two following lemmas verify
the tables against `q^inversions/Z`, so these are derived execution tables rather
than assumed ranking-law inputs.
-/

/-- Exact normalized `q=1/2` Mallows mass for each named ranking. -/
def sourceAlgorithmMallowsMass : SourceFourRanking → ℚ
  | .r0123 => 64 / 315
  | .r0132 => 32 / 315
  | .r0213 => 32 / 315
  | .r0231 => 16 / 315
  | .r0312 => 16 / 315
  | .r0321 => 8 / 315
  | .r1023 => 32 / 315
  | .r1032 => 16 / 315
  | .r1203 => 16 / 315
  | .r1230 => 8 / 315
  | .r1302 => 8 / 315
  | .r1320 => 4 / 315
  | .r2013 => 16 / 315
  | .r2031 => 8 / 315
  | .r2103 => 8 / 315
  | .r2130 => 4 / 315
  | .r2301 => 4 / 315
  | .r2310 => 2 / 315
  | .r3012 => 8 / 315
  | .r3021 => 4 / 315
  | .r3102 => 4 / 315
  | .r3120 => 2 / 315
  | .r3201 => 2 / 315
  | .r3210 => 1 / 315

/-- Exact normalized `q=4/7` Mallows mass for each named ranking. -/
def sourceHumanMallowsMass : SourceFourRanking → ℚ
  | .r0123 => 117649 / 731445
  | .r0132 => 67228 / 731445
  | .r0213 => 67228 / 731445
  | .r0231 => 38416 / 731445
  | .r0312 => 38416 / 731445
  | .r0321 => 21952 / 731445
  | .r1023 => 67228 / 731445
  | .r1032 => 38416 / 731445
  | .r1203 => 38416 / 731445
  | .r1230 => 21952 / 731445
  | .r1302 => 21952 / 731445
  | .r1320 => 12544 / 731445
  | .r2013 => 38416 / 731445
  | .r2031 => 21952 / 731445
  | .r2103 => 21952 / 731445
  | .r2130 => 12544 / 731445
  | .r2301 => 12544 / 731445
  | .r2310 => 7168 / 731445
  | .r3012 => 21952 / 731445
  | .r3021 => 12544 / 731445
  | .r3102 => 12544 / 731445
  | .r3120 => 7168 / 731445
  | .r3201 => 7168 / 731445
  | .r3210 => 4096 / 731445

theorem sourceExecutableMallowsPartition_algorithm :
    sourceExecutableMallowsPartition sourceAlgorithmQ = 315 / 64 := by
  unfold sourceExecutableMallowsPartition
  rw [SourceFourRanking.sum_twenty_four]
  norm_num [sourceAlgorithmQ,
    sourceExecutableInversionCount, sourceFourRankingAt, Fin.ext_iff]

theorem sourceExecutableMallowsPartition_human :
    sourceExecutableMallowsPartition sourceHumanQ = 731445 / 117649 := by
  unfold sourceExecutableMallowsPartition
  rw [SourceFourRanking.sum_twenty_four]
  norm_num [sourceHumanQ,
    sourceExecutableInversionCount, sourceFourRankingAt, Fin.ext_iff]

/-- The transparent algorithm table is exactly the normalized Mallows law. -/
theorem sourceAlgorithmMallowsMass_eq_executable (pi : SourceFourRanking) :
    sourceAlgorithmMallowsMass pi =
      sourceExecutableMallowsMass sourceAlgorithmQ pi := by
  unfold sourceExecutableMallowsMass
  rw [sourceExecutableMallowsPartition_algorithm]
  cases pi <;>
    norm_num [sourceAlgorithmMallowsMass, sourceAlgorithmQ,
      sourceExecutableInversionCount, sourceFourRankingAt, Fin.ext_iff]

/-- The transparent human table is exactly the normalized Mallows law. -/
theorem sourceHumanMallowsMass_eq_executable (pi : SourceFourRanking) :
    sourceHumanMallowsMass pi =
      sourceExecutableMallowsMass sourceHumanQ pi := by
  unfold sourceExecutableMallowsMass
  rw [sourceExecutableMallowsPartition_human]
  cases pi <;>
    norm_num [sourceHumanMallowsMass, sourceHumanQ,
      sourceExecutableInversionCount, sourceFourRankingAt, Fin.ext_iff]

/-- The exact human Mallows atom table is normalized. -/
theorem sourceHumanMallowsMass_sum :
    (∑ pi : SourceFourRanking, sourceHumanMallowsMass pi) = 1 := by
  rw [SourceFourRanking.sum_twenty_four]
  norm_num [sourceHumanMallowsMass]

/-- Expected `Uniform[0,1]` value of the candidate at each of four true ranks. -/
def sourceExpectedOrderStatisticValue (c : SourceFourCandidate) : ℚ :=
  if c = 0 then 4 / 5
  else if c = 1 then 3 / 5
  else if c = 2 then 2 / 5
  else 1 / 5

/-- Highest-ranked candidate not already selected. -/
def sourceBestAvailable (pi : SourceFourRanking)
    (selected : Finset SourceFourCandidate) : SourceFourCandidate :=
  if pi 0 ∉ selected then pi 0
  else if pi 1 ∉ selected then pi 1
  else if pi 2 ∉ selected then pi 2
  else pi 3

/-- Transparent specialization of `sourceBestAvailable` after one selection. -/
def sourceBestAvailableAfterOne :
    SourceFourRanking → SourceFourCandidate → SourceFourCandidate
  | .r0123, selected => if 0 = selected then 1 else 0
  | .r0132, selected => if 0 = selected then 1 else 0
  | .r0213, selected => if 0 = selected then 2 else 0
  | .r0231, selected => if 0 = selected then 2 else 0
  | .r0312, selected => if 0 = selected then 3 else 0
  | .r0321, selected => if 0 = selected then 3 else 0
  | .r1023, selected => if 1 = selected then 0 else 1
  | .r1032, selected => if 1 = selected then 0 else 1
  | .r1203, selected => if 1 = selected then 2 else 1
  | .r1230, selected => if 1 = selected then 2 else 1
  | .r1302, selected => if 1 = selected then 3 else 1
  | .r1320, selected => if 1 = selected then 3 else 1
  | .r2013, selected => if 2 = selected then 0 else 2
  | .r2031, selected => if 2 = selected then 0 else 2
  | .r2103, selected => if 2 = selected then 1 else 2
  | .r2130, selected => if 2 = selected then 1 else 2
  | .r2301, selected => if 2 = selected then 3 else 2
  | .r2310, selected => if 2 = selected then 3 else 2
  | .r3012, selected => if 3 = selected then 0 else 3
  | .r3021, selected => if 3 = selected then 0 else 3
  | .r3102, selected => if 3 = selected then 1 else 3
  | .r3120, selected => if 3 = selected then 1 else 3
  | .r3201, selected => if 3 = selected then 2 else 3
  | .r3210, selected => if 3 = selected then 2 else 3

private def sourceFirstNotTwo (a b c d first second : SourceFourCandidate) :
    SourceFourCandidate :=
  if a ≠ first ∧ a ≠ second then a
  else if b ≠ first ∧ b ≠ second then b
  else if c ≠ first ∧ c ≠ second then c
  else d

/-- Transparent specialization of `sourceBestAvailable` after two selections. -/
def sourceBestAvailableAfterTwo :
    SourceFourRanking → SourceFourCandidate → SourceFourCandidate → SourceFourCandidate
  | .r0123 => sourceFirstNotTwo 0 1 2 3
  | .r0132 => sourceFirstNotTwo 0 1 3 2
  | .r0213 => sourceFirstNotTwo 0 2 1 3
  | .r0231 => sourceFirstNotTwo 0 2 3 1
  | .r0312 => sourceFirstNotTwo 0 3 1 2
  | .r0321 => sourceFirstNotTwo 0 3 2 1
  | .r1023 => sourceFirstNotTwo 1 0 2 3
  | .r1032 => sourceFirstNotTwo 1 0 3 2
  | .r1203 => sourceFirstNotTwo 1 2 0 3
  | .r1230 => sourceFirstNotTwo 1 2 3 0
  | .r1302 => sourceFirstNotTwo 1 3 0 2
  | .r1320 => sourceFirstNotTwo 1 3 2 0
  | .r2013 => sourceFirstNotTwo 2 0 1 3
  | .r2031 => sourceFirstNotTwo 2 0 3 1
  | .r2103 => sourceFirstNotTwo 2 1 0 3
  | .r2130 => sourceFirstNotTwo 2 1 3 0
  | .r2301 => sourceFirstNotTwo 2 3 0 1
  | .r2310 => sourceFirstNotTwo 2 3 1 0
  | .r3012 => sourceFirstNotTwo 3 0 1 2
  | .r3021 => sourceFirstNotTwo 3 0 2 1
  | .r3102 => sourceFirstNotTwo 3 1 0 2
  | .r3120 => sourceFirstNotTwo 3 1 2 0
  | .r3201 => sourceFirstNotTwo 3 2 0 1
  | .r3210 => sourceFirstNotTwo 3 2 1 0

/-- The one-selection specialization computes the original sequential choice. -/
theorem sourceBestAvailable_singleton (pi : SourceFourRanking)
    (selected : SourceFourCandidate) :
    sourceBestAvailable pi {selected} =
      sourceBestAvailableAfterOne pi selected := by
  cases pi <;> fin_cases selected <;> decide

/-- The two-selection specialization computes the original sequential choice. -/
theorem sourceBestAvailable_pair (pi : SourceFourRanking)
    (first second : SourceFourCandidate) :
    sourceBestAvailable pi {first, second} =
      sourceBestAvailableAfterTwo pi first second := by
  cases pi <;> fin_cases first <;> fin_cases second <;> decide

/-- With no prior selection, the first-ranked candidate is chosen. -/
theorem sourceBestAvailable_empty (pi : SourceFourRanking) :
    sourceBestAvailable pi ∅ = pi 0 := by
  cases pi <;> decide

/-- Assemble three human-ranking coordinates by firm label. -/
def sourceHumanRankings (h0 h1 h2 : SourceFourRanking) :
    SourceThreeFirm → SourceFourRanking :=
  fun firm => if firm = 0 then h0 else if firm = 1 then h1 else h2

/--
Rank-mean payoff of labeled firm `0` after rankings and order are fixed.
`usesAlgorithm firm=true` means that firm uses the common ranking `algorithm`;
otherwise it uses its own coordinate of `human`. This substitutes asserted
order-statistic means by true rank and is not cardinal utility in one source
model realization.
-/
def sourceFocalUtility (usesAlgorithm : SourceThreeFirm → Bool)
    (algorithm : SourceFourRanking)
    (human : SourceThreeFirm → SourceFourRanking)
    (order : SourceFirmOrder) : ℚ :=
  let ranking : SourceThreeFirm → SourceFourRanking := fun firm =>
    if usesAlgorithm firm then algorithm else human firm
  let c0 := sourceBestAvailable (ranking (order 0)) ∅
  let c1 := sourceBestAvailable (ranking (order 1)) {c0}
  let c2 := sourceBestAvailable (ranking (order 2)) {c0, c1}
  if order 0 = 0 then sourceExpectedOrderStatisticValue c0
  else if order 1 = 0 then sourceExpectedOrderStatisticValue c1
  else sourceExpectedOrderStatisticValue c2

def sourceProfileAAA : SourceThreeFirm → Bool := fun _ => true
def sourceProfileHAA : SourceThreeFirm → Bool := fun firm => decide (firm ≠ 0)
def sourceProfileAAH : SourceThreeFirm → Bool := fun firm => decide (firm ≠ 2)
def sourceProfileHAH : SourceThreeFirm → Bool := fun firm => decide (firm = 1)
def sourceProfileAHH : SourceThreeFirm → Bool := fun firm => decide (firm = 0)
def sourceProfileHHH : SourceThreeFirm → Bool := fun _ => false

def sourceUniformFirmOrderMass : ℚ := 1 / 6

/-!
## Exact conditional transition tables

Directly reducing the joint `24^3` collapsed all-human sum produces an
unnecessarily large proof term. The next tables instead integrate one ranking
coordinate at a time. Each table entry is proved below to be the corresponding
sum under the exact `q = 4/7` table. The six-order conditional evaluators then
use only these proved transition probabilities and rank-mean values. A bridge
to the source joint experiment remains a separate obligation.
-/

/-- Probability that an independent human selects candidate `c` from the empty set. -/
def sourceHumanTopCandidateMass : SourceFourCandidate → ℚ :=
  fun c =>
    if c = 0 then 343 / 715
    else if c = 1 then 196 / 715
    else if c = 2 then 112 / 715
    else 64 / 715

/-- Probability that an independent human selects `next` after `selected` was taken. -/
def sourceHumanNextCandidateMass :
    SourceFourCandidate → SourceFourCandidate → ℚ :=
  fun selected next =>
    if selected = 0 then
      if next = 0 then 0
      else if next = 1 then 49 / 93
      else if next = 2 then 28 / 93
      else 16 / 93
    else if selected = 1 then
      if next = 0 then 3773 / 6045
      else if next = 1 then 0
      else if next = 2 then 15904 / 66495
      else 9088 / 66495
    else if selected = 2 then
      if next = 0 then 37387 / 66495
      else if next = 1 then 21364 / 66495
      else if next = 2 then 0
      else 704 / 6045
    else
      if next = 0 then 49 / 93
      else if next = 1 then 28 / 93
      else if next = 2 then 16 / 93
      else 0

/-- Expected value of a human's choice when no candidate has yet been taken. -/
def sourceHumanExpectedFirstValue : ℚ := 2248 / 3575

/-- Expected value of a human's choice after candidate `c` has been taken. -/
def sourceHumanExpectedAfterOneValue : SourceFourCandidate → ℚ :=
  fun c =>
    if c = 0 then 73 / 155
    else if c = 1 then 15916 / 25575
    else if c = 2 then 221384 / 332475
    else 104 / 155

/-- Expected value of a human's choice after candidates `c` and `d` have been taken. -/
def sourceHumanExpectedAfterTwoValue :
    SourceFourCandidate → SourceFourCandidate → ℚ :=
  fun c d =>
    if c = 0 then
      if d = 0 then 73 / 155
      else if d = 1 then 18 / 55
      else if d = 2 then 831 / 1705
      else 29 / 55
    else if c = 1 then
      if d = 0 then 18 / 55
      else if d = 1 then 15916 / 25575
      else if d = 2 then 74644 / 110825
      else 1172 / 1705
    else if c = 2 then
      if d = 0 then 831 / 1705
      else if d = 1 then 74644 / 110825
      else if d = 2 then 221384 / 332475
      else 8 / 11
    else
      if d = 0 then 29 / 55
      else if d = 1 then 1172 / 1705
      else if d = 2 then 8 / 11
      else 104 / 155

set_option maxRecDepth 100000

/-- The top-candidate table is the exact aggregation of the 24 human rankings. -/
theorem sourceHumanTopCandidateMass_eq_ranking_sum
    (c : SourceFourCandidate) :
    sourceHumanTopCandidateMass c =
      ∑ human : SourceFourRanking,
        sourceHumanMallowsMass human *
          (if human 0 = c then 1 else 0) := by
  fin_cases c <;>
    rw [SourceFourRanking.sum_twenty_four] <;>
    norm_num [sourceHumanTopCandidateMass, sourceHumanMallowsMass,
      sourceFourRankingAt, Fin.ext_iff]

/-- The one-selected transition table is the exact aggregation of the 24 human rankings. -/
theorem sourceHumanNextCandidateMass_eq_ranking_sum
    (selected next : SourceFourCandidate) :
    sourceHumanNextCandidateMass selected next =
      ∑ human : SourceFourRanking,
        sourceHumanMallowsMass human *
          (if sourceBestAvailable human {selected} = next then 1 else 0) := by
  simp_rw [sourceBestAvailable_singleton]
  fin_cases selected <;> fin_cases next <;>
    rw [SourceFourRanking.sum_twenty_four] <;>
    norm_num [sourceHumanNextCandidateMass, sourceHumanMallowsMass,
      sourceBestAvailableAfterOne, sourceFourRankingAt, Fin.ext_iff]

/-- The no-selection human value is the exact 24-ranking expectation. -/
theorem sourceHumanExpectedFirstValue_eq_ranking_sum :
    sourceHumanExpectedFirstValue =
      ∑ human : SourceFourRanking,
        sourceHumanMallowsMass human *
          sourceExpectedOrderStatisticValue (sourceBestAvailable human ∅) := by
  simp_rw [sourceBestAvailable_empty]
  rw [SourceFourRanking.sum_twenty_four]
  norm_num [sourceHumanExpectedFirstValue, sourceHumanMallowsMass,
    sourceExpectedOrderStatisticValue, sourceFourRankingAt, Fin.ext_iff]

/-- The one-selection human value table is the exact 24-ranking expectation. -/
theorem sourceHumanExpectedAfterOneValue_eq_ranking_sum
    (c : SourceFourCandidate) :
    sourceHumanExpectedAfterOneValue c =
      ∑ human : SourceFourRanking,
        sourceHumanMallowsMass human *
          sourceExpectedOrderStatisticValue
            (sourceBestAvailable human {c}) := by
  simp_rw [sourceBestAvailable_singleton]
  fin_cases c <;>
    rw [SourceFourRanking.sum_twenty_four] <;>
    norm_num [sourceHumanExpectedAfterOneValue, sourceHumanMallowsMass,
      sourceBestAvailableAfterOne, sourceExpectedOrderStatisticValue,
      sourceFourRankingAt, Fin.ext_iff]

private theorem sourceHumanExpectedAfterTwoValue_eq_ranking_sum_diag
    (c : SourceFourCandidate) :
    sourceHumanExpectedAfterTwoValue c c =
      ∑ human : SourceFourRanking,
        sourceHumanMallowsMass human *
          sourceExpectedOrderStatisticValue
            (sourceBestAvailable human {c, c}) := by
  fin_cases c
  · simpa [sourceHumanExpectedAfterTwoValue,
      sourceHumanExpectedAfterOneValue] using
      (sourceHumanExpectedAfterOneValue_eq_ranking_sum (c := 0))
  · simpa [sourceHumanExpectedAfterTwoValue,
      sourceHumanExpectedAfterOneValue] using
      (sourceHumanExpectedAfterOneValue_eq_ranking_sum (c := 1))
  · simpa [sourceHumanExpectedAfterTwoValue,
      sourceHumanExpectedAfterOneValue] using
      (sourceHumanExpectedAfterOneValue_eq_ranking_sum (c := 2))
  · simpa [sourceHumanExpectedAfterTwoValue,
      sourceHumanExpectedAfterOneValue] using
      (sourceHumanExpectedAfterOneValue_eq_ranking_sum (c := 3))

private theorem sourceHumanAfterTwoCandidateMass_zero_one :
    (∑ human : SourceFourRanking,
      sourceHumanMallowsMass human *
        (if sourceBestAvailableAfterTwo human 0 1 = 2 then 1 else 0)) =
      7 / 11 := by
  rw [SourceFourRanking.sum_twenty_four]
  norm_num [sourceHumanMallowsMass, sourceBestAvailableAfterTwo,
    sourceFirstNotTwo, Fin.ext_iff]

private theorem sourceHumanAfterTwoCandidateMass_zero_two :
    (∑ human : SourceFourRanking,
      sourceHumanMallowsMass human *
        (if sourceBestAvailableAfterTwo human 0 2 = 1 then 1 else 0)) =
      245 / 341 := by
  rw [SourceFourRanking.sum_twenty_four]
  norm_num [sourceHumanMallowsMass, sourceBestAvailableAfterTwo,
    sourceFirstNotTwo, Fin.ext_iff]

private theorem sourceHumanAfterTwoCandidateMass_zero_three :
    (∑ human : SourceFourRanking,
      sourceHumanMallowsMass human *
        (if sourceBestAvailableAfterTwo human 0 3 = 1 then 1 else 0)) =
      7 / 11 := by
  rw [SourceFourRanking.sum_twenty_four]
  norm_num [sourceHumanMallowsMass, sourceBestAvailableAfterTwo,
    sourceFirstNotTwo, Fin.ext_iff]

private theorem sourceHumanAfterTwoCandidateMass_one_two :
    (∑ human : SourceFourRanking,
      sourceHumanMallowsMass human *
        (if sourceBestAvailableAfterTwo human 1 2 = 0 then 1 else 0)) =
      17493 / 22165 := by
  rw [SourceFourRanking.sum_twenty_four]
  norm_num [sourceHumanMallowsMass, sourceBestAvailableAfterTwo,
    sourceFirstNotTwo, Fin.ext_iff]

private theorem sourceHumanAfterTwoCandidateMass_one_three :
    (∑ human : SourceFourRanking,
      sourceHumanMallowsMass human *
        (if sourceBestAvailableAfterTwo human 1 3 = 0 then 1 else 0)) =
      245 / 341 := by
  rw [SourceFourRanking.sum_twenty_four]
  norm_num [sourceHumanMallowsMass, sourceBestAvailableAfterTwo,
    sourceFirstNotTwo, Fin.ext_iff]

private theorem sourceHumanAfterTwoCandidateMass_two_three :
    (∑ human : SourceFourRanking,
      sourceHumanMallowsMass human *
        (if sourceBestAvailableAfterTwo human 2 3 = 0 then 1 else 0)) =
      7 / 11 := by
  rw [SourceFourRanking.sum_twenty_four]
  norm_num [sourceHumanMallowsMass, sourceBestAvailableAfterTwo,
    sourceFirstNotTwo, Fin.ext_iff]

private theorem sourceHumanExpectedAfterTwoValue_eq_ranking_sum_zero_one :
    sourceHumanExpectedAfterTwoValue 0 1 =
      ∑ human : SourceFourRanking,
        sourceHumanMallowsMass human *
          sourceExpectedOrderStatisticValue
            (sourceBestAvailable human {0, 1}) := by
  simp_rw [sourceBestAvailable_pair]
  have hpoint (human : SourceFourRanking) :
      sourceHumanMallowsMass human *
          sourceExpectedOrderStatisticValue
            (sourceBestAvailableAfterTwo human 0 1) =
        sourceHumanMallowsMass human * (1 / 5) +
          (1 / 5) *
            (sourceHumanMallowsMass human *
              (if sourceBestAvailableAfterTwo human 0 1 = 2 then 1 else 0)) := by
    cases human <;>
      norm_num [sourceHumanMallowsMass, sourceBestAvailableAfterTwo,
        sourceFirstNotTwo, sourceExpectedOrderStatisticValue, Fin.ext_iff]
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
    sourceHumanMallowsMass_sum, sourceHumanAfterTwoCandidateMass_zero_one]
  norm_num [sourceHumanExpectedAfterTwoValue, Fin.ext_iff]

private theorem sourceHumanExpectedAfterTwoValue_eq_ranking_sum_zero_two :
    sourceHumanExpectedAfterTwoValue 0 2 =
      ∑ human : SourceFourRanking,
        sourceHumanMallowsMass human *
          sourceExpectedOrderStatisticValue
            (sourceBestAvailable human {0, 2}) := by
  simp_rw [sourceBestAvailable_pair]
  have hpoint (human : SourceFourRanking) :
      sourceHumanMallowsMass human *
          sourceExpectedOrderStatisticValue
            (sourceBestAvailableAfterTwo human 0 2) =
        sourceHumanMallowsMass human * (1 / 5) +
          (2 / 5) *
            (sourceHumanMallowsMass human *
              (if sourceBestAvailableAfterTwo human 0 2 = 1 then 1 else 0)) := by
    cases human <;>
      norm_num [sourceHumanMallowsMass, sourceBestAvailableAfterTwo,
        sourceFirstNotTwo, sourceExpectedOrderStatisticValue, Fin.ext_iff]
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
    sourceHumanMallowsMass_sum, sourceHumanAfterTwoCandidateMass_zero_two]
  norm_num [sourceHumanExpectedAfterTwoValue, Fin.ext_iff]

private theorem sourceHumanExpectedAfterTwoValue_eq_ranking_sum_zero_three :
    sourceHumanExpectedAfterTwoValue 0 3 =
      ∑ human : SourceFourRanking,
        sourceHumanMallowsMass human *
          sourceExpectedOrderStatisticValue
            (sourceBestAvailable human {0, 3}) := by
  simp_rw [sourceBestAvailable_pair]
  have hpoint (human : SourceFourRanking) :
      sourceHumanMallowsMass human *
          sourceExpectedOrderStatisticValue
            (sourceBestAvailableAfterTwo human 0 3) =
        sourceHumanMallowsMass human * (2 / 5) +
          (1 / 5) *
            (sourceHumanMallowsMass human *
              (if sourceBestAvailableAfterTwo human 0 3 = 1 then 1 else 0)) := by
    cases human <;>
      norm_num [sourceHumanMallowsMass, sourceBestAvailableAfterTwo,
        sourceFirstNotTwo, sourceExpectedOrderStatisticValue, Fin.ext_iff]
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
    sourceHumanMallowsMass_sum, sourceHumanAfterTwoCandidateMass_zero_three]
  norm_num [sourceHumanExpectedAfterTwoValue, Fin.ext_iff]

private theorem sourceHumanExpectedAfterTwoValue_eq_ranking_sum_one_two :
    sourceHumanExpectedAfterTwoValue 1 2 =
      ∑ human : SourceFourRanking,
        sourceHumanMallowsMass human *
          sourceExpectedOrderStatisticValue
            (sourceBestAvailable human {1, 2}) := by
  simp_rw [sourceBestAvailable_pair]
  have hpoint (human : SourceFourRanking) :
      sourceHumanMallowsMass human *
          sourceExpectedOrderStatisticValue
            (sourceBestAvailableAfterTwo human 1 2) =
        sourceHumanMallowsMass human * (1 / 5) +
          (3 / 5) *
            (sourceHumanMallowsMass human *
              (if sourceBestAvailableAfterTwo human 1 2 = 0 then 1 else 0)) := by
    cases human <;>
      norm_num [sourceHumanMallowsMass, sourceBestAvailableAfterTwo,
        sourceFirstNotTwo, sourceExpectedOrderStatisticValue, Fin.ext_iff]
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
    sourceHumanMallowsMass_sum, sourceHumanAfterTwoCandidateMass_one_two]
  norm_num [sourceHumanExpectedAfterTwoValue, Fin.ext_iff]

private theorem sourceHumanExpectedAfterTwoValue_eq_ranking_sum_one_three :
    sourceHumanExpectedAfterTwoValue 1 3 =
      ∑ human : SourceFourRanking,
        sourceHumanMallowsMass human *
          sourceExpectedOrderStatisticValue
            (sourceBestAvailable human {1, 3}) := by
  simp_rw [sourceBestAvailable_pair]
  have hpoint (human : SourceFourRanking) :
      sourceHumanMallowsMass human *
          sourceExpectedOrderStatisticValue
            (sourceBestAvailableAfterTwo human 1 3) =
        sourceHumanMallowsMass human * (2 / 5) +
          (2 / 5) *
            (sourceHumanMallowsMass human *
              (if sourceBestAvailableAfterTwo human 1 3 = 0 then 1 else 0)) := by
    cases human <;>
      norm_num [sourceHumanMallowsMass, sourceBestAvailableAfterTwo,
        sourceFirstNotTwo, sourceExpectedOrderStatisticValue, Fin.ext_iff]
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
    sourceHumanMallowsMass_sum, sourceHumanAfterTwoCandidateMass_one_three]
  norm_num [sourceHumanExpectedAfterTwoValue, Fin.ext_iff]

private theorem sourceHumanExpectedAfterTwoValue_eq_ranking_sum_two_three :
    sourceHumanExpectedAfterTwoValue 2 3 =
      ∑ human : SourceFourRanking,
        sourceHumanMallowsMass human *
          sourceExpectedOrderStatisticValue
            (sourceBestAvailable human {2, 3}) := by
  simp_rw [sourceBestAvailable_pair]
  have hpoint (human : SourceFourRanking) :
      sourceHumanMallowsMass human *
          sourceExpectedOrderStatisticValue
            (sourceBestAvailableAfterTwo human 2 3) =
        sourceHumanMallowsMass human * (3 / 5) +
          (1 / 5) *
            (sourceHumanMallowsMass human *
              (if sourceBestAvailableAfterTwo human 2 3 = 0 then 1 else 0)) := by
    cases human <;>
      norm_num [sourceHumanMallowsMass, sourceBestAvailableAfterTwo,
        sourceFirstNotTwo, sourceExpectedOrderStatisticValue, Fin.ext_iff]
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
    sourceHumanMallowsMass_sum, sourceHumanAfterTwoCandidateMass_two_three]
  norm_num [sourceHumanExpectedAfterTwoValue, Fin.ext_iff]

/-- The two-selection human value table is the exact 24-ranking expectation. -/
theorem sourceHumanExpectedAfterTwoValue_eq_ranking_sum
    (c d : SourceFourCandidate) :
    sourceHumanExpectedAfterTwoValue c d =
      ∑ human : SourceFourRanking,
        sourceHumanMallowsMass human *
          sourceExpectedOrderStatisticValue
            (sourceBestAvailable human {c, d}) := by
  fin_cases c <;> fin_cases d
  · exact sourceHumanExpectedAfterTwoValue_eq_ranking_sum_diag 0
  · exact sourceHumanExpectedAfterTwoValue_eq_ranking_sum_zero_one
  · exact sourceHumanExpectedAfterTwoValue_eq_ranking_sum_zero_two
  · exact sourceHumanExpectedAfterTwoValue_eq_ranking_sum_zero_three
  · simpa [sourceHumanExpectedAfterTwoValue, Finset.pair_comm] using
      sourceHumanExpectedAfterTwoValue_eq_ranking_sum_zero_one
  · exact sourceHumanExpectedAfterTwoValue_eq_ranking_sum_diag 1
  · exact sourceHumanExpectedAfterTwoValue_eq_ranking_sum_one_two
  · exact sourceHumanExpectedAfterTwoValue_eq_ranking_sum_one_three
  · simpa [sourceHumanExpectedAfterTwoValue, Finset.pair_comm] using
      sourceHumanExpectedAfterTwoValue_eq_ranking_sum_zero_two
  · simpa [sourceHumanExpectedAfterTwoValue, Finset.pair_comm] using
      sourceHumanExpectedAfterTwoValue_eq_ranking_sum_one_two
  · exact sourceHumanExpectedAfterTwoValue_eq_ranking_sum_diag 2
  · exact sourceHumanExpectedAfterTwoValue_eq_ranking_sum_two_three
  · simpa [sourceHumanExpectedAfterTwoValue, Finset.pair_comm] using
      sourceHumanExpectedAfterTwoValue_eq_ranking_sum_zero_three
  · simpa [sourceHumanExpectedAfterTwoValue, Finset.pair_comm] using
      sourceHumanExpectedAfterTwoValue_eq_ranking_sum_one_three
  · simpa [sourceHumanExpectedAfterTwoValue, Finset.pair_comm] using
      sourceHumanExpectedAfterTwoValue_eq_ranking_sum_two_three
  · exact sourceHumanExpectedAfterTwoValue_eq_ranking_sum_diag 3

/-! ### Six-order collapsed rank-mean expectations -/

/-- All-algorithm focal value conditional on the shared algorithm ranking. -/
def sourceConditionalAAA (algorithm : SourceFourRanking) : SourceFirmOrder → ℚ
  | .f012 | .f021 => sourceExpectedOrderStatisticValue (algorithm 0)
  | .f102 | .f201 => sourceExpectedOrderStatisticValue (algorithm 1)
  | .f120 | .f210 => sourceExpectedOrderStatisticValue (algorithm 2)

/-- Human focal value against two algorithm users, conditional on their ranking. -/
def sourceConditionalHAA (algorithm : SourceFourRanking) : SourceFirmOrder → ℚ
  | .f012 | .f021 => sourceHumanExpectedFirstValue
  | .f102 | .f201 => sourceHumanExpectedAfterOneValue (algorithm 0)
  | .f120 | .f210 =>
      sourceHumanExpectedAfterTwoValue (algorithm 0) (algorithm 1)

/-- Algorithm focal value against one algorithm and one human. -/
def sourceConditionalAAH (algorithm : SourceFourRanking) : SourceFirmOrder → ℚ
  | .f012 | .f021 => sourceExpectedOrderStatisticValue (algorithm 0)
  | .f102 => sourceExpectedOrderStatisticValue (algorithm 1)
  | .f120 =>
      ∑ next : SourceFourCandidate,
          sourceHumanNextCandidateMass (algorithm 0) next *
          sourceExpectedOrderStatisticValue
            (sourceBestAvailableAfterTwo algorithm (algorithm 0) next)
  | .f201 =>
      ∑ first : SourceFourCandidate,
        sourceHumanTopCandidateMass first *
          sourceExpectedOrderStatisticValue
            (sourceBestAvailableAfterOne algorithm first)
  | .f210 =>
      ∑ first : SourceFourCandidate,
        sourceHumanTopCandidateMass first *
          sourceExpectedOrderStatisticValue
            (sourceBestAvailableAfterTwo algorithm first
              (sourceBestAvailableAfterOne algorithm first))

/-- Human focal value against one algorithm and one human. -/
def sourceConditionalHAH (algorithm : SourceFourRanking) : SourceFirmOrder → ℚ
  | .f012 | .f021 => sourceHumanExpectedFirstValue
  | .f102 => sourceHumanExpectedAfterOneValue (algorithm 0)
  | .f120 =>
      ∑ next : SourceFourCandidate,
        sourceHumanNextCandidateMass (algorithm 0) next *
          sourceHumanExpectedAfterTwoValue (algorithm 0) next
  | .f201 =>
      ∑ first : SourceFourCandidate,
        sourceHumanTopCandidateMass first *
          sourceHumanExpectedAfterOneValue first
  | .f210 =>
      ∑ first : SourceFourCandidate,
        sourceHumanTopCandidateMass first *
          sourceHumanExpectedAfterTwoValue first
            (sourceBestAvailableAfterOne algorithm first)

/-- Algorithm focal value against two independent human users. -/
def sourceConditionalAHH (algorithm : SourceFourRanking) : SourceFirmOrder → ℚ
  | .f012 | .f021 => sourceExpectedOrderStatisticValue (algorithm 0)
  | .f102 | .f201 =>
      ∑ first : SourceFourCandidate,
        sourceHumanTopCandidateMass first *
          sourceExpectedOrderStatisticValue
            (sourceBestAvailableAfterOne algorithm first)
  | .f120 | .f210 =>
      ∑ first : SourceFourCandidate,
        sourceHumanTopCandidateMass first *
          (∑ next : SourceFourCandidate,
            sourceHumanNextCandidateMass first next *
              sourceExpectedOrderStatisticValue
                (sourceBestAvailableAfterTwo algorithm first next))

/-- Human focal value against two independent human users. -/
def sourceConditionalHHH : SourceFirmOrder → ℚ
  | .f012 | .f021 => sourceHumanExpectedFirstValue
  | .f102 | .f201 =>
      ∑ first : SourceFourCandidate,
        sourceHumanTopCandidateMass first *
          sourceHumanExpectedAfterOneValue first
  | .f120 | .f210 =>
      ∑ first : SourceFourCandidate,
        sourceHumanTopCandidateMass first *
          (∑ next : SourceFourCandidate,
            sourceHumanNextCandidateMass first next *
              sourceHumanExpectedAfterTwoValue first next)

/-! ### Symbolic six-order averages -/

/-- Expand a sum over the four concrete candidate labels. -/
private theorem sourceFourCandidate_sum_four (f : SourceFourCandidate → ℚ) :
    (∑ c : SourceFourCandidate, f c) = f 0 + f 1 + f 2 + f 3 := by
  classical
  have huniv :
      (Finset.univ : Finset SourceFourCandidate) = {0, 1, 2, 3} := by
    ext c
    fin_cases c <;> simp
  simp [huniv, add_assoc]

/-- Average the all-algorithm focal payoff over the six equiprobable arrival orders. -/
private theorem sourceConditionalAAA_order_average (algorithm : SourceFourRanking) :
    (∑ order : SourceFirmOrder,
      sourceUniformFirmOrderMass * sourceConditionalAAA algorithm order) =
      (sourceExpectedOrderStatisticValue (algorithm 0) +
        sourceExpectedOrderStatisticValue (algorithm 1) +
        sourceExpectedOrderStatisticValue (algorithm 2)) / 3 := by
  rw [SourceFirmOrder.sum_six]
  simp only [sourceUniformFirmOrderMass, sourceConditionalAAA]
  ring

/-- Average the focal-human-against-two-algorithms payoff over arrival orders. -/
private theorem sourceConditionalHAA_order_average (algorithm : SourceFourRanking) :
    (∑ order : SourceFirmOrder,
      sourceUniformFirmOrderMass * sourceConditionalHAA algorithm order) =
      (sourceHumanExpectedFirstValue +
        sourceHumanExpectedAfterOneValue (algorithm 0) +
        sourceHumanExpectedAfterTwoValue (algorithm 0) (algorithm 1)) / 3 := by
  rw [SourceFirmOrder.sum_six]
  simp only [sourceUniformFirmOrderMass, sourceConditionalHAA]
  ring

/-- Average the focal-algorithm-against-algorithm-and-human payoff over orders. -/
private theorem sourceConditionalAAH_order_average (algorithm : SourceFourRanking) :
    (∑ order : SourceFirmOrder,
      sourceUniformFirmOrderMass * sourceConditionalAAH algorithm order) =
      (2 * sourceExpectedOrderStatisticValue (algorithm 0) +
        sourceExpectedOrderStatisticValue (algorithm 1) +
        (∑ next : SourceFourCandidate,
          sourceHumanNextCandidateMass (algorithm 0) next *
            sourceExpectedOrderStatisticValue
              (sourceBestAvailableAfterTwo algorithm (algorithm 0) next)) +
        (∑ first : SourceFourCandidate,
          sourceHumanTopCandidateMass first *
            sourceExpectedOrderStatisticValue
              (sourceBestAvailableAfterOne algorithm first)) +
        (∑ first : SourceFourCandidate,
          sourceHumanTopCandidateMass first *
            sourceExpectedOrderStatisticValue
              (sourceBestAvailableAfterTwo algorithm first
                (sourceBestAvailableAfterOne algorithm first))) ) / 6 := by
  rw [SourceFirmOrder.sum_six]
  simp only [sourceUniformFirmOrderMass, sourceConditionalAAH]
  ring

/-- Average the focal-human-against-algorithm-and-human payoff over orders. -/
private theorem sourceConditionalHAH_order_average (algorithm : SourceFourRanking) :
    (∑ order : SourceFirmOrder,
      sourceUniformFirmOrderMass * sourceConditionalHAH algorithm order) =
      (2 * sourceHumanExpectedFirstValue +
        sourceHumanExpectedAfterOneValue (algorithm 0) +
        (∑ next : SourceFourCandidate,
          sourceHumanNextCandidateMass (algorithm 0) next *
            sourceHumanExpectedAfterTwoValue (algorithm 0) next) +
        (∑ first : SourceFourCandidate,
          sourceHumanTopCandidateMass first *
            sourceHumanExpectedAfterOneValue first) +
        (∑ first : SourceFourCandidate,
          sourceHumanTopCandidateMass first *
            sourceHumanExpectedAfterTwoValue first
              (sourceBestAvailableAfterOne algorithm first))) / 6 := by
  rw [SourceFirmOrder.sum_six]
  simp only [sourceUniformFirmOrderMass, sourceConditionalHAH]
  ring

/-- Average the focal-algorithm-against-two-humans payoff over arrival orders. -/
private theorem sourceConditionalAHH_order_average (algorithm : SourceFourRanking) :
    (∑ order : SourceFirmOrder,
      sourceUniformFirmOrderMass * sourceConditionalAHH algorithm order) =
      (sourceExpectedOrderStatisticValue (algorithm 0) +
        (∑ first : SourceFourCandidate,
          sourceHumanTopCandidateMass first *
            sourceExpectedOrderStatisticValue
              (sourceBestAvailableAfterOne algorithm first)) +
        (∑ first : SourceFourCandidate,
          sourceHumanTopCandidateMass first *
            (∑ next : SourceFourCandidate,
              sourceHumanNextCandidateMass first next *
                sourceExpectedOrderStatisticValue
                  (sourceBestAvailableAfterTwo algorithm first next)))) / 3 := by
  rw [SourceFirmOrder.sum_six]
  simp only [sourceUniformFirmOrderMass, sourceConditionalAHH]
  ring

/-- Average the focal-human-against-two-humans payoff over arrival orders. -/
private theorem sourceConditionalHHH_order_average :
    (∑ order : SourceFirmOrder,
      sourceUniformFirmOrderMass * sourceConditionalHHH order) =
      (sourceHumanExpectedFirstValue +
        (∑ first : SourceFourCandidate,
          sourceHumanTopCandidateMass first *
            sourceHumanExpectedAfterOneValue first) +
        (∑ first : SourceFourCandidate,
          sourceHumanTopCandidateMass first *
            (∑ next : SourceFourCandidate,
              sourceHumanNextCandidateMass first next *
                sourceHumanExpectedAfterTwoValue first next))) / 3 := by
  rw [SourceFirmOrder.sum_six]
  simp only [sourceUniformFirmOrderMass, sourceConditionalHHH]
  ring

/-! ### Algorithm rank-position aggregates -/

/-- Probability that the algorithm ranking puts a candidate in a given position. -/
private def sourceAlgorithmPositionCandidateMass :
    SourceFourCandidate → SourceFourCandidate → ℚ :=
  fun position candidate =>
    if position = 0 then
      if candidate = 0 then 8 / 15
      else if candidate = 1 then 4 / 15
      else if candidate = 2 then 2 / 15
      else 1 / 15
    else if position = 1 then
      if candidate = 0 then 4 / 15
      else if candidate = 1 then 38 / 105
      else if candidate = 2 then 5 / 21
      else 2 / 15
    else if position = 2 then
      if candidate = 0 then 2 / 15
      else if candidate = 1 then 5 / 21
      else if candidate = 2 then 38 / 105
      else 4 / 15
    else
      if candidate = 0 then 1 / 15
      else if candidate = 1 then 2 / 15
      else if candidate = 2 then 4 / 15
      else 8 / 15

/-- The algorithm position-candidate table is the exact 24-ranking aggregation. -/
private theorem sourceAlgorithmPositionCandidateMass_eq_ranking_sum
    (position candidate : SourceFourCandidate) :
    sourceAlgorithmPositionCandidateMass position candidate =
      ∑ algorithm : SourceFourRanking,
        sourceAlgorithmMallowsMass algorithm *
          (if algorithm position = candidate then 1 else 0) := by
  fin_cases position <;> fin_cases candidate <;>
    rw [SourceFourRanking.sum_twenty_four] <;>
    norm_num [sourceAlgorithmPositionCandidateMass, sourceAlgorithmMallowsMass,
      sourceFourRankingAt, Fin.ext_iff]

/-- Write a rank-mean payoff as its four candidate-indicator contributions. -/
private theorem sourceExpectedOrderStatisticValue_indicator
    (candidate : SourceFourCandidate) :
    sourceExpectedOrderStatisticValue candidate =
      (4 / 5) * (if candidate = 0 then 1 else 0) +
        (3 / 5) * (if candidate = 1 then 1 else 0) +
        (2 / 5) * (if candidate = 2 then 1 else 0) +
        (1 / 5) * (if candidate = 3 then 1 else 0) := by
  fin_cases candidate <;>
    norm_num [sourceExpectedOrderStatisticValue, Fin.ext_iff]

/-- Reduce an algorithm rank-position mean to the verified position-candidate table. -/
private theorem sourceAlgorithmExpectedRankValue_eq_candidateMass
    (position : SourceFourCandidate) :
    (∑ algorithm : SourceFourRanking,
      sourceAlgorithmMallowsMass algorithm *
        sourceExpectedOrderStatisticValue (algorithm position)) =
      (4 / 5) * sourceAlgorithmPositionCandidateMass position 0 +
        (3 / 5) * sourceAlgorithmPositionCandidateMass position 1 +
        (2 / 5) * sourceAlgorithmPositionCandidateMass position 2 +
        (1 / 5) * sourceAlgorithmPositionCandidateMass position 3 := by
  calc
    (∑ algorithm : SourceFourRanking,
      sourceAlgorithmMallowsMass algorithm *
        sourceExpectedOrderStatisticValue (algorithm position)) =
        (4 / 5) * (∑ algorithm : SourceFourRanking,
          sourceAlgorithmMallowsMass algorithm *
            (if algorithm position = 0 then 1 else 0)) +
          (3 / 5) * (∑ algorithm : SourceFourRanking,
            sourceAlgorithmMallowsMass algorithm *
              (if algorithm position = 1 then 1 else 0)) +
          (2 / 5) * (∑ algorithm : SourceFourRanking,
            sourceAlgorithmMallowsMass algorithm *
              (if algorithm position = 2 then 1 else 0)) +
          (1 / 5) * (∑ algorithm : SourceFourRanking,
            sourceAlgorithmMallowsMass algorithm *
              (if algorithm position = 3 then 1 else 0)) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro algorithm _
      rw [sourceExpectedOrderStatisticValue_indicator]
      ring
    _ = _ := by
      rw [← sourceAlgorithmPositionCandidateMass_eq_ranking_sum position 0,
        ← sourceAlgorithmPositionCandidateMass_eq_ranking_sum position 1,
        ← sourceAlgorithmPositionCandidateMass_eq_ranking_sum position 2,
        ← sourceAlgorithmPositionCandidateMass_eq_ranking_sum position 3]

/-- Exact rank-mean value of the first algorithm choice under the Mallows table. -/
private theorem sourceAlgorithmExpectedFirstRankValue :
    (∑ algorithm : SourceFourRanking,
      sourceAlgorithmMallowsMass algorithm *
        sourceExpectedOrderStatisticValue (algorithm 0)) =
      49 / 75 := by
  rw [sourceAlgorithmExpectedRankValue_eq_candidateMass]
  norm_num [sourceAlgorithmPositionCandidateMass, Fin.ext_iff]

/-- Exact rank-mean value of the second algorithm choice under the Mallows table. -/
private theorem sourceAlgorithmExpectedSecondRankValue :
    (∑ algorithm : SourceFourRanking,
      sourceAlgorithmMallowsMass algorithm *
        sourceExpectedOrderStatisticValue (algorithm 1)) =
      58 / 105 := by
  rw [sourceAlgorithmExpectedRankValue_eq_candidateMass]
  norm_num [sourceAlgorithmPositionCandidateMass, Fin.ext_iff]

/-- Exact rank-mean value of the third algorithm choice under the Mallows table. -/
private theorem sourceAlgorithmExpectedThirdRankValue :
    (∑ algorithm : SourceFourRanking,
      sourceAlgorithmMallowsMass algorithm *
        sourceExpectedOrderStatisticValue (algorithm 2)) =
      47 / 105 := by
  rw [sourceAlgorithmExpectedRankValue_eq_candidateMass]
  norm_num [sourceAlgorithmPositionCandidateMass, Fin.ext_iff]

/-- Collapsed focal rank-mean payoff at the all-algorithm profile. -/
def sourceExecutableExpectedAAA : ℚ :=
  ∑ algorithm : SourceFourRanking,
    sourceAlgorithmMallowsMass algorithm *
      (∑ order : SourceFirmOrder,
        sourceUniformFirmOrderMass * sourceConditionalAAA algorithm order)

/-- Collapsed focal rank-mean payoff after switching to human against two algorithm users. -/
def sourceExecutableExpectedHAA : ℚ :=
  ∑ algorithm : SourceFourRanking,
    sourceAlgorithmMallowsMass algorithm *
      (∑ order : SourceFirmOrder,
        sourceUniformFirmOrderMass * sourceConditionalHAA algorithm order)

/-- Collapsed focal algorithm rank-mean payoff against one algorithm and one human. -/
def sourceExecutableExpectedAAH : ℚ :=
  ∑ algorithm : SourceFourRanking,
    sourceAlgorithmMallowsMass algorithm *
      (∑ order : SourceFirmOrder,
        sourceUniformFirmOrderMass * sourceConditionalAAH algorithm order)

/-- Collapsed focal human rank-mean payoff against one algorithm and one human. -/
def sourceExecutableExpectedHAH : ℚ :=
  ∑ algorithm : SourceFourRanking,
    sourceAlgorithmMallowsMass algorithm *
      (∑ order : SourceFirmOrder,
        sourceUniformFirmOrderMass * sourceConditionalHAH algorithm order)

/-- Collapsed focal algorithm rank-mean payoff against two human users. -/
def sourceExecutableExpectedAHH : ℚ :=
  ∑ algorithm : SourceFourRanking,
    sourceAlgorithmMallowsMass algorithm *
      (∑ order : SourceFirmOrder,
        sourceUniformFirmOrderMass * sourceConditionalAHH algorithm order)

/-- Collapsed focal rank-mean payoff at the all-human profile. -/
def sourceExecutableExpectedHHH : ℚ :=
  ∑ order : SourceFirmOrder,
    sourceUniformFirmOrderMass * sourceConditionalHHH order

/- The following equalities are kernel-checked evaluations of the collapsed finite sums above. -/

theorem source_executable_expectedAAA_eq :
    sourceExecutableExpectedAAA = 124 / 225 := by
  unfold sourceExecutableExpectedAAA
  simp_rw [sourceConditionalAAA_order_average]
  have hpoint (algorithm : SourceFourRanking) :
      sourceAlgorithmMallowsMass algorithm *
          ((sourceExpectedOrderStatisticValue (algorithm 0) +
            sourceExpectedOrderStatisticValue (algorithm 1) +
            sourceExpectedOrderStatisticValue (algorithm 2)) / 3) =
        (sourceAlgorithmMallowsMass algorithm *
            sourceExpectedOrderStatisticValue (algorithm 0) +
          sourceAlgorithmMallowsMass algorithm *
            sourceExpectedOrderStatisticValue (algorithm 1) +
          sourceAlgorithmMallowsMass algorithm *
            sourceExpectedOrderStatisticValue (algorithm 2)) / 3 := by
    ring
  simp_rw [hpoint]
  rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_add_distrib,
    sourceAlgorithmExpectedFirstRankValue, sourceAlgorithmExpectedSecondRankValue,
    sourceAlgorithmExpectedThirdRankValue]
  norm_num

theorem source_executable_expectedHAA_eq :
    sourceExecutableExpectedHAA = 57174284 / 104729625 := by
  unfold sourceExecutableExpectedHAA
  simp_rw [sourceConditionalHAA_order_average]
  rw [SourceFourRanking.sum_twenty_four]
  norm_num [sourceAlgorithmMallowsMass, sourceHumanExpectedFirstValue,
    sourceHumanExpectedAfterOneValue, sourceHumanExpectedAfterTwoValue,
    sourceFourRankingAt, Fin.ext_iff]

theorem source_executable_expectedAAH_eq :
    sourceExecutableExpectedAAH = 117110677 / 209459250 := by
  unfold sourceExecutableExpectedAAH
  simp_rw [sourceConditionalAAH_order_average]
  rw [SourceFourRanking.sum_twenty_four]
  simp_rw [sourceFourCandidate_sum_four]
  norm_num [sourceAlgorithmMallowsMass, sourceHumanTopCandidateMass,
    sourceHumanNextCandidateMass, sourceExpectedOrderStatisticValue,
    sourceBestAvailableAfterOne, sourceBestAvailableAfterTwo,
    sourceFirstNotTwo, sourceFourRankingAt, Fin.ext_iff]

theorem source_executable_expectedHAH_eq :
    sourceExecutableExpectedHAH = 2539918857979 / 4642664276250 := by
  unfold sourceExecutableExpectedHAH
  simp_rw [sourceConditionalHAH_order_average]
  rw [SourceFourRanking.sum_twenty_four]
  simp_rw [sourceFourCandidate_sum_four]
  norm_num [sourceAlgorithmMallowsMass, sourceHumanTopCandidateMass,
    sourceHumanNextCandidateMass, sourceHumanExpectedFirstValue,
    sourceHumanExpectedAfterOneValue, sourceHumanExpectedAfterTwoValue,
    sourceBestAvailableAfterOne, sourceFourRankingAt, Fin.ext_iff]

theorem source_executable_expectedAHH_eq :
    sourceExecutableExpectedAHH = 42778976113 / 74881681875 := by
  unfold sourceExecutableExpectedAHH
  simp_rw [sourceConditionalAHH_order_average]
  rw [SourceFourRanking.sum_twenty_four]
  simp_rw [sourceFourCandidate_sum_four]
  norm_num [sourceAlgorithmMallowsMass, sourceHumanTopCandidateMass,
    sourceHumanNextCandidateMass, sourceExpectedOrderStatisticValue,
    sourceBestAvailableAfterOne, sourceBestAvailableAfterTwo,
    sourceFirstNotTwo, sourceFourRankingAt, Fin.ext_iff]

theorem source_executable_expectedHHH_eq :
    sourceExecutableExpectedHHH =
      8730423441013 / 15807166464375 := by
  unfold sourceExecutableExpectedHHH
  rw [sourceConditionalHHH_order_average]
  simp_rw [sourceFourCandidate_sum_four]
  norm_num [sourceHumanTopCandidateMass, sourceHumanNextCandidateMass,
    sourceHumanExpectedFirstValue, sourceHumanExpectedAfterOneValue,
    sourceHumanExpectedAfterTwoValue, Fin.ext_iff]

theorem source_executable_algorithmGain_AA_eq :
    sourceExecutableExpectedAAA - sourceExecutableExpectedHAA =
      543376 / 104729625 := by
  rw [source_executable_expectedAAA_eq, source_executable_expectedHAA_eq]
  norm_num

theorem source_executable_algorithmGain_AH_eq :
    sourceExecutableExpectedAAH - sourceExecutableExpectedHAH =
      1034061069 / 85975264375 := by
  rw [source_executable_expectedAAH_eq, source_executable_expectedHAH_eq]
  norm_num

theorem source_executable_algorithmGain_HH_eq :
    sourceExecutableExpectedAHH - sourceExecutableExpectedHHH =
      6300308847656 / 331950495751875 := by
  rw [source_executable_expectedAHH_eq, source_executable_expectedHHH_eq]
  norm_num

/-! ## Compact real-valued paper interface -/

/-! ### Signed-welfare observation -/

/-- Adding a constant to every candidate value adds twice that constant to shared welfare. -/
theorem expectedWelfareShared_add_const {n : ℕ}
    (mu : PMF (Ranking n)) (value : Candidate n → ℝ) (shift : ℝ) :
    expectedWelfareShared mu (fun c => value c + shift) =
      expectedWelfareShared mu value + 2 * shift := by
  unfold expectedWelfareShared
    AppliedModelingLib.SocialChoice.Ranking.expectedWelfareShared
  rw [show
    (fun pi =>
      AppliedModelingLib.SocialChoice.Ranking.welfareOrdered
        (fun c => value c + shift) pi pi) =
      (fun pi =>
        AppliedModelingLib.SocialChoice.Ranking.welfareOrdered value pi pi +
          2 * shift) by
      funext pi
      simp [AppliedModelingLib.SocialChoice.Ranking.welfareOrdered,
        AppliedModelingLib.SocialChoice.Ranking.secondMoverUtility]
      ring]
  rw [pmfExp_add]
  simp

/-- Adding a constant to values also adds twice that constant to independent welfare. -/
theorem expectedWelfareOrdered_add_const {n : ℕ}
    (muSecond muFirst : PMF (Ranking n))
    (value : Candidate n → ℝ) (shift : ℝ) :
    expectedWelfareOrdered muSecond muFirst (fun c => value c + shift) =
      expectedWelfareOrdered muSecond muFirst value + 2 * shift := by
  unfold expectedWelfareOrdered
    AppliedModelingLib.SocialChoice.Ranking.welfareOrdered
  have hintegrand :
      (fun pi sigma =>
        (value (firstChoice sigma) + shift) +
          secondMoverUtility (fun c => value c + shift) pi sigma) =
        (fun pi sigma =>
          value (firstChoice sigma) + secondMoverUtility value pi sigma +
            2 * shift) := by
    funext pi sigma
    simp [secondMoverUtility]
    ring
  rw [hintegrand]
  rw [pmfPairExp_add]
  simp

/--
The source's signed-utility observation: any strict all-human welfare advantage
can be translated so that all-algorithm welfare is negative while all-human
welfare remains positive.  Translation does not alter any ranking law or
welfare difference.
-/
theorem signed_welfare_sign_reversal_of_strict_gap {n : ℕ}
    (algorithmLaw humanLaw : PMF (Ranking n))
    (value : Candidate n → ℝ)
    (hgap : expectedWelfareShared algorithmLaw value <
      expectedWelfareOrdered humanLaw humanLaw value) :
    ∃ shift,
      expectedWelfareShared algorithmLaw (fun c => value c + shift) < 0 ∧
        0 < expectedWelfareOrdered humanLaw humanLaw
          (fun c => value c + shift) := by
  let lower := expectedWelfareShared algorithmLaw value
  let upper := expectedWelfareOrdered humanLaw humanLaw value
  let shift := -(lower + upper) / 4
  refine ⟨shift, ?_, ?_⟩
  · rw [expectedWelfareShared_add_const]
    dsimp [shift, lower, upper]
    linarith
  · rw [expectedWelfareOrdered_add_const]
    dsimp [shift, lower, upper]
    linarith

/-- The focal firm's two opponents, up to permutation. -/
inductive ThreeFirmOpponentProfile where
  | algorithmAlgorithm
  | algorithmHuman
  | humanHuman
  deriving DecidableEq, Fintype

/-- Exact per-firm utility at the source example's all-algorithm profile. -/
noncomputable def sourceThreeFirmAllAlgorithmPerFirm : ℝ := 124 / 225

/-- Exact per-firm utility at the source example's all-human profile. -/
noncomputable def sourceThreeFirmAllHumanPerFirm : ℝ :=
  8730423441013 / 15807166464375

/--
Exact gain from a unilateral switch from human to algorithm, indexed by the
other two firms' strategies.  The mixed profile covers either opponent order.
-/
noncomputable def sourceThreeFirmAlgorithmGain : ThreeFirmOpponentProfile → ℝ
  | .algorithmAlgorithm => 543376 / 104729625
  | .algorithmHuman => 1034061069 / 85975264375
  | .humanHuman => 6300308847656 / 331950495751875

/-- The source example's all-human advantage is exactly positive. -/
theorem source_threeFirm_allHuman_advantage_exact :
    sourceThreeFirmAllHumanPerFirm - sourceThreeFirmAllAlgorithmPerFirm =
      18918367313 / 15807166464375 := by
  norm_num [sourceThreeFirmAllHumanPerFirm, sourceThreeFirmAllAlgorithmPerFirm]

/-- All-human per-firm utility is strictly higher than all-algorithm utility. -/
theorem source_threeFirm_allAlgorithm_lt_allHuman :
    sourceThreeFirmAllAlgorithmPerFirm < sourceThreeFirmAllHumanPerFirm := by
  norm_num [sourceThreeFirmAllHumanPerFirm, sourceThreeFirmAllAlgorithmPerFirm]

/-- Every enumerated opponent profile gives a strictly positive algorithm gain. -/
theorem source_threeFirm_algorithmGain_pos
    (opponents : ThreeFirmOpponentProfile) :
    0 < sourceThreeFirmAlgorithmGain opponents := by
  cases opponents <;> norm_num [sourceThreeFirmAlgorithmGain]

/--
Internal arithmetic certificate for the collapsed rank-mean witness. It does
not establish the source three-firm equilibrium or welfare claim.
-/
theorem source_threeFirm_arithmetic_paradox :
    (forall opponents, 0 < sourceThreeFirmAlgorithmGain opponents) ∧
      sourceThreeFirmAllAlgorithmPerFirm < sourceThreeFirmAllHumanPerFirm := by
  exact ⟨source_threeFirm_algorithmGain_pos,
    source_threeFirm_allAlgorithm_lt_allHuman⟩

/-- The compact all-algorithm constant is the cast of the collapsed expectation. -/
theorem source_threeFirm_allAlgorithm_from_executable :
    (sourceExecutableExpectedAAA : ℝ) = sourceThreeFirmAllAlgorithmPerFirm := by
  rw [source_executable_expectedAAA_eq]
  norm_num [sourceThreeFirmAllAlgorithmPerFirm]

/-- The compact all-human constant is the cast of the collapsed expectation. -/
theorem source_threeFirm_allHuman_from_executable :
    (sourceExecutableExpectedHHH : ℝ) = sourceThreeFirmAllHumanPerFirm := by
  rw [source_executable_expectedHHH_eq]
  norm_num [sourceThreeFirmAllHumanPerFirm]

/--
The focal rank-mean gain in the collapsed finite evaluator. The profile names
record the other two firms' choices up to their order.
-/
def sourceExecutableAlgorithmGain : ThreeFirmOpponentProfile → ℚ
  | .algorithmAlgorithm => sourceExecutableExpectedAAA - sourceExecutableExpectedHAA
  | .algorithmHuman => sourceExecutableExpectedAAH - sourceExecutableExpectedHAH
  | .humanHuman => sourceExecutableExpectedAHH - sourceExecutableExpectedHHH

/-- Every collapsed unilateral-gain row is strictly positive. -/
theorem source_executable_algorithmGain_pos
    (opponents : ThreeFirmOpponentProfile) :
    0 < (sourceExecutableAlgorithmGain opponents : ℝ) := by
  cases opponents
  · rw [sourceExecutableAlgorithmGain, source_executable_algorithmGain_AA_eq]
    norm_num
  · rw [sourceExecutableAlgorithmGain, source_executable_algorithmGain_AH_eq]
    norm_num
  · rw [sourceExecutableAlgorithmGain, source_executable_algorithmGain_HH_eq]
    norm_num

/-- The collapsed all-algorithm row is lower than the collapsed all-human row. -/
theorem source_executable_allAlgorithm_lt_allHuman :
    (sourceExecutableExpectedAAA : ℝ) < sourceExecutableExpectedHHH := by
  rw [source_executable_expectedAAA_eq, source_executable_expectedHHH_eq]
  norm_num

/-- Every compact unilateral-gain constant is derived from the collapsed evaluator. -/
theorem source_threeFirm_algorithmGain_from_executable
    (opponents : ThreeFirmOpponentProfile) :
    (sourceExecutableAlgorithmGain opponents : ℝ) =
      sourceThreeFirmAlgorithmGain opponents := by
  cases opponents
  · rw [sourceExecutableAlgorithmGain, source_executable_algorithmGain_AA_eq]
    norm_num [sourceThreeFirmAlgorithmGain]
  · rw [sourceExecutableAlgorithmGain, source_executable_algorithmGain_AH_eq]
    norm_num [sourceThreeFirmAlgorithmGain]
  · rw [sourceExecutableAlgorithmGain, source_executable_algorithmGain_HH_eq]
    norm_num [sourceThreeFirmAlgorithmGain]

end KR21Monoculture
