import KR21Monoculture.WeakCompetition
import KR21Monoculture.Kendall
import AppliedModelingLib.SocialChoice.Ranking.Mallows
import Mathlib.Algebra.BigOperators.Field

open scoped BigOperators
open AppliedModelingLib

namespace KR21Monoculture

/--
Unnormalised real Mallows weight.  This file uses the inverse of the paper
parameter: if the paper writes mass proportional to `Φ^{-d}` with `Φ > 1`,
then this file writes the same mass as `q^d` with `q = Φ⁻¹` and `0 < q < 1`.
-/
noncomputable def mallowsWeight {n : ℕ} (q : ℝ) (ρ π : Ranking n) : ℝ := q ^ kendallTau ρ π

@[simp] theorem mallowsWeight_center {n : ℕ} (q : ℝ) (ρ : Ranking n) :
    mallowsWeight q ρ ρ = 1 := by
  simp [mallowsWeight]

/-- The finite partition function for the real-weight Mallows kernel. -/
noncomputable def mallowsPartition {n : ℕ} (q : ℝ) (ρ : Ranking n) : ℝ := ∑ π : Ranking n, mallowsWeight q ρ π

/--
A Mallows distribution packaged as an actual `PMF` plus the real finite-sum facts
that identify its probabilities with normalized Mallows weights.

This deliberately avoids making the first implementation depend on a delicate
`ENNReal` construction.  A later file can replace this specification with a
constructor using `PMF.ofFintype` or `PMF.normalize`.
-/
structure MallowsSpec (n : ℕ) where
  center : Ranking n
  /-- Inverse Mallows parameter `q`; the paper's parameter is `q⁻¹`. -/
  q : ℝ
  law : PMF (Ranking n)
  partition : ℝ
  q_pos : 0 < q
  partition_pos : 0 < partition
  partition_eq_sum : partition = mallowsPartition q center
  law_apply_toReal : ∀ π : Ranking n,
    (law π).toReal = mallowsWeight q center π / partition

namespace MallowsSpec

variable {n : ℕ} (M : MallowsSpec n)

/-- The true/central first candidate. -/
def centerFirst : Candidate n := firstChoice M.center

/-- The true/central second candidate. -/
def centerSecond : Candidate n := secondChoice M.center

@[simp] theorem partition_ne_zero : M.partition ≠ 0 :=  ne_of_gt M.partition_pos

/--
Shared-library view of the KR-local Mallows specification.

The KR file keeps its local structure so downstream paper proofs can continue
rewriting with fields such as `M.partition_eq_sum`.  This adapter is the
preferred route when a proof only needs reusable Mallows law facts.
-/
def toShared : AppliedModelingLib.SocialChoice.Ranking.MallowsSpec n where
  center := M.center
  q := M.q
  law := M.law
  partition := M.partition
  q_pos := M.q_pos
  partition_pos := M.partition_pos
  partition_eq_sum := by
    simpa [AppliedModelingLib.SocialChoice.Ranking.mallowsPartition,
      AppliedModelingLib.SocialChoice.Ranking.mallowsWeight, mallowsPartition,
      mallowsWeight, AppliedModelingLib.SocialChoice.Ranking.kendallTau, kendallTau]
      using M.partition_eq_sum
  law_apply_toReal := by
    intro π
    simpa [AppliedModelingLib.SocialChoice.Ranking.mallowsWeight, mallowsWeight,
      AppliedModelingLib.SocialChoice.Ranking.kendallTau, kendallTau]
      using M.law_apply_toReal π

/-- The unnormalised mass of rankings whose first choice is `c`. -/
noncomputable def firstWeight (c : Candidate n) : ℝ :=
  ∑ π : Ranking n,
    if c = firstChoice π then mallowsWeight M.q M.center π else 0

/-- The unnormalised mass of rankings whose first two choices are `c,d`. -/
noncomputable def firstSecondWeight (c d : Candidate n) : ℝ :=
  ∑ π : Ranking n,
    if c = firstChoice π ∧ d = secondChoice π
    then mallowsWeight M.q M.center π
    else 0

/-- First-choice probabilities reduce to finite Mallows weights. -/
theorem firstChoiceProb_eq_firstWeight_div_partition (c : Candidate n) :
    firstChoiceProb M.law c = M.firstWeight c / M.partition := by
  simpa [firstChoiceProb, AppliedModelingLib.SocialChoice.Ranking.firstChoiceProb]
    using (M.toShared).firstChoiceProb_eq_firstWeight_div_partition c

/-- Probability that a Mallows draw begins with the ordered pair `(c,d)`. -/
noncomputable def firstSecondChoiceProb (c d : Candidate n) : ℝ := pmfProb M.law (fun π => c = firstChoice π ∧ d = secondChoice π)

/-- Unnormalised mass of rankings that correctly order the center-ordered pair
`(c,d)`.  The guard `rankOf M.center c < rankOf M.center d` keeps the definition
paper-facing: `c` is the better item and `d` is the worse item. -/
noncomputable def pairCorrectWeight (c d : Candidate n) : ℝ :=
  ∑ π : Ranking n,
    if rankOf M.center c < rankOf M.center d ∧ rankOf π c < rankOf π d
    then mallowsWeight M.q M.center π
    else 0

/-- Probability that a Mallows draw correctly orders the center-ordered pair
`(c,d)`. -/
noncomputable def pairCorrectProb (c d : Candidate n) : ℝ :=
  pmfProb M.law
    (fun π => rankOf M.center c < rankOf M.center d ∧
      rankOf π c < rankOf π d)

/-- Unnormalised mass of rankings that incorrectly order the center-ordered
pair `(c,d)`. -/
noncomputable def pairWrongWeight (c d : Candidate n) : ℝ :=
  ∑ π : Ranking n,
    if rankOf M.center c < rankOf M.center d ∧ rankOf π d < rankOf π c
    then mallowsWeight M.q M.center π
    else 0

/-- Probability that a Mallows draw incorrectly orders the center-ordered pair
`(c,d)`. -/
noncomputable def pairWrongProb (c d : Candidate n) : ℝ :=
  pmfProb M.law
    (fun π => rankOf M.center c < rankOf M.center d ∧
      rankOf π d < rankOf π c)

@[simp] theorem toShared_firstWeight (c : Candidate n) :
    (M.toShared).firstWeight c = M.firstWeight c := by
  rfl

@[simp] theorem toShared_firstSecondWeight (c d : Candidate n) :
    (M.toShared).firstSecondWeight c d = M.firstSecondWeight c d := by
  rfl

@[simp] theorem toShared_pairCorrectWeight (c d : Candidate n) :
    (M.toShared).pairCorrectWeight c d = M.pairCorrectWeight c d := by
  rfl

@[simp] theorem toShared_pairWrongWeight (c d : Candidate n) :
    (M.toShared).pairWrongWeight c d = M.pairWrongWeight c d := by
  rfl

/-- First/second-choice probabilities reduce to finite Mallows weights. -/
theorem firstSecondChoiceProb_eq_firstSecondWeight_div_partition
    (c d : Candidate n) :
    M.firstSecondChoiceProb c d = M.firstSecondWeight c d / M.partition := by
  simpa [firstSecondChoiceProb,
    AppliedModelingLib.SocialChoice.Ranking.MallowsSpec.firstSecondChoiceProb]
    using (M.toShared).firstSecondChoiceProb_eq_firstSecondWeight_div_partition c d

/-- Pair-correct probabilities reduce to finite Mallows weights. -/
theorem pairCorrectProb_eq_pairCorrectWeight_div_partition
    (c d : Candidate n) :
    M.pairCorrectProb c d = M.pairCorrectWeight c d / M.partition := by
  simpa [pairCorrectProb,
    AppliedModelingLib.SocialChoice.Ranking.MallowsSpec.pairCorrectProb]
    using (M.toShared).pairCorrectProb_eq_pairCorrectWeight_div_partition c d

/-- Pair-wrong probabilities reduce to finite Mallows weights. -/
theorem pairWrongProb_eq_pairWrongWeight_div_partition
    (c d : Candidate n) :
    M.pairWrongProb c d = M.pairWrongWeight c d / M.partition := by
  simpa [pairWrongProb,
    AppliedModelingLib.SocialChoice.Ranking.MallowsSpec.pairWrongProb]
    using (M.toShared).pairWrongProb_eq_pairWrongWeight_div_partition c d

/-- Correct and wrong pair-order weights partition the Mallows mass for a
center-ordered pair. -/
theorem pairCorrectWeight_add_pairWrongWeight_eq_partition
    {c d : Candidate n} (hcd : rankOf M.center c < rankOf M.center d) :
    M.pairCorrectWeight c d + M.pairWrongWeight c d = M.partition := by
  simpa using (M.toShared).pairCorrectWeight_add_pairWrongWeight_eq_partition hcd

/-- Correct pair probability as normalized correct-vs-wrong pair mass. -/
theorem pairCorrectProb_eq_pairCorrectWeight_div_correct_add_wrong
    {c d : Candidate n} (hcd : rankOf M.center c < rankOf M.center d) :
    M.pairCorrectProb c d =
      M.pairCorrectWeight c d /
        (M.pairCorrectWeight c d + M.pairWrongWeight c d) := by
  rw [M.pairCorrectProb_eq_pairCorrectWeight_div_partition]
  rw [M.pairCorrectWeight_add_pairWrongWeight_eq_partition hcd]

/-- The first-choice weights partition the Mallows partition function. -/
theorem sum_firstWeight_eq_partition :
    (∑ c : Candidate n, M.firstWeight c) = M.partition := by
  simpa using (M.toShared).sum_firstWeight_eq_partition

/-- For a fixed first candidate, summing over second candidates recovers first mass. -/
theorem sum_firstSecondWeight_right_eq_firstWeight (c : Candidate n) :
    (∑ d : Candidate n, M.firstSecondWeight c d) = M.firstWeight c := by
  simpa using (M.toShared).sum_firstSecondWeight_right_eq_firstWeight c

/-- The probability version of `sum_firstSecondWeight_right_eq_firstWeight`. -/
theorem sum_firstSecondChoiceProb_right_eq_firstChoiceProb (c : Candidate n) :
    (∑ d : Candidate n, M.firstSecondChoiceProb c d) = firstChoiceProb M.law c := by
  simpa [firstChoiceProb, AppliedModelingLib.SocialChoice.Ranking.firstChoiceProb,
    firstSecondChoiceProb,
    AppliedModelingLib.SocialChoice.Ranking.MallowsSpec.firstSecondChoiceProb]
    using (M.toShared).sum_firstSecondChoiceProb_right_eq_firstChoiceProb c

/-- First-choice probability of the center's first candidate in weight form. -/
theorem centerFirstProb_eq :
    firstChoiceProb M.law M.centerFirst = M.firstWeight M.centerFirst / M.partition :=
  M.firstChoiceProb_eq_firstWeight_div_partition M.centerFirst

/-- First/second probability of the center's first two candidates in weight form. -/
theorem centerFirstSecondProb_eq :
    M.firstSecondChoiceProb M.centerFirst M.centerSecond =
      M.firstSecondWeight M.centerFirst M.centerSecond / M.partition :=
  M.firstSecondChoiceProb_eq_firstSecondWeight_div_partition M.centerFirst M.centerSecond

end MallowsSpec

/--
Two Mallows laws meant to represent the algorithmic and human rankings around the
same central/true ranking.
-/
structure MallowsComparison (n : ℕ) where
  algorithm : MallowsSpec n
  human : MallowsSpec n
  same_center : algorithm.center = human.center

namespace MallowsComparison

variable {n : ℕ} (C : MallowsComparison n)

/-- The induced two-strategy model for a fixed pointwise value vector. -/
noncomputable def toModel (value : Candidate n → ℝ) : Model n where
  algorithmRanking := C.algorithm.law
  humanRanking := C.human.law
  value := value

/--
Algorithm is the lower-`q` / more concentrated law, as a data-level predicate.
Here `q` is the inverse of the paper's `Φ`, so lower means more accurate.
-/
def AlgorithmNoiselessOrMoreConcentrated : Prop := C.algorithm.q ≤ C.human.q

/--
The finite Mallows lemmas needed by the existing algebraic core.

The paper proves these from the Mallows finite-sum formulas.  In this repo they
are isolated as the exact local proof obligations that remain after the reusable
utility identities are in place.
-/
structure FiniteLemmaCertificate (value : Candidate n → ℝ) : Prop where
  independent_reranking_gain_pos_algorithm :
    0 < expectedRerankingGain C.algorithm.law value
  independent_reranking_gain_pos_human :
    0 < expectedRerankingGain C.human.law value
  weaker_competition_collision_sum_pos :
    0 < pmfExp C.human.law
      (fun π =>
        (firstChoiceProb C.algorithm.law (firstChoice π) -
            firstChoiceProb C.human.law (firstChoice π)) * valueGap value π)

/-- The certificate gives Definition 2 for the algorithm/Mallows law. -/
theorem algorithm_prefersIndependentReranking_of_certificate
    {value : Candidate n → ℝ} (cert : C.FiniteLemmaCertificate value) :
    Model.PrefersIndependentReranking C.algorithm.law value :=
   (prefersIndependentReranking_iff_expectedRerankingGain_pos
    (μ := C.algorithm.law) (value := value)).2
      cert.independent_reranking_gain_pos_algorithm

/-- The certificate also records Definition 2 for the human/Mallows law. -/
theorem human_prefersIndependentReranking_of_certificate
    {value : Candidate n → ℝ} (cert : C.FiniteLemmaCertificate value) :
    Model.PrefersIndependentReranking C.human.law value :=
   (prefersIndependentReranking_iff_expectedRerankingGain_pos
    (μ := C.human.law) (value := value)).2
      cert.independent_reranking_gain_pos_human

/-- The certificate gives Definition 3 for algorithmic-vs-human Mallows laws. -/
theorem prefersWeakerCompetition_of_certificate
    {value : Candidate n → ℝ} (cert : C.FiniteLemmaCertificate value) :
    Model.PrefersWeakerCompetition C.algorithm.law C.human.law value :=
   (prefersWeakerCompetition_iff_expected_collision_loss_diff_pos
    (μBetter := C.algorithm.law) (μWorse := C.human.law) (value := value)).2
      cert.weaker_competition_collision_sum_pos

/-- The local Mallows finite lemmas imply the paper-level fixed-parameter hypotheses. -/
theorem paperHypotheses_of_certificate
    {value : Candidate n → ℝ} (cert : C.FiniteLemmaCertificate value) :
    Model.PaperHypotheses (C.toModel value) := by
  constructor
  · exact C.algorithm_prefersIndependentReranking_of_certificate cert
  · exact C.prefersWeakerCompetition_of_certificate cert

end MallowsComparison

end KR21Monoculture
