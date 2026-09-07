import Mathlib.Data.Finset.Prod
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sigmoid

/-!
# Finite Pairwise-Comparison Counts

This module represents aggregate directed counts over a finite alternative set,
separately from sampled contextual preference observations. The representation
is suitable for random-utility maximum-likelihood models: diagonal counts are
ruled out, likelihoods range over the finite off-diagonal pair set, and score
shifts leave every comparison probability and the likelihood unchanged.

## Main declarations

- `PairwiseCountDataset`
- `pairwiseLogLikelihood`
- `PairwiseCountDataset.isPairwiseMLE`
-/

open scoped BigOperators

namespace AppliedModelingLib
namespace Learning
namespace HumanFeedback

/--
The optimization-relevant directed counts from a finite comparison dataset.
Diagonal reports may occur in the source sampling model, but their
log-likelihood contribution is constant in the score vector, so this sufficient
statistic omits them.
-/
structure PairwiseCountDataset (Alternative : Type*) where
  /-- Number of observations in which the first alternative beat the second. -/
  count : Alternative → Alternative → ℕ
  /-- Diagonal observations are omitted from the optimization statistic. -/
  diagonal_zero : ∀ alternative, count alternative alternative = 0

namespace PairwiseCountDataset

/-- Two aggregate datasets are equal when all their directed counts agree. -/
theorem ext {Alternative : Type*} {firstDataset secondDataset : PairwiseCountDataset Alternative}
    (hcount : ∀ first second,
      firstDataset.count first second = secondDataset.count first second) :
    firstDataset = secondDataset := by
  cases firstDataset with
  | mk firstCount firstDiagonal =>
    cases secondDataset with
    | mk secondCount secondDiagonal =>
      have hfunctions : firstCount = secondCount := by
        funext first second
        exact hcount first second
      subst secondCount
      rfl

/--
The CDF-like link used by the source's general pairwise random-utility model.
It records the exact requirements stated after Eq. (1), independently of the
stronger strict-monotonicity, continuity, and strict-log-concavity hypotheses
that individual results impose later.
-/
structure CDFLikePairwiseLink where
  /-- Probability assigned to a real score difference. -/
  toFun : ℝ → ℝ
  nonneg : ∀ gap, 0 ≤ toFun gap
  le_one : ∀ gap, toFun gap ≤ 1
  monotone : Monotone toFun
  complementary : ∀ gap, toFun (-gap) + toFun gap = 1
  tendsto_atBot_zero : Filter.Tendsto toFun Filter.atBot (nhds 0)
  tendsto_atTop_one : Filter.Tendsto toFun Filter.atTop (nhds 1)

instance : CoeFun CDFLikePairwiseLink (fun _ => ℝ → ℝ) where
  coe link := link.toFun

/-- The logistic Bradley--Terry link as a CDF-like pairwise link. -/
noncomputable def sigmoidCDFLikePairwiseLink : CDFLikePairwiseLink where
  toFun := Real.sigmoid
  nonneg := Real.sigmoid_nonneg
  le_one := Real.sigmoid_le_one
  monotone := Real.sigmoid_monotone
  complementary := by
    intro gap
    rw [Real.sigmoid_neg]
    ring
  tendsto_atBot_zero := Real.tendsto_sigmoid_atBot
  tendsto_atTop_one := Real.tendsto_sigmoid_atTop

/-- The logistic CDF-like link is continuous. -/
theorem continuous_sigmoidCDFLikePairwiseLink :
    Continuous (sigmoidCDFLikePairwiseLink : ℝ → ℝ) :=
  continuous_sigmoid

/-- The logistic CDF-like link is strictly increasing. -/
theorem strictMono_sigmoidCDFLikePairwiseLink :
    StrictMono (sigmoidCDFLikePairwiseLink : ℝ → ℝ) :=
  Real.sigmoid_strictMono

/-- A strictly monotone CDF-like pairwise link takes every finite gap to `(0, 1)`. -/
theorem CDFLikePairwiseLink.openProbability
    (link : CDFLikePairwiseLink) (hstrict : StrictMono (link : ℝ → ℝ))
    (gap : ℝ) : link gap ∈ Set.Ioo (0 : ℝ) 1 := by
  constructor
  · have hlt : link (gap - 1) < link gap := hstrict (by linarith)
    exact lt_of_le_of_lt (link.nonneg (gap - 1)) hlt
  · have hlt : link gap < link (gap + 1) := hstrict (by linarith)
    exact lt_of_lt_of_le hlt (link.le_one (gap + 1))

/-- A continuous CDF-like link realizes every probability strictly between its endpoints. -/
theorem CDFLikePairwiseLink.exists_eq_of_mem_Ioo
    (link : CDFLikePairwiseLink) (hcontinuous : Continuous (link : ℝ → ℝ))
    {probability : ℝ} (hprobability : probability ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ gap : ℝ, link gap = probability := by
  rcases (isPreconnected_univ.intermediate_value_Ioo
    (l₁ := Filter.atBot) (l₂ := Filter.atTop)
    (by simp) (by simp) hcontinuous.continuousOn
    link.tendsto_atBot_zero link.tendsto_atTop_one hprobability) with ⟨gap, -, hgap⟩
  exact ⟨gap, hgap⟩

/-- The source comparison graph has an edge exactly for a positive directed count. -/
def edge {Alternative : Type*} (dataset : PairwiseCountDataset Alternative)
    (first second : Alternative) : Prop :=
  0 < dataset.count first second

/-- A comparison-graph edge joins distinct alternatives. -/
theorem edge_ne {Alternative : Type*} (dataset : PairwiseCountDataset Alternative)
    {first second : Alternative} (hedge : dataset.edge first second) : first ≠ second := by
  intro hsame
  subst second
  unfold edge at hedge
  rw [dataset.diagonal_zero first] at hedge
  exact Nat.lt_irrefl _ hedge

/-- The undirected form of the source comparison graph. -/
def adjacent {Alternative : Type*} (dataset : PairwiseCountDataset Alternative)
    (first second : Alternative) : Prop :=
  dataset.edge first second ∨ dataset.edge second first

/-- Reachability in the directed comparison graph, including the empty path. -/
def reaches {Alternative : Type*} (dataset : PairwiseCountDataset Alternative)
    (first second : Alternative) : Prop :=
  Relation.ReflTransGen dataset.edge first second

/-- Reachability in the undirected form of the comparison graph. -/
def connectedTo {Alternative : Type*} (dataset : PairwiseCountDataset Alternative)
    (first second : Alternative) : Prop :=
  Relation.ReflTransGen dataset.adjacent first second

/-- The source's connected comparison-graph condition. -/
def isConnected {Alternative : Type*} (dataset : PairwiseCountDataset Alternative) : Prop :=
  ∀ first second, dataset.connectedTo first second

/-- The source's directed strong-connectivity condition. -/
def isStronglyConnected {Alternative : Type*} (dataset : PairwiseCountDataset Alternative) : Prop :=
  ∀ first second, dataset.reaches first second

/-- Every undirected connected component is strongly connected in the source sense. -/
def everyComponentStronglyConnected {Alternative : Type*}
    (dataset : PairwiseCountDataset Alternative) : Prop :=
  ∀ first second, dataset.connectedTo first second → dataset.reaches first second

/-- A score vector uses one real utility coordinate per alternative. -/
abbrev ScoreVector (Alternative : Type*) := Alternative → ℝ

/--
Pointwise pooling of two aggregate comparison datasets. This is the dataset
sum `D = D₁ + D₂` in the source's separability definition.
-/
def add {Alternative : Type*} (firstDataset secondDataset : PairwiseCountDataset Alternative) :
    PairwiseCountDataset Alternative where
  count := fun first second => firstDataset.count first second + secondDataset.count first second
  diagonal_zero := by
    intro alternative
    rw [firstDataset.diagonal_zero alternative, secondDataset.diagonal_zero alternative]

/-- Pointwise counts of a pooled dataset are the sum of its component counts. -/
@[simp] theorem add_count
    {Alternative : Type*} (firstDataset secondDataset : PairwiseCountDataset Alternative)
    (first second : Alternative) :
    (firstDataset.add secondDataset).count first second =
      firstDataset.count first second + secondDataset.count first second :=
  rfl

/-- The random-utility probability that `first` beats `second` under a score link. -/
def randomUtilityWinProbability {Alternative : Type*}
    (link : ℝ → ℝ) (score : ScoreVector Alternative)
    (first second : Alternative) : ℝ :=
  link (score first - score second)

/-- Adding a common score shift leaves every score-difference probability unchanged. -/
theorem randomUtilityWinProbability_shift
    {Alternative : Type*} (link : ℝ → ℝ) (score : ScoreVector Alternative)
    (shift : ℝ) (first second : Alternative) :
    randomUtilityWinProbability link (fun alternative => score alternative + shift) first second =
      randomUtilityWinProbability link score first second := by
  unfold randomUtilityWinProbability
  congr 1
  ring

/-- The CDF-like symmetry condition lifts to complementary pairwise outcomes. -/
theorem randomUtilityWinProbability_add_swap
    {Alternative : Type*} (link : CDFLikePairwiseLink)
    (score : ScoreVector Alternative) (first second : Alternative) :
    randomUtilityWinProbability link score first second +
        randomUtilityWinProbability link score second first = 1 := by
  unfold randomUtilityWinProbability
  have hgap : score second - score first = -(score first - score second) := by ring
  rw [hgap]
  linarith [link.complementary (score first - score second)]

/--
The finite log likelihood from the source model, summed only over ordered
distinct pairs. The link is intentionally a caller-supplied real function:
range, symmetry, monotonicity, continuity, and log-concavity are distinct
source conditions used by different later results.
-/
noncomputable def pairwiseLogLikelihood
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (link : ℝ → ℝ)
    (score : ScoreVector Alternative) : ℝ :=
  ∑ pair ∈ (Finset.univ : Finset Alternative).offDiag,
    (dataset.count pair.1 pair.2 : ℝ) *
      Real.log (randomUtilityWinProbability link score pair.1 pair.2)

/--
Pooling datasets adds their finite log likelihoods at every fixed score vector.
This is the likelihood identity underlying the source's separability setup.
-/
theorem pairwiseLogLikelihood_add
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (firstDataset secondDataset : PairwiseCountDataset Alternative) (link : ℝ → ℝ)
    (score : ScoreVector Alternative) :
    pairwiseLogLikelihood (firstDataset.add secondDataset) link score =
      pairwiseLogLikelihood firstDataset link score +
        pairwiseLogLikelihood secondDataset link score := by
  unfold pairwiseLogLikelihood
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  rintro ⟨first, second⟩ _
  rw [add_count, Nat.cast_add, add_mul]

/--
Add a finite number of directed `winner ≻ loser` observations while preserving
the source model's zero diagonal. This is the dataset change in Definition 4.1
of Noothigattu--Peters--Procaccia (2020).
-/
def addDirectedCount {Alternative : Type*} [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative)
    (winner loser : Alternative) (added : ℕ) (hwinner_loser : winner ≠ loser) :
    PairwiseCountDataset Alternative where
  count := fun first second =>
    if first = winner ∧ second = loser then dataset.count first second + added
    else dataset.count first second
  diagonal_zero := by
    intro alternative
    by_cases htarget : alternative = winner ∧ alternative = loser
    · rcases htarget with ⟨hwinner, hloser⟩
      subst winner
      subst loser
      exact (hwinner_loser rfl).elim
    · rw [if_neg htarget]
      exact dataset.diagonal_zero alternative

/-- The targeted directed count increases by exactly the supplied natural amount. -/
@[simp] theorem addDirectedCount_count_winner_loser
    {Alternative : Type*} [DecidableEq Alternative] (dataset : PairwiseCountDataset Alternative)
    (winner loser : Alternative) (added : ℕ) (hwinner_loser : winner ≠ loser) :
    (dataset.addDirectedCount winner loser added hwinner_loser).count winner loser =
      dataset.count winner loser + added := by
  simp [addDirectedCount]

/-- Every directed count other than the targeted one is unchanged. -/
theorem addDirectedCount_count_eq_of_ne
    {Alternative : Type*} [DecidableEq Alternative] (dataset : PairwiseCountDataset Alternative)
    (winner loser : Alternative) (added : ℕ) (hwinner_loser : winner ≠ loser)
    {first second : Alternative} (hpair : (first, second) ≠ (winner, loser)) :
    (dataset.addDirectedCount winner loser added hwinner_loser).count first second =
      dataset.count first second := by
  change (if first = winner ∧ second = loser then dataset.count first second + added
    else dataset.count first second) = dataset.count first second
  rw [if_neg]
  rintro ⟨hfirst, hsecond⟩
  exact hpair (Prod.ext hfirst hsecond)

/--
The count-side premise of Definition 4.1: exactly one directed comparison
count has increased, with every other ordered count unchanged.
-/
def hasSinglePairCountIncrease {Alternative : Type*}
    (baseline updated : PairwiseCountDataset Alternative) (winner loser : Alternative) : Prop :=
  baseline.count winner loser < updated.count winner loser ∧
    ∀ first second, (first, second) ≠ (winner, loser) →
      updated.count first second = baseline.count first second

/-- A one-pair strict count increase necessarily concerns two distinct alternatives. -/
theorem hasSinglePairCountIncrease_ne
    {Alternative : Type*} (baseline updated : PairwiseCountDataset Alternative)
    {winner loser : Alternative}
    (hincrease : hasSinglePairCountIncrease baseline updated winner loser) : winner ≠ loser := by
  intro hsame
  subst loser
  have hlt : baseline.count winner winner < updated.count winner winner := hincrease.1
  rw [baseline.diagonal_zero winner, updated.diagonal_zero winner] at hlt
  exact Nat.lt_irrefl _ hlt

/-- A positive directed-count addition realizes the source's one-pair increase premise. -/
theorem addDirectedCount_hasSinglePairCountIncrease
    {Alternative : Type*} [DecidableEq Alternative] (dataset : PairwiseCountDataset Alternative)
    (winner loser : Alternative) (added : ℕ) (hwinner_loser : winner ≠ loser)
    (hadded : 0 < added) :
    hasSinglePairCountIncrease dataset
      (dataset.addDirectedCount winner loser added hwinner_loser) winner loser := by
  constructor
  · rw [addDirectedCount_count_winner_loser]
    omega
  · intro first second hpair
    exact addDirectedCount_count_eq_of_ne dataset winner loser added hwinner_loser hpair

/--
Any two finite datasets satisfying Definition 4.1's one-pair count premise are
exactly related by an `addDirectedCount` update. The added amount is the
positive natural difference of the designated directed counts.
-/
theorem exists_addDirectedCount_eq_of_hasSinglePairCountIncrease
    {Alternative : Type*} [DecidableEq Alternative]
    (baseline updated : PairwiseCountDataset Alternative) (winner loser : Alternative)
    (hincrease : hasSinglePairCountIncrease baseline updated winner loser) :
    ∃ added : ℕ, 0 < added ∧
      updated = baseline.addDirectedCount winner loser added
        (hasSinglePairCountIncrease_ne baseline updated hincrease) := by
  let added : ℕ := updated.count winner loser - baseline.count winner loser
  have hadded : 0 < added := by
    dsimp [added]
    exact Nat.sub_pos_of_lt hincrease.1
  refine ⟨added, hadded, ?_⟩
  apply PairwiseCountDataset.ext
  intro first second
  by_cases htarget : (first, second) = (winner, loser)
  · have hfirst : first = winner := congrArg Prod.fst htarget
    have hsecond : second = loser := congrArg Prod.snd htarget
    subst first
    subst second
    rw [addDirectedCount_count_winner_loser]
    dsimp [added]
    omega
  · rw [hincrease.2 first second htarget,
      addDirectedCount_count_eq_of_ne baseline winner loser added
        (hasSinglePairCountIncrease_ne baseline updated hincrease) htarget]

/--
The likelihood under a single directed-count addition is the old likelihood
plus exactly the new count times the corresponding log win probability. This
is the first identity in Supplement D's proof of Theorem 4.2.
-/
theorem pairwiseLogLikelihood_addDirectedCount
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (link : ℝ → ℝ)
    (score : ScoreVector Alternative) (winner loser : Alternative) (added : ℕ)
    (hwinner_loser : winner ≠ loser) :
    pairwiseLogLikelihood (dataset.addDirectedCount winner loser added hwinner_loser) link score =
      pairwiseLogLikelihood dataset link score + (added : ℝ) *
        Real.log (randomUtilityWinProbability link score winner loser) := by
  classical
  let offDiagonalPairs : Finset (Alternative × Alternative) :=
    (Finset.univ : Finset Alternative).offDiag
  let oldTerm : Alternative × Alternative → ℝ := fun pair =>
    (dataset.count pair.1 pair.2 : ℝ) *
      Real.log (randomUtilityWinProbability link score pair.1 pair.2)
  let newTerm : Alternative × Alternative → ℝ := fun pair =>
    ((dataset.addDirectedCount winner loser added hwinner_loser).count pair.1 pair.2 : ℝ) *
      Real.log (randomUtilityWinProbability link score pair.1 pair.2)
  have htarget : (winner, loser) ∈ offDiagonalPairs := by
    exact Finset.mem_offDiag.2 ⟨Finset.mem_univ winner, Finset.mem_univ loser,
      hwinner_loser⟩
  have hnewSplit :
      (∑ pair ∈ offDiagonalPairs, newTerm pair) =
        newTerm (winner, loser) +
          ∑ pair ∈ offDiagonalPairs \ {(winner, loser)}, newTerm pair := by
    exact Finset.sum_eq_add_sum_diff_singleton (winner, loser) newTerm
      (fun hnot => (hnot htarget).elim)
  have holdSplit :
      (∑ pair ∈ offDiagonalPairs, oldTerm pair) =
        oldTerm (winner, loser) +
          ∑ pair ∈ offDiagonalPairs \ {(winner, loser)}, oldTerm pair := by
    exact Finset.sum_eq_add_sum_diff_singleton (winner, loser) oldTerm
      (fun hnot => (hnot htarget).elim)
  have houtside :
      (∑ pair ∈ offDiagonalPairs \ {(winner, loser)}, newTerm pair) =
        ∑ pair ∈ offDiagonalPairs \ {(winner, loser)}, oldTerm pair := by
    refine Finset.sum_congr rfl ?_
    intro pair hpair
    have hne : pair ≠ (winner, loser) := by
      simpa using (Finset.mem_sdiff.mp hpair).2
    dsimp [newTerm, oldTerm]
    rw [addDirectedCount_count_eq_of_ne dataset winner loser added hwinner_loser hne]
  have htargetTerm :
      newTerm (winner, loser) = oldTerm (winner, loser) + (added : ℝ) *
        Real.log (randomUtilityWinProbability link score winner loser) := by
    dsimp [newTerm, oldTerm]
    rw [addDirectedCount_count_winner_loser]
    push_cast
    ring
  change (∑ pair ∈ offDiagonalPairs, newTerm pair) =
    (∑ pair ∈ offDiagonalPairs, oldTerm pair) + (added : ℝ) *
      Real.log (randomUtilityWinProbability link score winner loser)
  rw [hnewSplit, holdSplit, houtside, htargetTerm]
  ring

/-- The pairwise log likelihood is invariant under a common additive score shift. -/
theorem pairwiseLogLikelihood_shift
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (link : ℝ → ℝ)
    (score : ScoreVector Alternative) (shift : ℝ) :
    pairwiseLogLikelihood dataset link (fun alternative => score alternative + shift) =
      pairwiseLogLikelihood dataset link score := by
  unfold pairwiseLogLikelihood
  refine Finset.sum_congr rfl ?_
  rintro ⟨first, second⟩ _
  rw [randomUtilityWinProbability_shift]

/-- The source's reference-alternative normalization for score vectors. -/
def isReferenceNormalized {Alternative : Type*}
    (reference : Alternative) (score : ScoreVector Alternative) : Prop :=
  score reference = 0

/--
An MLE under the source's fixed-reference convention: a reference-normalized
score vector maximizing the finite pairwise log likelihood over the same
normalization set.
-/
def isPairwiseMLE
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (link : ℝ → ℝ)
    (reference : Alternative) (score : ScoreVector Alternative) : Prop :=
  isReferenceNormalized reference score ∧
    IsMaxOn (pairwiseLogLikelihood dataset link)
      {candidate : ScoreVector Alternative | isReferenceNormalized reference candidate}
      score

/-- Uniqueness of a fixed-reference finite pairwise MLE. -/
def hasUniquePairwiseMLE
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (link : ℝ → ℝ)
    (reference : Alternative) : Prop :=
  ∃ score : ScoreVector Alternative,
    isPairwiseMLE dataset link reference score ∧
      ∀ other, isPairwiseMLE dataset link reference other → other = score

/--
A source-style labelling `x₁,…,xₘ` of the finite alternatives for which every
higher-labelled alternative loses its direct majority comparison to every
lower-labelled one. The equivalence to `Fin card` records that the labels are
an enumeration, not merely an arbitrary rank function.
-/
def hasPairwiseMajorityRanking
    {Alternative : Type*} [Fintype Alternative]
    (dataset : PairwiseCountDataset Alternative)
    (ranking : Alternative ≃ Fin (Fintype.card Alternative)) : Prop :=
  ∀ first second, ranking first < ranking second →
    dataset.count second first < dataset.count first second

/-- A score vector realizes a source majority ranking with weak score order. -/
def scoreRespectsPairwiseMajorityRanking
    {Alternative : Type*} [Fintype Alternative]
    (score : ScoreVector Alternative)
    (ranking : Alternative ≃ Fin (Fintype.card Alternative)) : Prop :=
  ∀ first second, ranking first < ranking second → score second ≤ score first

/--
The global property in Definition 5.1: every finite fixed-reference MLE
weakly respects every strict source majority ranking of its dataset.
-/
def pairwiseMLEPairwiseMajorityConsistent (link : ℝ → ℝ) : Prop :=
  ∀ {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (reference : Alternative)
    (score : ScoreVector Alternative)
    (ranking : Alternative ≃ Fin (Fintype.card Alternative)),
    isPairwiseMLE dataset link reference score →
    dataset.hasPairwiseMajorityRanking ranking →
    scoreRespectsPairwiseMajorityRanking score ranking

/--
The global property in Definition 6.1: if two component-data MLEs both rank a
pair strictly in one direction, every MLE of their pointwise pooled counts has
the same strict ordering.
-/
def pairwiseMLESeparable (link : ℝ → ℝ) : Prop :=
  ∀ {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (firstDataset secondDataset : PairwiseCountDataset Alternative)
    (firstReference : Alternative) (firstScore : ScoreVector Alternative)
    (secondReference : Alternative) (secondScore : ScoreVector Alternative)
    (first second : Alternative),
    isPairwiseMLE firstDataset link firstReference firstScore →
    isPairwiseMLE secondDataset link secondReference secondScore →
    firstScore second < firstScore first →
    secondScore second < secondScore first →
    ∀ pooledReference pooledScore,
      isPairwiseMLE (firstDataset.add secondDataset) link pooledReference pooledScore →
        pooledScore second < pooledScore first

/--
The strong monotonicity property in Definition 4.1: when exactly the directed
count `winner ≻ loser` increases, the two unique fixed-reference MLEs move
`winner` weakly upward and `loser` weakly downward relative to every alternative.
-/
def pairwiseMLEMonotonicity
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (link : ℝ → ℝ) : Prop :=
  ∀ (baseline updated : PairwiseCountDataset Alternative)
    (reference winner loser : Alternative),
    hasSinglePairCountIncrease baseline updated winner loser →
    hasUniquePairwiseMLE baseline link reference →
    hasUniquePairwiseMLE updated link reference →
    ∀ baselineScore updatedScore,
      isPairwiseMLE baseline link reference baselineScore →
      isPairwiseMLE updated link reference updatedScore →
      ∀ other,
        baselineScore winner - baselineScore other ≤ updatedScore winner - updatedScore other ∧
          updatedScore loser - updatedScore other ≤ baselineScore loser - baselineScore other

/--
The count-side premise of Definition 3.1 in Noothigattu--Peters--Procaccia
(2020): `first` has a larger direct count against `second` and strictly better
outgoing/incoming counts against every other alternative.
-/
def hasParetoCountDominance {Alternative : Type*}
    (dataset : PairwiseCountDataset Alternative) (first second : Alternative) : Prop :=
  dataset.count second first < dataset.count first second ∧
    ∀ other, other ≠ first → other ≠ second →
      dataset.count second other < dataset.count first other ∧
        dataset.count other first < dataset.count other second

/-- The strict direct comparison in a Pareto-count premise forces distinct alternatives. -/
theorem hasParetoCountDominance_ne
    {Alternative : Type*} (dataset : PairwiseCountDataset Alternative)
    {first second : Alternative} (hpareto : dataset.hasParetoCountDominance first second) :
    first ≠ second := by
  intro hsame
  subst second
  exact Nat.lt_irrefl _ hpareto.1

/--
A fixed-reference MLE is maximal against every score vector, not only
reference-normalized candidates: shift the candidate by the negative of its
reference coordinate and use score-shift invariance.
-/
theorem isPairwiseMLE_global_max
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (link : ℝ → ℝ)
    (reference : Alternative) (score : ScoreVector Alternative)
    (hmle : isPairwiseMLE dataset link reference score)
    (candidate : ScoreVector Alternative) :
    pairwiseLogLikelihood dataset link candidate ≤
      pairwiseLogLikelihood dataset link score := by
  let normalizedCandidate : ScoreVector Alternative :=
    fun alternative => candidate alternative + -candidate reference
  have hnormalized : isReferenceNormalized reference normalizedCandidate := by
    dsimp [isReferenceNormalized, normalizedCandidate]
    ring
  have hmax := hmle.2 hnormalized
  rw [← pairwiseLogLikelihood_shift dataset link candidate (-candidate reference)]
  exact hmax

/--
At a unique fixed-reference MLE, every distinct score vector satisfying the
same normalization has strictly smaller finite likelihood. This is the strict
maximality step used when the Supplement-D proof replaces one nonempty block
of score coordinates by a different block.
-/
theorem isPairwiseMLE_strict_global_max_of_unique
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (link : ℝ → ℝ)
    (reference : Alternative) (score : ScoreVector Alternative)
    (hmle : isPairwiseMLE dataset link reference score)
    (hunique : ∀ other, isPairwiseMLE dataset link reference other → other = score)
    (candidate : ScoreVector Alternative)
    (hcandidate : isReferenceNormalized reference candidate)
    (hne : candidate ≠ score) :
    pairwiseLogLikelihood dataset link candidate <
      pairwiseLogLikelihood dataset link score := by
  have hle := isPairwiseMLE_global_max dataset link reference score hmle candidate
  refine lt_of_le_of_ne hle ?_
  intro heq
  have hcandidateMax : IsMaxOn (pairwiseLogLikelihood dataset link)
      {other : ScoreVector Alternative | isReferenceNormalized reference other} candidate := by
    intro other hother
    rw [heq]
    exact hmle.2 hother
  have hcandidateMLE : isPairwiseMLE dataset link reference candidate :=
    ⟨hcandidate, hcandidateMax⟩
  exact hne (hunique candidate hcandidateMLE)

/--
At a unique fixed-reference MLE, a candidate with a different score
difference on any pair has strictly smaller likelihood. Unlike the preceding
normalized form, this statement is invariant under a common score shift and
therefore applies directly to source-style score vectors normalized at another
alternative.
-/
theorem isPairwiseMLE_strict_global_max_of_unique_of_score_sub_ne
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (link : ℝ → ℝ)
    (reference : Alternative) (score : ScoreVector Alternative)
    (hmle : isPairwiseMLE dataset link reference score)
    (hunique : ∀ other, isPairwiseMLE dataset link reference other → other = score)
    (candidate : ScoreVector Alternative) (first second : Alternative)
    (hdifference : candidate first - candidate second ≠ score first - score second) :
    pairwiseLogLikelihood dataset link candidate <
      pairwiseLogLikelihood dataset link score := by
  let normalizedCandidate : ScoreVector Alternative :=
    fun alternative => candidate alternative + -candidate reference
  have hnormalized : isReferenceNormalized reference normalizedCandidate := by
    dsimp [isReferenceNormalized, normalizedCandidate]
    ring
  have hne : normalizedCandidate ≠ score := by
    intro heq
    apply hdifference
    have hfirst := congrFun heq first
    have hsecond := congrFun heq second
    dsimp [normalizedCandidate] at hfirst hsecond
    linarith
  have hstrict := isPairwiseMLE_strict_global_max_of_unique dataset link reference score
    hmle hunique normalizedCandidate hnormalized hne
  dsimp [normalizedCandidate] at hstrict
  rw [pairwiseLogLikelihood_shift dataset link candidate (-candidate reference)] at hstrict
  exact hstrict

end PairwiseCountDataset
end HumanFeedback
end Learning
end AppliedModelingLib
