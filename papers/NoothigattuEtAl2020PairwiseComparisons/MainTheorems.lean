import AppliedModelingLib.Foundations.Optimization.CoinFlipLikelihood
import AppliedModelingLib.Learning.HumanFeedback.PairwiseCount
import AppliedModelingLib.Learning.HumanFeedback.PairwiseCountMLE
import AppliedModelingLib.Learning.HumanFeedback.PairwiseCountExistence
import NoothigattuEtAl2020PairwiseComparisons.Counterexamples

/-!
# Paper-Facing Theorems: Axioms for Learning from Pairwise Comparisons

This file is the implementation theorem layer for the source paper. Keep
source-faithful definitions and theorem wrappers here, and expose only the
compact human-review subset in `PaperInterface.lean`.

During the statement-first phase, each exact paper-facing proposition lives in a
transparent `<name>Spec : Prop` declaration in `PaperInterface.lean`; the paired
theorem/lemma endpoint belongs in `ProofInterface.lean` and has exactly that
type. Add proof implementations here only after those specifications pass v11
raw-source-to-expanded-Spec review and recursive premise provenance audit. Before full closeout, the v11
realization audit independently binds pinned source atoms to the elaborated Spec
and accounts for the complete Lean closure; a proof hole or a declaration name
is never evidence for that correspondence.
-/

namespace NoothigattuEtAl2020PairwiseComparisons

open AppliedModelingLib
open AppliedModelingLib.Learning.HumanFeedback
open AppliedModelingLib.Learning.HumanFeedback.PairwiseCountDataset

/--
Source: Claim A.1 in the official supplementary PDF, p. 13.

The source's `h` and `t` are positive real heads and tails weights.  The
statement retains both the strict-concavity conclusion and the exact unique
maximum location on the open probability interval.
-/
theorem claimA1_coin_flip_likelihood :
    ∀ {heads tails : ℝ}, 0 < heads → 0 < tails →
      StrictConcaveOn ℝ (Set.Ioo (0 : ℝ) 1)
          (coinFlipLogLikelihood heads tails) ∧
        (heads / (heads + tails) ∈ Set.Ioo (0 : ℝ) 1 ∧
          IsMaxOn (coinFlipLogLikelihood heads tails) (Set.Ioo (0 : ℝ) 1)
            (heads / (heads + tails)) ) ∧
          ∀ maximizer,
            maximizer ∈ Set.Ioo (0 : ℝ) 1 →
              IsMaxOn (coinFlipLogLikelihood heads tails) (Set.Ioo (0 : ℝ) 1) maximizer →
                maximizer = heads / (heads + tails) := by
  intro heads tails hheads htails
  have htotal : 0 < heads + tails := add_pos hheads htails
  have hmaxPos : 0 < heads / (heads + tails) := div_pos hheads htotal
  have hmaxLt : heads / (heads + tails) < 1 :=
    (div_lt_one htotal).mpr (lt_add_of_pos_right heads htails)
  have hmaxMem : heads / (heads + tails) ∈ Set.Ioo (0 : ℝ) 1 := ⟨hmaxPos, hmaxLt⟩
  have hmax := coinFlipLogLikelihood_isMaxOn hheads htails
  refine ⟨coinFlipLogLikelihood_strictConcave hheads htails, ⟨hmaxMem, hmax⟩, ?_⟩
  intro maximizer hmem hmaximizer
  exact (coinFlipLogLikelihood_strictConcave hheads htails).eq_of_isMaxOn
    hmaximizer hmax hmem hmaxMem

/--
Source: Claim C.1 in the official supplementary PDF, p. 17.

The source uses this strict crossed-product inequality inside the exchange
argument for Theorem 3.2.  Its positive-factor hypotheses are retained even
though the algebraic conclusion only needs the two displayed strict gaps.
-/
theorem claimC1_strict_crossed_product
    {c d e f : ℝ}
    (hc : 0 < c) (hd : 0 < d) (he : 0 < e) (hf : 0 < f)
    (hdc : d < c) (hfe : f < e) :
    c * e + d * f > c * f + d * e := by
  have hleftGap : 0 < c - d := sub_pos.mpr hdc
  have hrightGap : 0 < e - f := sub_pos.mpr hfe
  have hproduct : 0 < (c - d) * (e - f) :=
    mul_pos hleftGap hrightGap
  nlinarith

/--
Source: Lemma 2.1 (main p. 4; official Supplement A.1).

The finite fixed-reference MLE exists if and only if every undirected
comparison component has directed paths in both directions between all of its
vertices. The compactness proof normalizes every component at its minimum; the
formal route uses a convenient tail-derived compactness bound rather than
tracking the appendix's more explicit numerical constant.
-/
theorem lemma2_1_mle_exists
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (link : CDFLikePairwiseLink)
    (reference : Alternative) (hcontinuous : Continuous (link : ℝ → ℝ))
    (hstrict : StrictMono (link : ℝ → ℝ)) :
    (∃ score : ScoreVector Alternative, isPairwiseMLE dataset link reference score) ↔
      dataset.everyComponentStronglyConnected :=
  pairwiseMLE_exists_iff_everyComponentStronglyConnected dataset link reference hcontinuous hstrict

/--
Source: Lemma 2.2 (main paper p. 4; official supplement A.2).

The source's `F⁻¹` perfect-fit distance is represented by its unique
inverse-image characterization on the open unit interval. This preserves the
paper's exact distance conclusion without assigning an arbitrary value to an
inverse outside that domain.
-/
theorem lemma2_2_one_neighbor_perfect_fit
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (link : CDFLikePairwiseLink)
    (reference : Alternative) (score : ScoreVector Alternative)
    {first second : Alternative}
    (hmle : isPairwiseMLE dataset link reference score)
    (honly : dataset.hasOnlyNeighbor first second)
    (hforward : 0 < dataset.count first second)
    (hreverse : 0 < dataset.count second first)
    (hcontinuous : Continuous (link : ℝ → ℝ))
    (hstrict : StrictMono (link : ℝ → ℝ)) :
    ∃! delta : ℝ,
      link delta = (dataset.count first second : ℝ) /
        ((dataset.count first second : ℝ) + (dataset.count second first : ℝ)) ∧
      score first - score second = delta :=
  isPairwiseMLE_existsUnique_perfectFit_distance dataset link reference score hmle honly
    hforward hreverse hcontinuous hstrict

/--
Source: Lemma 2.3 (main paper p. 4; official Supplement A.3).

Under positive directed counts for every distinct alternative pair, the
reference-normalized MLE is bounded in finite `ℓ∞` norm by the source's
`|X| · max δ(x,y)` expression.  The shared proof follows the appendix's
ordered-score cut argument, including the reflected negative-coordinate case.
-/
theorem lemma2_3_mle_supNorm_bound
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (link : CDFLikePairwiseLink)
    (reference : Alternative) (score : ScoreVector Alternative)
    (hmle : isPairwiseMLE dataset link reference score)
    (hcomplete : ∀ first second, first ≠ second → 0 < dataset.count first second)
    (hcontinuous : Continuous (link : ℝ → ℝ))
    (hstrict : StrictMono (link : ℝ → ℝ)) :
    scoreSupNorm reference score ≤ (Fintype.card Alternative : ℝ) *
      dataset.maxPerfectFitDistance link hcontinuous reference :=
  scoreSupNorm_le_card_mul_maxPerfectFitDistance_of_pairwiseMLE dataset link hcontinuous hstrict
    reference score hmle hcomplete

/--
Source: Lemma 2.4 (main paper p. 4; official Supplement B).

Strict log-concavity of `log ∘ F` makes the finite likelihood strictly concave
on the fixed-reference domain exactly for connected comparison graphs. In that
case strict concavity gives uniqueness of every existing fixed-reference MLE;
a disconnected component can instead be translated without changing any
likelihood term.
-/
theorem lemma2_4_strictConcavity_and_unique_mle
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (link : ℝ → ℝ)
    (reference : Alternative)
    (hlogStrict : StrictConcaveOn ℝ Set.univ (fun gap => Real.log (link gap))) :
    (StrictConcaveOn ℝ
        {score : ScoreVector Alternative | isReferenceNormalized reference score}
        (pairwiseLogLikelihood dataset link) ∧
      ∀ score, isPairwiseMLE dataset link reference score →
        ∀ other, isPairwiseMLE dataset link reference other → other = score) ↔
      dataset.isConnected := by
  constructor
  · intro h
    exact (pairwiseLogLikelihood_strictConcaveOn_iff_isConnected dataset link hlogStrict reference).mp h.1
  · intro hconnected
    refine ⟨pairwiseLogLikelihood_strictConcaveOn_of_isConnected dataset link hlogStrict reference
      hconnected, ?_⟩
    intro score hmle other hother
    exact isPairwiseMLE_unique_of_isConnected dataset link hlogStrict reference hconnected
      score hmle other hother

/--
Finite realization of source Theorem 3.2: strict monotonicity makes every
fixed-reference MLE satisfy the Definition-3.1 Pareto score ordering.
-/
theorem theorem3_2_mle_satisfies_pareto_efficiency
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (link : CDFLikePairwiseLink)
    (reference : Alternative) (score : ScoreVector Alternative)
    {first second : Alternative}
    (hstrict : StrictMono (link : ℝ → ℝ))
    (hmle : isPairwiseMLE dataset link reference score)
    (hpareto : dataset.hasParetoCountDominance first second) :
    score second ≤ score first :=
  isPairwiseMLE_pareto_score_order dataset link reference score hmle hpareto hstrict

/--
Finite realization of source Theorem 4.2: strict monotonicity and
log-concavity of the source random-utility CDF imply Definition 4.1
monotonicity for all finite datasets with unique fixed-reference MLEs.
-/
theorem theorem4_2_mle_satisfies_monotonicity
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (link : CDFLikePairwiseLink)
    (hstrict : StrictMono (link : ℝ → ℝ))
    (hlogConcave : ConcaveOn ℝ Set.univ (fun gap => Real.log (link gap))) :
    pairwiseMLEMonotonicity (Alternative := Alternative) link :=
  pairwiseMLEMonotonicity_of_strictMono_logConcave link hstrict hlogConcave

/--
Source Theorem 5.3: every strictly monotone, strictly log-concave,
differentiable random-utility link has a finite pairwise-count instance that
violates pairwise majority consistency.  Differentiability supplies the
continuity used in the source proof; the implementation realizes its small
rational perturbation with exact integer counts.
-/
theorem theorem5_3_mle_violates_pairwise_majority_consistency
    (link : CDFLikePairwiseLink) (hstrict : StrictMono (link : ℝ → ℝ))
    (hlogStrict : StrictConcaveOn ℝ Set.univ (fun gap => Real.log (link gap)))
    (hdifferentiable : Differentiable ℝ (link : ℝ → ℝ)) :
    ¬ pairwiseMLEPairwiseMajorityConsistent.{0} link :=
  theorem5_3_mle_violates_pairwise_majority_consistency_core
    link hstrict hlogStrict hdifferentiable

/--
Source Theorem 6.3: every strictly monotone, strictly log-concave,
differentiable random-utility link has finite component datasets whose MLEs
are not separable after pooling. The proof realizes the source's positive
rational perturbation with exact integer counts.
-/
theorem theorem6_3_mle_violates_separability
    (link : CDFLikePairwiseLink) (hstrict : StrictMono (link : ℝ → ℝ))
    (hlogStrict : StrictConcaveOn ℝ Set.univ (fun gap => Real.log (link gap)))
    (hdifferentiable : Differentiable ℝ (link : ℝ → ℝ)) :
    ¬ pairwiseMLESeparable.{0} link :=
  theorem6_3_mle_violates_separability_core link hstrict hlogStrict hdifferentiable

end NoothigattuEtAl2020PairwiseComparisons
