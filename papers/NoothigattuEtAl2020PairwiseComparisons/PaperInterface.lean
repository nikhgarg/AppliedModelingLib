import NoothigattuEtAl2020PairwiseComparisons.MainTheorems
import NoothigattuEtAl2020PairwiseComparisons.Assumptions

/-!
# Human-Facing Paper Interface: Axioms for Learning from Pairwise Comparisons

This is the compact Lean file a human should read after formalization to check
whether the paper's definitions and named theorem statements were represented
correctly. Keep the row-level dashboard and LLM audit statements in this file
for every paper. Move implementation details, proof aliases, and bulky helper
lemmas behind imported modules such as `AuditInterface.lean`, but expose the
audited paper-facing statements directly here; do not use
`paper_interface.audit_surface_path`.

Rules for completing this file:

- Keep the paper's definitions/formatted objects first, in source order.
- Expose the actual paper formulas here; do not only point to generic library
  definitions or implementation witnesses.
- A material reusable `AppliedModelingLib` primitive may remain a reference here only
  after `audit/library_semantic_review.json` records its exact bounded library
  declaration and an explicit byte-pinned paper-source connection. The
  dashboard and human-review packet show and source-check that declaration
  before the dependent Spec; a library name, docstring, or glossary is not a
  semantic bridge. Do not add a duplicate paper claim merely to restate it.
- If a named theorem needs a hypothesis that is not derived from earlier Lean
  declarations, declare that hypothesis in `Assumptions.lean` and list it in
  `status.json` `review_surface.assumption_names`.
- Then state the named results directly, with assumptions visible in each
  theorem signature by referencing named paper assumptions imported from
  `Assumptions.lean`.
- In the statement-first phase, write every complete source-facing statement as
  a transparent `<name>Spec : Prop` here, exactly once. Put the paired
  theorem/lemma of that exact type in `ProofInterface.lean`; an unfinished
  private-draft proof must be replaced before review. This separation keeps
  the human semantic surface free of thin wrapper declarations.
- Before drafting that Lean surface, independently inventory every material
  source atom from exact pinned source quote bytes. Do not infer source atoms
  from declaration, binder, field, function, or source-map names.
- Run raw-source-to-expanded-Spec statement matching plus recursive
  premise/conclusion provenance on the skeleton. The semantic comparison uses
  only byte-pinned source quotes (and separately pinned source context) against
  the expanded transparent Spec; map summaries and proof wrappers are not
  semantic inputs. Then freeze each canonical Lean declaration-manifest digest.
- In the proof phase, replace an unfinished `ProofInterface.lean` proof with a short
  proof that calls into `MainTheorems.lean` or lower proof files without
  changing the specification or theorem type. Any specification/type change
  invalidates the freeze and requires a fresh statement audit.
- At formalized closeout, complete the v11 realization receipt: Lean Meta checks
  the theorem has exactly the transparent Spec type; each source atom is bound
  to the elaborated Spec surface; closure traversal includes proof and instance
  arguments; and every material terminal has a source, approved correction or
  additional assumption, checked derivation, or version-pinned foundation
  disposition. No data, container, or identifier-based exemption is allowed.
- The transparent `...Spec` is the sole semantic-review target for its source
  claim. The paired theorem/lemma is a proof endpoint whose exact Spec type is
  verified by Lean Meta, not a duplicate source-to-Lean comparison row.
- Keep proof endpoints, exhaustive endpoint aliases, and proof-seam checks in
  `ProofInterface.lean`, implementation modules, or `ProofLedger.lean`, not
  here. Do not create new `PostPaperAudit.lean` or `AuditLedger.lean` files;
  those names are legacy.

## Named Results

Each entry has one semantic-review target (`Spec`) and one proof endpoint (the
paired theorem/lemma). The human dashboard and review packet present that pair
once rather than treating the two declarations as duplicate paper claims.

- Claim A.1, coin-flip likelihood (Supplement p. 13).
- Claim C.1, strict crossed-product inequality (Supplement p. 17).
- Lemma 2.1, MLE existence iff componentwise strong connectivity (main p. 4;
  Supplement A.1).
- Lemma 2.2, perfect fit for an alternative with one comparison-graph neighbor
  (main p. 4; Supplement A.2).
- Lemma 2.3, the finite sup-norm bound for an MLE with complete positive
  directed counts (main p. 4; Supplement A.3).
- Lemma 2.4, graph connectivity, strict concavity, and MLE uniqueness (main
  p. 4; Supplement B).
- Definition 3.1, Pareto efficiency (main paper p. 5).
- Theorem 3.2, MLE satisfies Pareto efficiency under strict monotonicity (main
  paper p. 5; Supplement C).
- Definition 4.1, monotonicity (main paper p. 5).
- Theorem 4.2, MLE satisfies monotonicity under strict monotonicity and
  log-concavity (main paper p. 5; Supplement D).
- Definition 5.1, pairwise majority consistency (main paper p. 6).
- Theorem 5.3, MLE violates pairwise majority consistency under strict
  monotonicity, strict log-concavity, and differentiability (main paper p. 7;
  Supplement E).
- Definition 6.1, separability (main paper p. 7).
- Theorem 6.3, MLE violates separability under strict monotonicity, strict
  log-concavity, and differentiability (main paper p. 8; Supplement F).
-/

namespace NoothigattuEtAl2020PairwiseComparisons

open AppliedModelingLib
open AppliedModelingLib.Learning.HumanFeedback
open AppliedModelingLib.Learning.HumanFeedback.PairwiseCountDataset

/--
Source-facing statement of Claim A.1 (official supplementary PDF, p. 13).
For positive `h,t`, the source defines `f(p) = h log(p) + t log(1-p)` on
`p ∈ (0,1)`, says it is strictly concave, and says its maximum is uniquely
attained at `h/(h+t)`.
-/
def claimA1_coin_flip_likelihoodSpec : Prop :=
  ∀ {heads tails : ℝ}, 0 < heads → 0 < tails →
    StrictConcaveOn ℝ (Set.Ioo (0 : ℝ) 1)
        (coinFlipLogLikelihood heads tails) ∧
      (heads / (heads + tails) ∈ Set.Ioo (0 : ℝ) 1 ∧
        IsMaxOn (coinFlipLogLikelihood heads tails) (Set.Ioo (0 : ℝ) 1)
          (heads / (heads + tails)) ) ∧
        ∀ maximizer,
          maximizer ∈ Set.Ioo (0 : ℝ) 1 →
            IsMaxOn (coinFlipLogLikelihood heads tails) (Set.Ioo (0 : ℝ) 1) maximizer →
              maximizer = heads / (heads + tails)

/--
Source-facing statement of Claim C.1 (official supplementary PDF, p. 17).
The source quantifies real `c,d,e,f > 0`, assumes `c > d` and `e > f`, and
concludes `ce + df > cf + de`.
-/
def claimC1_strict_crossed_productSpec : Prop :=
  ∀ {c d e f : ℝ},
    0 < c → 0 < d → 0 < e → 0 < f →
      d < c → f < e →
        c * e + d * f > c * f + d * e

/--
Source-facing statement of Lemma 2.1 (main paper p. 4; Supplement A.1).
With the source's fixed-reference score normalization made explicit, a finite
MLE exists exactly when each undirected comparison component is directed
strongly connected. The source's unnormalised statement is equivalent because
common shifts on connected components leave the likelihood unchanged.
-/
def lemma2_1_mle_existsSpec : Prop :=
  ∀ {Alternative : Type*} [Fintype Alternative]
    (dataset : PairwiseCountDataset Alternative) (link : CDFLikePairwiseLink)
    (reference : Alternative),
    let _ : DecidableEq Alternative := Classical.decEq Alternative
    Continuous (link : ℝ → ℝ) →
      StrictMono (link : ℝ → ℝ) →
        ((∃ score : ScoreVector Alternative, isPairwiseMLE dataset link reference score) ↔
          dataset.everyComponentStronglyConnected)

/--
Source-facing intrinsic formulation of Lemma 2.2 (main paper p. 4;
Supplement A.2). The source writes the conclusion as `β̂_a - β̂_b =
F⁻¹(#(a ≻ b)/(#(a ≻ b)+#(b ≻ a)))`. Here the unique inverse image is exposed
directly, retaining the exact strict-monotonicity, continuity, one-neighbor,
and two-positive-count premises while avoiding a noncanonical total inverse
outside `(0,1)`.
-/
def lemma2_2_one_neighbor_perfect_fitSpec : Prop :=
  ∀ {Alternative : Type*} [Fintype Alternative]
    (dataset : PairwiseCountDataset Alternative) (link : CDFLikePairwiseLink)
    (reference : Alternative) (score : ScoreVector Alternative)
    {first second : Alternative},
    let _ : DecidableEq Alternative := Classical.decEq Alternative
    isPairwiseMLE dataset link reference score →
    dataset.hasOnlyNeighbor first second →
    0 < dataset.count first second →
    0 < dataset.count second first →
    Continuous (link : ℝ → ℝ) →
    StrictMono (link : ℝ → ℝ) →
    ∃! delta : ℝ,
      link delta = (dataset.count first second : ℝ) /
        ((dataset.count first second : ℝ) + (dataset.count second first : ℝ)) ∧
      score first - score second = delta

/--
Source-facing Lemma 2.3 (main paper p. 4; Supplement A.3).  The displayed
source premise means positive counts in both directions for every *distinct*
alternative pair: diagonal counts are structurally zero in the pairwise-count
model, so interpreting the quantifier literally on diagonal pairs would make
the premise inconsistent.  The source's OCR transcript renders the `∞` in
the norm as `1`; the official PDF glyph is `ℓ∞`.
-/
def lemma2_3_mle_supNorm_boundSpec : Prop :=
  ∀ {Alternative : Type*} [Fintype Alternative],
    let _ : DecidableEq Alternative := Classical.decEq Alternative
    ∀ (dataset : PairwiseCountDataset Alternative) (link : CDFLikePairwiseLink)
      (reference : Alternative) (score : ScoreVector Alternative)
      (hmle : isPairwiseMLE dataset link reference score)
      (hcomplete : ∀ first second, first ≠ second → 0 < dataset.count first second)
      (hcontinuous : Continuous (link : ℝ → ℝ))
      (hstrict : StrictMono (link : ℝ → ℝ)),
      scoreSupNorm reference score ≤ (Fintype.card Alternative : ℝ) *
        dataset.maxPerfectFitDistance link hcontinuous reference

/--
Source-facing Lemma 2.4 (main paper p. 4; Supplement B). Under strict
log-concavity of the source CDF, the finite likelihood is strictly concave on
the fixed-reference score domain and every MLE in that domain is unique
(whenever one exists) exactly when the undirected comparison graph is
connected.
-/
def lemma2_4_strictConcavity_and_unique_mleSpec : Prop :=
  ∀ {Alternative : Type*} [Fintype Alternative]
    (dataset : PairwiseCountDataset Alternative) (link : CDFLikePairwiseLink)
    (reference : Alternative)
    (hlogStrict : StrictConcaveOn ℝ Set.univ (fun gap => Real.log (link gap))),
    let _ : DecidableEq Alternative := Classical.decEq Alternative
    (StrictConcaveOn ℝ
        {score : ScoreVector Alternative | isReferenceNormalized reference score}
        (pairwiseLogLikelihood dataset link) ∧
      ∀ score, isPairwiseMLE dataset link reference score →
        ∀ other, isPairwiseMLE dataset link reference other → other = score) ↔
      dataset.isConnected

/--
Source-facing Definition 3.1 (main paper p. 5). For every MLE, the strict
count comparisons stated by the source require the learned score of `first` to
be at least the learned score of `second`.
-/
def definition3_1_pareto_efficiency (link : CDFLikePairwiseLink) : Prop :=
  ∀ {Alternative : Type} [Fintype Alternative]
    (dataset : PairwiseCountDataset Alternative) (reference : Alternative)
    (score : ScoreVector Alternative)
    {first second : Alternative},
    let _ : DecidableEq Alternative := Classical.decEq Alternative
    isPairwiseMLE dataset link reference score →
    dataset.hasParetoCountDominance first second →
    score second ≤ score first

/--
Source-facing Theorem 3.2 (main paper p. 5; Supplement C): under strict
monotonicity of the random-utility CDF, every finite fixed-reference MLE obeys
the Definition-3.1 Pareto count condition.
-/
def theorem3_2_mle_satisfies_pareto_efficiencySpec : Prop :=
  ∀ (link : CDFLikePairwiseLink),
    StrictMono (link : ℝ → ℝ) →
    definition3_1_pareto_efficiency link

/--
Source-facing Definition 4.1 (main paper p. 5). When exactly the directed
count `winner ≻ loser` increases, each of the two datasets has a unique
fixed-reference MLE, and `baselineScore` and `updatedScore` are those MLEs,
the winner's learned score weakly increases and the loser's weakly decreases
relative to every alternative.
-/
def definition4_1_monotonicitySpec (link : CDFLikePairwiseLink) : Prop :=
  ∀ {Alternative : Type} [Fintype Alternative],
    let _ : DecidableEq Alternative := Classical.decEq Alternative
    pairwiseMLEMonotonicity (Alternative := Alternative) link

/--
Source-facing Theorem 4.2 (main paper p. 5; Supplement D): if the source CDF
is strictly monotonic and log-concave, maximum likelihood estimation satisfies
Definition 4.1 monotonicity. The finite CDF-like structure supplies the source
model conditions stated after Eq. (1); uniqueness remains exactly in the
Definition-4.1 property rather than being added as a theorem premise.
-/
def theorem4_2_mle_satisfies_monotonicitySpec : Prop :=
  ∀ (link : CDFLikePairwiseLink),
    StrictMono (link : ℝ → ℝ) →
    ConcaveOn ℝ Set.univ (fun gap => Real.log (link gap)) →
    Differentiable ℝ (link : ℝ → ℝ) →
    definition4_1_monotonicitySpec link

/--
Source-facing Definition 5.1 (main paper p. 7). A source labelling of all
alternatives gives a strict pairwise-count majority to every lower index over
every higher index; every MLE must then rank each lower-index alternative
at least as high as each higher-index alternative.
-/
def definition5_1_pairwise_majority_consistencySpec (link : CDFLikePairwiseLink) : Prop :=
  pairwiseMLEPairwiseMajorityConsistent.{0} link

/--
Source-facing Theorem 5.3 (main paper p. 7; Supplement E). Under exactly the
source's strict monotonicity, strict log-concavity, and differentiability
assumptions on its CDF-like link, the finite MLE rule fails Definition 5.1.
The finite link structure retains Eq. (1)'s CDF-like model conditions.
-/
def theorem5_3_mle_violates_pairwise_majority_consistencySpec : Prop :=
  ∀ (link : CDFLikePairwiseLink),
    StrictMono (link : ℝ → ℝ) →
    StrictConcaveOn ℝ Set.univ (fun gap => Real.log (link gap)) →
    Differentiable ℝ (link : ℝ → ℝ) →
    ¬ definition5_1_pairwise_majority_consistencySpec link

/--
Source-facing Definition 6.1 (main paper p. 7). When two datasets each have
an MLE that ranks `first` strictly above `second`, every MLE of their pointwise
pooled count dataset must preserve that strict ordering.
-/
def definition6_1_separabilitySpec (link : CDFLikePairwiseLink) : Prop :=
  pairwiseMLESeparable.{0} link

/--
Source-facing Theorem 6.3 (main paper p. 8; Supplement F). Under exactly the
source's strict monotonicity, strict log-concavity, and differentiability
assumptions on its CDF-like link, the finite MLE rule fails Definition 6.1.
-/
def theorem6_3_mle_violates_separabilitySpec : Prop :=
  ∀ (link : CDFLikePairwiseLink),
    StrictMono (link : ℝ → ℝ) →
    StrictConcaveOn ℝ Set.univ (fun gap => Real.log (link gap)) →
    Differentiable ℝ (link : ℝ → ℝ) →
    ¬ definition6_1_separabilitySpec link

end NoothigattuEtAl2020PairwiseComparisons
