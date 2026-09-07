# Formalization Notes

This file preserves the previous hand-written paper-folder README content.
The paper-folder `README.md` is now a generated status overview.

# Falahatgar et al. (2017): Maxing and Ranking with Few Assumptions

This package formalizes Falahatgar et al.'s finite preference-relation,
maxing, ranking-lower-bound, and Borda bridges. Xu et al.'s OPT-Maximize use
is one downstream consumer, not this package's scope boundary.

The source's published supplement is essential: it contains Appendix A.3 and
A.7, whose proof structure supplies the machine-checked deterministic
invariants. The source's finite Bernoulli model now instantiates the
statistical guarantee of `Compare`, the fresh adaptive Seq-Eliminate calls,
Pick-Anchor's Lemma 3 probability conclusion and all-parameter
ceiling-aware resource bound, and the finite one-round Prune survivor-count bridge. Lemma 13's multi-round protected-arm probability is
also closed under a finite scheduled Bernoulli product coupling. OPT-Maximize's
first-round Prune size guarantee (Lemma 14) is also closed with its printed
`8 log² n` condition. Lemma 15's deterministic shrinkage, source tail
arithmetic, and concrete finite fresh stopped-round sampler are checked. For
the nontrivial `n ≥ 3` branch, its printed `1 - δ / 2` size conclusion and
exact stopped comparison envelope are proved jointly at Algorithm 2's
one-indexed squared-log guard, represented by `floor(log_2 n)^2 - 1` checked
rounds in the paper's `δ ≤ 1 / 2` regime, including the deterministic
at-most-two-arm boundary. The same literal PMF now carries the sharp geometric
source-rate comparison envelope. Its rounded-cutoff instance
has both a fixed-positive-normalized-confidence linear rate and a uniform
parameter-sequence `O(n (1 + log (1 / delta)) / (upper - lower)²)` rate over
the source-normalized confidence and gap regime.
Main Lemma 5 is proved separately under its exact weaker archival premises:
`sqrt(6 n log n) <= n'` and `1/n <= delta`. When `n'/n > 1/2`, Prune is
already stopped; otherwise the proof monitors contraction with
`max delta (n'/n)` while retaining `delta` in every actual comparison batch.
The proof endpoint constructs the finite batch cap internally, runs on the
paper carrier `S`, and projects that monitor flag away. The interface states
only the canonical output-size event, the population-only ceiling-aware bound
`16 n (2/(upper-lower)^2 + 1) (1 + log(1/delta))` on actual stopped-execution
comparisons, and conditional maximum retention. It exposes neither
proof-storage witnesses nor an external probability space, and it does not
inherit Supplement Lemma 15's stronger `n'/n <= delta` premise.
For Theorem 6, the total OPT-Maximize branch has a single finite
`1 - delta` event combining an epsilon-maximum output with a deterministic
population-only comparison envelope. It uses the explicit upward-rounded,
capped source cutoff, an exact finite batch maximum, and Algorithm 3's literal
`delta / 4` phase allocation. The proof separates the already-stopped small
population case from the large case, where the printed `delta > 1/n` guard
absorbs the inverse-square contraction tail. Its exact population envelope has
a checked fixed-`(epsilon, delta)` linear limit and `O(n)` rate, with every
ceiling and source-cutoff term retained until that calculation. Its public
rate-shape theorem is `O(n (1 + log (1 / delta)) / epsilon²)` at the printed
accuracy thresholds. The printed unshifted uniform `log (1 / delta)` display
is not substituted at the `delta = 1` endpoint. Supplement Lemma 17 is proved
by the same small/large split under its printed `delta >= 1/n` premise, without
an added confidence-versus-cutoff condition.

The Section-5 Borda sampler is now a concrete finite uniform-opponent/Bernoulli
product law, and its empirical-ranking concentration theorem and exact total
ceiling-corrected budget are proved. At fixed positive accuracy and valid
confidence its total number of comparisons is `O(n log n)`. The
standalone Lemma-21 estimator uses the Supplemental PDF's exact
`ceil((1 / (2 epsilon²)) log(2 / delta))` count; the retained text extraction
reverses that fraction. Theorem 9 and Supplement Theorem 22 still have their
displayed `2n / epsilon²` coefficient because Algorithm 9 invokes the estimator
at accuracy `epsilon/2`.
Theorem 7's lower-bound bridge is proved for finite adaptive policy trees with
arbitrary finite independent randomization. For Theorem 8, the exact
uniform-opponent source PMF and every finite adaptive reward trace are proved
equal to their Borda-mean Bernoulli-bandit counterparts. A ceiling-specified
uniform best-arm batch is now replayed as a finite sequential policy and
transferred to a literal Borda-maxing `1-delta` theorem; the cited QE
algorithm now also has a literal sequential QE-plus-final policy whose output
PMF is proved equal to the source joint experiment. Accordingly,
The source-facing `PaperInterface.theorem8_bordaMaxingSpec` therefore states
the abstract algorithm-existence, `1-delta` success, and source-rate comparison
claim without exposing that proof implementation. It chooses one algorithm
before the unknown win matrix, and its operational record proves that the
unpadded comparison count is a prefix-stable stopping count sufficient to
determine the output. The Zhou--Chen--Li result is proved in this repository
and used as an attributed proved dependency, not an external assumption.

Appendix B.2's Strong-Transitivity-Ranking now has its literal finite
Algorithm-6/7 execution.  A single product PMF samples each unordered,
distinct pair exactly once at the source ceiling budget; the reverse centered
estimate is obtained by negation (equivalently, the raw estimate is
complemented), rather than by a second independent batch.  The per-pair
Hoeffding tail, the full `1 - delta` epsilon-ranking guarantee, and the exact
`choose n 2` times ceiling-budget comparison count are proved.  The count is
bounded by `5 n² (1 + log(n / delta)) / epsilon²` for the source parameter
range, and therefore has a fixed-positive-accuracy,
fixed-valid-confidence `O(n² log n)` rate.
The standalone Lemma-19 estimator likewise uses the PDF's
`ceil((1 / (2 epsilon²)) log(2 / delta))` coefficient (the extraction again
reverses it); Algorithm 7's `epsilon/2` call recovers the `2 / epsilon²`
per-pair factor. Lean also follows Algorithm 7's immediately subsequent proof
where two PDF display typos occur: the reverse entry complements the empirical
forward estimate, and the selection threshold is `1/2 - epsilon/2`.
See `FORMALIZATION_AUDIT.md`.

Status: formalization scope complete; commit, publication, and other closeout
steps are intentionally deferred.
