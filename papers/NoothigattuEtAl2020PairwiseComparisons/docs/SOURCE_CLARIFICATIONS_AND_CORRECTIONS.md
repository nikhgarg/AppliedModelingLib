# Source Clarifications: Axioms for Learning from Pairwise Comparisons

## Lemma 2.3 distinct alternatives

- **Positive directed counts for every pair → every distinct pair.** Diagonal
  counts are zero in the paper's pairwise-comparison model, so the literal
  all-pairs premise cannot hold.

## Counterexample proofs for Theorems 5.3 and 6.3

- **Continuity of the maximizer under small perturbations → a compact
  likelihood-gap argument.** A uniform score bound restricts the search to
  a compact set; a strict base-likelihood gap separates the bad-order set.
  An explicit positive rational perturbation is chosen whose bounded
  likelihood contribution cannot close that gap. The construction retains a strict
  score reversal under the source assumptions.
