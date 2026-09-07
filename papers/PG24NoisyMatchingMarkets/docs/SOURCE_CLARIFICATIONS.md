# Source clarifications: Wisdom and Foolishness of Noisy Matching Markets

Source: [*Wisdom and Foolishness of Noisy Matching Markets*](https://arxiv.org/abs/2402.16771). Propositions, lemmas, definitions, corollaries, remarks, examples, and conjectures share one counter, separate from the main theorem counter; the numbering below is the numbering rendered by the paper.

## Proposition 1: tail orientation and unproved polynomial rate

- The displayed integral above the market-clearing threshold has the wrong tail orientation. The surrounding prose and footnote concern matched mass below that threshold. Above the threshold, matching probability tends to one, so the integral tends to the positive supply and cannot decay to zero.
- The corrected lower-tail mass is proved to vanish uniformly over the admissible economies and stable matchings. The intended `O(C^{-K(β,γ)})` rate remains unproved. The printed big-O statement does not specify a constant uniform over varying stable matchings, and its large-gap route also uses the unresolved Proposition 7(ii) estimate. The qualitative conclusion suffices for Theorem 1.

## Proposition 7(ii) and Proposition 8: unproved polynomial rates

- Proposition 7(i)'s maximum-affordance rate is proved exactly. For Proposition 7(ii), the current proof establishes convergence to one of high-value affordability but not its printed error rate `O(C^{-2φ₁-2φ₃+2φ₂}) = O(C^{-K(β,γ)})`. The source's maximum-concentration assumption bounds variances of large-sample maxima, while the printed step invokes a one-draw lower-tail Chebyshev estimate. It also uses an atom-sensitive strict-tail complement and omits the square in Chebyshev's denominator.
- Proposition 8 displays the rate `O(C^{-K(β,γ)})`. Its printed proof depends on Proposition 7(ii)'s unavailable polynomial estimate. The current formalization proves only that the same high-cutoff, low-value integral converges to zero.
- A suitable one-draw lower-tail bound would support the printed route. The current work neither derives that bound from maximum concentration nor gives a counterexample to the two rate claims under all source hypotheses.

## Other appendix proof corrections

- Cutoff blocks omitting equality at boundary `P*` → a complete partition assigning each boundary college to one side, with integer rounding of block sizes.
- Propositions 2 and 5 use `φ₃-1=-K(β,γ)`: a block of `C^φ₃` colleges, each of capacity `α/C`, has capacity `α C^(φ₃-1)`. The printed proofs contain sign errors; the displayed conclusions are unchanged.
- Propositions 3 and 4 require the low-value deviation event to be contained in the Chebyshev event, together with the actual endpoints from the middle-integral decomposition. The corrected argument preserves their displayed conclusions and polynomial exponents.
- Lemma 6 replaces the printed maximum-growth equality with a triangle inequality and an independent-sample dyadic argument. The associated large-gap calculation also uses atom-safe strict and weak tails and a squared deviation denominator.
- Proposition 9's central interval uses its upper quantile endpoint consistently. To obtain Theorem 2 for every real target, the proof starts from an interior anchor and applies the source long-tail comparison through finitely many value shifts. A bounded connected value support cannot eventually contain every real target inside the central quantile interval.

## Coalition conditional laws

- Conditional noise specifications for every true-value vector → almost-everywhere conditional laws on the student-law support. This determines all affordability probabilities and integrals in Theorems 3–4; no off-support kernel is specified.
