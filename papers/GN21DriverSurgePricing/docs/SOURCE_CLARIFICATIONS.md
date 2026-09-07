# Source Clarifications for *Driver Surge Pricing*

Sources: [published article](https://doi.org/10.1287/mnsc.2021.4058) and [arXiv v4](https://arxiv.org/pdf/1905.07544v4).

## Policy domain and endpoint regularity

- **Source clarification:** Lemma 5 applies its stated policy-reward
  continuity to the finite endpoint families in its compactness argument,
  including their boundary representatives.
- **Source clarification:** its near-optimal response-shape condition is used
  on the policies in that reward band. The checked endpoint form makes the
  zero-length comparisons explicit when an interval collapses.
- **Theorem 4 policy continuity — Source clarification.** The paper's assumed
  continuity covers the acceptance-set domain used in the formalization, for
  either state in each feasible open two-state context.

## Theorem 3 proof route

- Lemma 9's “for each non-surge policy, there exists a feasible price ratio” → a direct Theorem 3 proof fixing one structured price before comparing every policy (Appendix D.4). This avoids reversing the quantifiers. If `C<R1/R2<1`, with target earning rates `R1,R2` and source feasibility threshold `C`, the comparison gives acceptance of every trip in both states. The general clause gives a finite or infinite upper cutoff in the non-surge state and acceptance of every surge trip.
