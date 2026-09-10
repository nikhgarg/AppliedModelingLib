# Source Clarifications: Competitive Auctions and Digital Goods

## Logarithmic domains

- **Finite logarithmic bounds:** use $h\geq2$ for Theorems 4.1 and 7.1–7.2,
  and at least two bidders for Corollary 4.2, where $h$ is the largest
  normalized bid. The denominators vanish at $h=1$ or bidder count $n=1$.
  For $1<h<2$, the logarithm is defined but the dyadic proof's finite
  constant needs adjustment. The checked bounds give the source asymptotics;
  they do not assert the same finite coefficient throughout that smaller range.

## Lemma 8.1 and Theorem 8.2

- **Journal monotonicity condition:** for bids $b_i\leq b_j$ and prices
  $x\leq b_i$, bidder $i$'s probability of winning at a price at most $x$ is
  no greater than bidder $j$'s. This cross-bidder condition gives Lemma 8.1's
  allocation ordering and Theorem 8.2's bound $\mathbb{E}[R]\leq F$, where
  $F$ is optimal fixed-price revenue. The preliminary paper infers the
  condition from truthfulness; the [journal version, Definition 8.1 and
  Theorem 8.2](../cited publication), states it separately.
  Truthfulness by itself does not imply that comparison.
- **Inverse-CDF notation:** use the lower generalized inverse
  $\inf\{x:y\leq g_i(x)\}$ in the journal's common-uniform coupling.
  Its printed equality-level-set formula can be undefined at a CDF jump.
  The lower inverse has the required marginals and preserves the CDF ordering,
  so the expected-revenue argument applies to arbitrary real offer laws.

## Randomization and bounded supply

- **Randomization model:** the concrete mechanisms have finite outcome
  distributions, represented within a general model allowing countable
  distributions. Theorem 8.2 separately covers arbitrary real offer
  distributions. Accepted nonnegative offers are bounded by the bids, so
  their expected revenue is defined without an additional moment condition.
- **Excess demand:** when more bidders accept the price than there are items,
  serve them in a fixed priority order chosen independently of bids. This
  specifies one of the source's permitted rejection rules; it does not claim
  truthfulness for every possible rule that reacts to the bid amounts.
- **Theorem 6.2 count parameter:** take $\alpha$ to be a natural-number lower
  bound on the winner count, the role it plays in the source proof. The
  formalization proves the displayed probability bound for uniform exact
  half-sampling. A separate real-$\alpha$ calculation uses independent coin
  flips and is not an equivalence between the two sampling schemes.
- **Theorems 9.1 and 9.3 impossibility examples:** for every integer $H\geq2$
  and real $\alpha>0$, bids at $1$ and $H$ give $R/F\leq1/H$ and
  $F\geq\alpha H$. As $H$ grows, the revenue fraction tends to zero even
  with a large benchmark. Integer examples therefore prove the paper's
  no-constant-competitive-ratio conclusion. Theorem 9.1 treats deterministic
  bid-independent auctions; Lemma 9.2 extends it to the truthful deterministic
  set-of-bids model in Theorem 9.3. The construction does not parameterize
  every real $H$.
- **Half-sizes and parity:** interpret $n/2$ and $k/2$ as floor division for
  odd bidder counts or capacities. Truthfulness and total supply feasibility
  hold for all natural inputs; even inputs give exact halves. The bounded
  dual-price revenue guarantee remains conditional on its sampling good-event
  bounds, so this convention does not by itself prove an odd-input rate.
