# Source Clarifications: Competitive Auctions and Digital Goods

## Logarithmic domains

- **Unqualified logarithmic revenue bounds → $h\geq2$** in Theorem 4.1,
  Theorem 7.1, and Theorem 7.2's lower bound; **at least two bidders** in
  Corollary 4.2. Here $h$ is the largest normalized bid. At $h=1$ or bidder
  count $n=1$, the relevant denominator $\log_2h$ or $\log_2n$ is zero.
  The $h\geq2$ scope also excludes $1<h<2$, where the logarithm is defined;
  this proof restriction is not shown necessary for every revenue bound.

## Lemma 8.1 and Theorem 8.2

- **Preliminary-version inference from truthfulness → the journal version's
  monotone-offer condition:** if bids satisfy $b_i\leq b_j$ and $x\leq b_i$,
  bidder $i$'s probability of receiving and accepting an offer at price at
  most $x$ is no greater than bidder $j$'s. Truthfulness controls changes in
  one's own report and does not alone supply this cross-bidder comparison.
  The Lemma 8.1 and Theorem 8.2 proofs use the journal condition.

## Randomization and bounded supply

- **General randomized offers → countably supported outcome laws, and finite
  offer support in Lemma 8.1 and Theorem 8.2.** These restrict the current formalization's
  randomization domain; continuous-offer extensions remain unproved.
- **Arbitrary excess-demand rejection → one report-independent priority**
  among accepted bidders. This fixes the source's unspecified choice; the
  current result does not quantify over every rejection rule.

- **Theorem 6.2 count parameter → natural-number $\alpha$** in the current
  probability bound; arbitrary real parameters would need a rounding argument.
- **Theorems 9.1 and 9.3 high-value constructions → integer $H\geq2$**, with bids
  $1$ or $H$ and at least one high bid. Its revenue/benchmark ratio is at
  most $1/H$; no arbitrary-real-$H$ construction is asserted.
- **Bounded dual-price mechanism → an exact equal-half partition and even
  total supply $2q$**, assigning capacity $q$ to each side. Other partition
  or odd-supply cases are outside that checked mechanism.
