# Source clarifications: Internet Advertising and the Generalized Second-Price Auction

Source: [NBER Working Paper 11765](https://www.nber.org/papers/w11765),
Definition 4, Lemmas 5–6, and Theorems 7–8.

## Definition 4: unassigned bidders and the bottom slot

- **Adjacent allocated-rank no-envy → also no bottom-slot envy by every
  unassigned bidder:** require $\alpha_N(s_a-q_N)\leq0$ for every unassigned
  bidder $a$, where $\alpha_N$ and $q_N$ are the bottom position's click-through
  rate and per-click price, and $s_a$ is that bidder's value. This restricts the
  equilibria covered by Lemma 5 and Theorem 7's revenue comparison.
- **Counterexample to the printed condition:** one position with click rate
  $1$, values $(10,9)$, and bids $(10,0)$ is a GSP Nash equilibrium with vacuous
  adjacent-rank no-envy. The winner pays zero; the loser cannot profitably
  outbid $10$, but values the position at its recorded zero price. Thus the
  assignment is unstable, and its revenue $0$ is below the VCG revenue $9$.
  The added inequality excludes it. Checking only the first unassigned bidder
  would not control lower bidders whose values need not follow bid order.

## Lemma 6: positive winner surplus

- **Every stable assignment → stable assignments with strictly positive utility
  for every winner.** This added domain condition makes the Appendix's
  constructed bids strictly decreasing, preserving the allocation and winner
  payments under strict bid order.
- **Obstruction without strict surplus:** take click rates $(2,1)$, values
  $(10,9,8)$, and assign the first two bidders at per-click prices $(9,9)$.
  Utilities are $(2,0,0)$: the first bidder gets only $1$ in the lower position,
  the second is indifferent to the upper position, and the third loses from
  either. The assignment is stable, but exact GSP payment realization forces
  both the second and third bids to equal $9$. Under random tie ordering, the
  value-$8$ bidder prefers bidding slightly less to risking a loss. This
  demonstrates the strict-bid obstruction.
- **Unspecified bid lower bound → real-valued bids.** With multiple unassigned
  bidders, the strictly decreasing auxiliary bid tail can be negative. A
  nonnegative-bid version would need a positive-tail condition; it is outside
  this implementation result.

## Theorem 8: symmetric continuation plans

- **Bidder-specific continuous strategies $p_i(k,h,s_i)$ → one common
  continuation plan instantiated at every bidder.** Here $k$ is the number of
  remaining bidders, $h$ the auction history, and $s_i$ bidder $i$'s value.
  Effective dropout-action uniqueness is proved only among equilibria in this
  symmetric class. Uniqueness over arbitrary bidder-specific profiles remains
  unproved; the scope restriction supplies no counterexample to it.
