# Source Clarifications

Source locators refer to `MSVV07AdWords.txt`.

## Theorem 8: finite suffix index

- Printed suffix exponent $k-i+1$ → $k-i$. The geometric dual witness gives
$\psi_k(i)=\sum_{j=i}^{k-1}y_j^*=1-(1-1/k)^{k-i}$, not the printed exponent
$k-i+1$ (`718–729`): at $k=2,i=1$ the values are $1/2$ and $3/4$.
Likewise, exact spend $i/k$ leaves $(k-i)/k$ unspent. These finite-index
corrections preserve the limiting tradeoff.

## Finite and limiting Theorem 8 readings

- **Paper:** with normalized optimal revenue $N$ and $k$ budget slabs, the
  argument bounds lost revenue by $N/k$, giving competitive ratio
  $1-1/e-1/k$ and then $1-1/e$ as $k\to\infty$.
- **Formalized source route:** under the paper's stated temporary Sections
  2--5 normalization (unit budgets and an offline allocation that assigns
  every arrival, respects budgets, and exhausts every bidder), the
  occurrence-indexed runner satisfies
  $$(1-1/e)\mathrm{OPT}\le\mathrm{ALG}+3N/(m+1)$$
  whenever every bid is at most its bidder's budget divided by $m+1$.
  The factor three records two finite weighted-accounting slab widths and one
  final unspent-budget slab width; it is an explicit source-faithful finite
  clarification, not a change to the limiting theorem.
- **Limit:** for a fixed advertiser population and any family satisfying that
  $1/(m+1)$ small-bids condition, $3N/(m+1)\to0$ automatically.  Lean proves
  the eventual $1-1/e$ competitive inequality against the actual
  occurrence-indexed offline optimum.  This is the paper's slab/small-bids
  limit, with no query-count-dependent convergence premise.
- For heterogeneous budgets, the auxiliary finite bound
  $E=\epsilon(e+1)\sum_q\max_a b_{aq}$ and its theorem under the explicit
  premise $E_r\to0$ provide a separate route when its stated error condition holds.

## Section 5 Lemma 7: finite slab accounting

- **Source clarification:** in the Theorem 8 dual-induced tradeoff, the
  source treats exact bidder types and nonstraddling payments as a negligible
  slab-width simplification. For the actual occurrence-indexed run, the
  weighted perturbation is at most $2N/k$: one slab width accounts for the
  right endpoint used to assign a final type, and one for a payment that
  crosses a slab boundary. This finite reading applies to that Theorem 8
  tradeoff, not to an arbitrary weighting function, and it leaves the
  $1-1/e$ limit unchanged.

## Sections 4--5: idealized slab lemmas

- **Source clarification:** before Section 4 Lemma 2, and again before
  Section 5 Lemma 5, the source explicitly asks the reader to idealize every
  final type as ending exactly at a slab boundary and to forbid
  boundary-crossing payments. The formalized Lemmas 2 and 5 derive the
  resulting beta identities from that stated idealized slab definition. For
  Lemma 2, the finite ledger records each OPT-assigned query, its common bid,
  and its Balance and OPT slabs; the local BALANCE rule proves Lemma 1 for
  each ledger event, and summing those events derives the required prefix
  inequality.
- **Finite source route:** for the dual tradeoff used in Theorem 8, the actual
  occurrence runner replaces Lemma 6's suppressed endpoint case with its
  explicit one-slab term. Lemma 7 and Theorem 8 bound the aggregate effect, so
  this clarification does not add a condition or change the limiting result.

## Section 4 tightness

- **Source clarification:** MSVV cites KP00 as an example of a tight finite
  instance but does not print its query--bidder incidence data. The
  formalization proves the existential tightness claim with an explicit,
  source-compatible finite nested-cohort family: for each `m`, it has
  `(m+1)^m` unit-budget bidders, bid `1/(m+1)`, a fixed deterministic Balance
  tie rule, a history covering every query, an exact offline assignment of
  value `(m+1)^m`, and an actual online/offline ratio converging to `1-1/e`.
  This does not claim to reconstruct KP00's unprinted construction or identify
  its incidence data with this family.

## Theorem 9: query-split lower-bound model

- **Source clarification:** Theorem 9 fixes an arbitrary deterministic online
  algorithm and writes $q_{ij}$ for the fraction of the identical queries in
  round $i$ that it allocates to bidder $j$ (`897–938`). Thus a round may be
  split among several currently eligible bidders, with the unallocated queries
  left unused; it is not a one-bidder choice for a collapsed round.
- **Formalized reading:** on this finite hard family, a deterministic policy is
  represented by its nonanticipating integer allocation counts for the $b$
  identical queries in each round. The counts enforce both the per-round and
  per-bidder capacities, and a randomized policy is a distribution over those
  finite policies. This is the source's $q_{ij}$ normal form, so the harmonic
  upper bound applies to actual normalized revenue of every feasible split.
- This convention makes the lower-bound model explicit; it adds no hypothesis
  and does not change Theorem 9's $1-1/e$ conclusion.

## Section 6 variants

- **Own-bid smallness → a bound on every possible winner's actual charge:**
  at most $\epsilon$ times that winner's budget. With unequal budgets, this
  does not follow just from bounding each bidder's own bid. The checked
  comparison also keeps all bidders alive so both charge definitions agree.
  These are current proof restrictions, not demonstrated necessities.
- **Qualitative scan efficiency → a unit-cost operation count.** Feasibility
  tests and exact real score comparisons cost one unit. Bit complexity for
  real arithmetic and exponential evaluation is not established.

## Section 8 weighted-bid proposal

- **Uncredited implementation:** the source uses weighted effective bids for
  allocation; the experimental runner also scales charges and budget
  feasibility. A bid of 10, weight 2, and remaining budget 15 should cost 10,
  but this runner treats it as 20 and rejects it.
- No checked theorem uses that runner. Its repair remains future work.

## Appendix counterexample: three-phase revenue

- Appendix phase totals $0.4N+0.2N+0$ sum to $0.6N$, not $0.62N$
(`1182–1220`). The execution also leaves a positive phase-two tail residual
$3/5-\log(9/5)$: phase one spent $\log(9/5)$ rather than the amount required
for exhaustion. Serving the residual in phase three gives online revenue
$9/10-\tfrac12\log(9/5)$ against offline value one. This is still strictly
below $1-1/e$, preserving the qualitative counterexample in the source's
continuous small-bid limit.

## The `kappa` witness family

- The unparameterized $\{0,a,\kappa a\}$ construction for every $\kappa>1$ (`1221–1224`) → the explicit continuous-limit witness below. Here $x,b,t$ are phase fractions and $a$ the bid scale:

$$u=1/\kappa,\quad z=e^{1-u},\quad d=z+u^2,
\qquad (x,b,t)=\frac{(u^2,z-1,1)}d.$$

These positive phase fractions sum to one. The tail spends
$\log((1-x)/t)=1-u$ in phase one and $\kappa x/t=u$ in phase two, exhausting
its unit budget. Offline revenue is $b+x+t=1$, while online revenue is

$$R(\kappa)=b+\kappa x=\frac{z-1+u}{z+u^2}<1-1/e.$$

The checked limits are $R(\kappa)\to1/2$ as $\kappa\downarrow1$ and
$R(\kappa)\to1-1/e$ as $\kappa\to\infty$. The right limit at one is not
the separate equal-bid Balance execution. No fixed-positive-$a$ discretization
bound is asserted by this continuous construction.
