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
- **Formalized:** for bids at most a fraction $\epsilon$ of their bidder's
  budget, the current proof gives
  $$(1-1/e)\mathrm{OPT}\le\mathrm{ALG}+E,\qquad
  E=\epsilon(e+1)\sum_q\max_a b_{aq}.$$
  Here the sum is the total of the largest bid at each query occurrence.
  The family theorem additionally assumes $E_r\to0$ and proves vanishing
  absolute additive error.
- **Formalization gap:** the paper fixes $N$ and sends the number of budget
  slabs $k$ to infinity, using $N/k\to0$. The current family theorem does not
  construct that discretization family or derive $E_r\to0$ from that regime.

## Section 4 tightness

- **Asserted finite tight instance → a proved fluid construction only.**
  The paper does not specify the finite query–bidder incidence construction
  in Section 4. The formalization makes the factor-LP constraints tight in
  a cohort-fluid limit; constructing the finite instance remains open.

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
