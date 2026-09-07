# Source clarifications: approximately fair allocations

Source: [*On Approximately Fair Allocations of Indivisible Goods*](https://doi.org/10.1145/988772.988792), Theorem 2.3 and Lemma 2.4.

## Lemma 2.4: choosing a progressing endpoint

- Lemma 2.4's minimum endpoint at which every player values `[0,x]` by at most `alpha` → a finite high-point/residual partition. The minimum can be `x=0`, so the printed step need not advance. The replacement constructs pieces worth at most `alpha` to every player and applies the finite allocation theorem.
- For finitely many finite valuation measures `mu_i` on a common bounded interval, with every atom at most `alpha>0`, the result is an allocation `A` satisfying `mu_i(A_j)-mu_i(A_i)<=alpha` for all players `i,j`. The construction does not prove Lemma 2.4's `O(n/alpha)` piece-count bound, where `n` is the player count. Theorem 2.3's `alpha=0` branch still depends on the cited external envy-free allocation theorem.
