# Source clarifications for the linear representation hypothesis

<a id="geometry-proposition-1-choosing-the-coherence-scale"></a>

## Proposition 9: choosing the coherence scale

- **Auxiliary scale:** replace $\mu=\epsilon/[k(1+\lambda^2)]$ by
  $$
  \mu=\frac{\epsilon\lambda^2}
  {4(k+1)(1+\lambda)^2(1+\lambda^2)(1+2\lambda)},
  \qquad \lambda=\sqrt{1/\delta-1}.
  $$
  The printed choice gives recovery bound $\epsilon(1+\lambda)^2/(1+\lambda^2)>\epsilon$ for $\lambda>0$. The smaller choice proves recovery and keeps normalization denominators positive. For fixed $0<\epsilon,\delta<1$, it preserves the $O_{\epsilon,\delta}(k^2\log m)$ dimension rate. This is a sufficient construction, not a counterexample to the proposition.

**Source:** Proposition 9, `cited publication:547-610`; scale choice, `:580-597`.

## Nondegenerate parameter domains

- **Theorem 1 (compressed sensing):** the finite construction is proved for $1\leq k$ and $2k\leq m$. The paper identifies $k=O(\log m)$ as its intended regime in [Section 1.2](https://arxiv.org/html/2602.11246v1#S1.SS2); since $k/m\to0$, the finite cutoff holds for all sufficiently large $m$. The checked bound therefore proves the stated $d=O(k\log(m/k))$ asymptotic conclusion in that regime.
- **Theorem 3 (lower bound):** use the nontrivial accuracy range $0<\epsilon<1$, together with the displayed lower restriction on $\epsilon$. Since features lie in $[-1,1]$, tolerance $\epsilon>1$ already permits the zero predictor. The endpoint $\epsilon=1$ is outside the checked result.
- **Proposition 11:** $\epsilon>0$ → $0<\epsilon<1$, making the norm lower bounds used in division positive. This is the range covered by the normalization proof; necessity for every broader formulation is not established.

**Source:** compressed sensing, `cited publication:184-199`, intended regime `:227`; lower bound, `:220-227`; Proposition 11, `:638-680`.

## Proposition 11 and the lower-bound proof

- [Proposition 11](GEOMETRY2_DENOMINATOR_SOURCE_NOTE.md): first denominator $1-\epsilon$ → $(1-\epsilon)^2$.
- [Theorem 12 and Corollary 13](THRESHOLD_ACTIVATION_ASYMPTOTIC_SCOPE_MEMO.md): add a complementary rank argument for the part of $k<\sqrt m$ not covered by the printed submatrix argument.
- [Lemma 7 (cited Alon theorem)](ALON_RANK_COROLLARY_SOURCE_NOTE.md): remains an external proof boundary for the lower-bound branch.
