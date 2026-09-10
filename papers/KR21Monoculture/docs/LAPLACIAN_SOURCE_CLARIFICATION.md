# Appendix C Lemma 1: Laplacian Clarification

- **Definition 4/Appendix C Lemma 1's global strict inequality → a weak
  inequality globally, strict only on overlap.** For
  $f(x)=e^{-\lambda|x|}$, $\lambda\geq0$, and $a>b,c>d$,
  $$f(a-c)f(b-d)\geq f(a-d)f(b-c).$$
  It is strict when $\lambda>0$, $b<c$, and $d<a$, so $(b,a)$ and $(d,c)$
  overlap. Source: [*Algorithmic Monoculture and Social Welfare*](https://arxiv.org/abs/2101.05853).
- **Evidence:** at $\lambda=1$ and $(a,b,c,d)=(11,10,2,1)$, both products
  equal $e^{-18}$. Separated intervals lie on linear absolute-value pieces,
  whose cross difference cancels; overlap makes that difference strict.
  Density normalization cancels from the comparison. Integrating the weak
  global inequality with strictness on a positive-mass overlap region supplies
  the downstream strict Laplace ranking comparison.

The [full explanation and downstream consequences](LAPLACIAN_LEMMA1_SOURCE_NOTE.md) give the source comparison and complete four-point calculation.
