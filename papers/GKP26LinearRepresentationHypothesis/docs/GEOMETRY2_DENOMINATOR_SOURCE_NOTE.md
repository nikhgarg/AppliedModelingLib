# Proposition 11: Denominator Typo

**Parts (ii)–(iii):** the first term is $\epsilon\gamma^2/(1-\epsilon)^2$ in place of $\epsilon\gamma^2/(1-\epsilon)$, where $\epsilon$ is the recovery tolerance and $\gamma$ bounds each vector norm.

For $0<\epsilon<1$, recovery gives $|\langle b_i,a_j\rangle|<\epsilon$ for $i\ne j$ and $\|a_i\|,\|b_i\|>(1-\epsilon)/\gamma$. Normalizing by two norms therefore gives

$$
\left|\left\langle\frac{b_i}{\|b_i\|},\frac{a_j}{\|a_j\|}\right\rangle\right|
<\frac{\epsilon\gamma^2}{(1-\epsilon)^2}.
$$

The missing factor is a local normalization correction in the printed proof. It makes the finite bound slightly larger; at $\gamma=1$, the near-orthogonality conclusion as $\epsilon\to0$ follows with either expression. The corrected expression is proved; this normalization argument alone does not rule out a sharper bound by another proof.

**Source:** Proposition 11(ii)–(iii) and its proof, Section 4.
