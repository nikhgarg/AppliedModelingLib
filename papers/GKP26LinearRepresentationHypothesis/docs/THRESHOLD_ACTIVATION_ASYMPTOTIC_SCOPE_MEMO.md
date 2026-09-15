# Theorem 12 and Corollary 13: Threshold and Activation Bounds

- **Proof coverage:** the printed Alon–Turan submatrix argument covers only part of $k<\sqrt m$ → supplement it with a trace/Frobenius argument on the remaining range. This preserves the stated lower bound $d=\Omega((k^2/\log k)\log(m/k))$, conditional on the [cited Alon rank theorem](ALON_RANK_COROLLARY_SOURCE_NOTE.md).

**Source:** Theorem 12 and Corollary 13. Here $m$ is the number of features, $k$ the sparsity bound, and $d$ the representation dimension.

- **Submatrix condition:** $m>k^2$ does not ensure that a submatrix of size approximately $m/(4k+1)$ exceeds $k^2$, as needed for the rank step. The formalized split uses $q=k-1$ and $(4q+1)q^2<m$ for that branch. This identifies a proof-step gap, not a counterexample to the theorem.

- **Added argument:** after row normalization, $C=B^\top A$ has $C_{ii}=1$. Threshold separation gives $\sum_{j\in T}|C_{ij}|\leq2$ for every off-diagonal set $|T|\leq q=k-1$. Therefore $\|C\|_F^2\leq m(5+4m/q^2)$. For $H=(C+C^\top)/2$, use $\operatorname{tr}H=m$, $\operatorname{rank}H\leq2d$, and $\|H\|_F\leq\|C\|_F$ to obtain
  $$
  d\geq\frac{m}{2(5+4m/q^2)},\qquad k^2\leq42d
  \quad(k\geq3,\ m>k^2).
  $$

- **Intermediate range:** when $k^2<m\leq(4(k-1)+1)(k-1)^2$, the source scale satisfies $(k^2/\log k)\log(m/k)\leq4k^2\leq168d$. Combine this with the Alon–Turan branch for larger $m$ to recover the full printed asymptotic regime.
