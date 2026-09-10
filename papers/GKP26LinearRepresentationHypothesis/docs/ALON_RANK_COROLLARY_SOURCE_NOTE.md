# Lemma 7 and Corollary 8: Alon Rank Bound

- **Proof boundary:** the source invokes Alon (2003), Theorem 9.3 → the formalization takes that theorem as a premise. Its standalone Lean representation is an axiom, with no native or proof-checked imported proof yet. Theorem 3, Theorem 12, and Corollary 13 use this external assumption.

- The unproved premise is the near-identity rank bound
  $$
  D_{ii}=1,\quad |D_{ij}|<\epsilon\ (i\ne j),\quad
  n^{-1/2}<\epsilon<1/2
  \quad\Longrightarrow\quad
  \operatorname{rank}D=\Omega\!\left(\frac{\log n}{\epsilon^2\log(1/\epsilon)}\right).
  $$

- **What remains conditional:** positive diagonal row scaling proves the source corollary from this premise. It supplies no proof of the premise itself.

**Source:** Lemma 7, citing Alon (2003), Theorem 9.3, and Corollary 8.
