# Source Clarifications

Source locations refer to `cited publication` and `cited publication`
for *Capacity Constraints Make Admissions Processes Less Predictable*.

## Capacity, variability, and queue representation

- **Theorem 1 no-zero and exact-one claims → positive, binding capacity
  $0<q<|U|$**, where $q$ is capacity and $U$ the applicant universe (main
  lines 281–285; appendix no-zero and q-representative arguments). At $q=0$
  everyone may be rejected; at $q\geq|U|$ everyone may be admitted. Both rules
  have instability and variability zero, so the exact nonzero conclusion excludes them.
- **Lemma A.1: two disjoint size-$q$ pools → one size-$(q+1)$ pool** in the
  monotonicity/q-acceptance contradiction (appendix lines 54–66). For $q>0$,
  q-acceptance admits every singleton; monotonicity would then admit all
  $q+1$ members of that pool, violating capacity. The proof therefore also
  covers universes smaller than $2q$.
- **Theorem 2's literal queue count → existence of a representation by one
  priority order** in the variability-one characterization. Redundant copies
  of a queue cannot change the choice rule. The range $1\leq m\leq n$, where
  $m$ is realized variability and $n$ the number of queues, is checked on the
  positive, binding-capacity domain above.

## Scores, strict orders, and assignment choices

- **Unrestricted strict-order completeness → comparison of distinct applicants
  only** (main lines 192–200). An applicant cannot strictly precede itself.
- **Raw-score rank selection → a fixed ex-ante tie order**, with $q>0$ and
  $q\leq|X|$ for the q-th threshold of pool $X$. This specifies the current
  selector, without asserting that raw predicted scores are distinct.
- **Lemma A.8 and Theorems A.10–A.11: unspecified selection among optimal
  linear assignments → a fixed generic refinement of the primary objective
  selecting one admitted set** (appendix lines 610–666). The source says
  weights have no ties; distinct weights can still give equal total assignment
  objectives. The refinement specifies a single choice in those cases.

## Exact appendix corrections

- **Lemma A.6, lines 422–433:** self-equality →
  $C(X_1)=C(X_2)\Rightarrow V_C(X_1)=V_C(X_2)$ for a feasible, q-acceptant,
  substitutable rule. Here $C(X)$ is the admitted set and $V_C(X)$ its members
  displaceable by one insertion. The source's one-instability condition supplies
  substitutability through Theorem 1.
- **Corollary A.3, lines 333–338:** $dk$ → $d=2k$ with $k>0$.
  Positive even tight instability is excluded; the $2k$ bound improves to
  $2k-1$.
- **Theorem A.6 proof, lines 397–416:** malformed union/deletion
  expression → $X=\bigcup_iX'_i=X_0\cup\{x'_1,\ldots,x'_m\}$, the pool formed
  by adjoining the selected applicants $x'_i$ to the base pool $X_0$.
- **Lemma A.7 proof, lines 435–442:** misplaced parenthesis →
  $X'\setminus\{x'\}=X$. The resulting removable-set equality also holds for
  pools smaller than capacity.
- **Theorem A.5 proof, lines 314–331:** applicant–set inequality →
  $x'\notin C(X')$. The new applicant's membership indicator is zero.
- **Theorem A.10 proof, lines 634–646:** self-comparison → comparison of
  $C(X')$ with $C(X)$, as required for the capacity contradiction.
- **Theorem A.11 proof, lines 656–666:** repeated applicant index → the distinct
  selected applicants $x_{s_i}$ and $x_{s_j}$ under their shared slot order.
