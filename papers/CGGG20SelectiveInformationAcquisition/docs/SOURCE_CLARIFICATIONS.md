# Source Clarifications: Fair Allocation through Selective Information Acquisition

Source anchors refer to `audit/cited publication`.

## Full-vector posterior reading for allocation policies

The source defines the allocation rule as $A(\hat{\mathbf U})$ of the full
post-screening estimate vector (lines 285--291). Read together with its
realized-to-posterior utility comparison (lines 693--697), the displayed
estimate for applicant $i$ is the lender's posterior utility after observing
that full vector:

$$
  \hat U_i = \mathbb E[U_i \mid \sigma(\hat{\mathbf U})]
$$

almost surely. This is the source-model reading used for Definition 1,
Theorem 2, Appendix Lemmas 4--5 and 7, and Appendix Theorem 6. It preserves
the paper's full-vector allocation class and makes the corresponding
realized-to-posterior comparison applicable to every permitted allocation.

## Appendix Lemma 5 interpolation display

The proof display at lines 725--730 defines an unused quantity with an
undefined $t_i$ and then gives an interpolation probability that does not
follow from the displayed target. Let $A$ be expected utility strictly above
the threshold and $B$ be expected utility at the threshold. For a target
$\upsilon$ with $A \leq \upsilon \leq A+B$ and $B>0$, admit the boundary with
probability $\alpha=(\upsilon-A)/B$. The resulting expected utility is
$A+\alpha B=\upsilon$, and $\alpha\in[0,1]$. If $B=0$, the target is $A$ and
any boundary probability works. The same argument with expected costs proves
the cost branch. Thus the Lemma's stated conclusion is unchanged.

## Appendix Theorem 6 threshold-domain proof route

Appendix Definition 3 allows a cost-aware threshold to use any real cutoff or
either infinite endpoint (lines 626--636), and Appendix Lemma 5 consequently
may return any such cost-attaining witness (lines 704--712). The printed proof
of Appendix Theorem 6 immediately applies Lemma 4's equal-cost case to that
witness (lines 735--754), but Lemma 4 states that case only for a finite
threshold $t>0$ (lines 643--650). Thus the source does not establish the
threshold-domain premise needed for that displayed proof step. This is a
proof-route issue only: it does not change the statement of Appendix Theorem
6 or of the main-text Theorem 2 that follows from it.

The Lean proof uses the needed stronger route. It proves the equal-cost utility
comparison for every finite cutoff, handles the two endpoint threshold cases
separately, and only then combines that result with exact cost attainment. The
resulting theorem has the same paper-facing conclusion without adding an
economic assumption.
