import GKP26LinearRepresentationHypothesis.MainTheorems

/-!
# Paper Assumptions: Linear Representation Hypothesis Capacity

All current paper-facing hypotheses are explicit parameters of the definitions
and theorems in `MainTheorems.lean` and `PaperInterface.lean`.  Exact
basis-pursuit recovery at the logarithmic measurement scale is a proved
reusable theorem in `AppliedModelingLib.Foundations.Probability.RademacherCompressedSensing`.
The one external theorem boundary is Alon's cited near-identity matrix-rank
bound.  The paper states that result as Lemma `lem:alon` and attributes it to
Alon (2003), Theorem 9.3; the paper's scaled corollary is proved in Lean from
this exact boundary.
-/

namespace GKP26LinearRepresentationHypothesis

open AppliedModelingLib.Math.RankBounds

/--
External cited theorem boundary for source Lemma `lem:alon`: there is a
positive universal constant for the normalized near-identity rank lower
bound.  This is the mathematical content of the source's `Omega` notation.
-/
axiom assumption_alon_normalized_rank_bound :
  ∃ c : ℝ, AlonNormalizedStrictRankBoundHolds c

end GKP26LinearRepresentationHypothesis
