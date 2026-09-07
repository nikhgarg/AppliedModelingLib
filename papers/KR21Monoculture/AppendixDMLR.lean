import KR21Monoculture.Sequential

/-!
# KR21 Appendix D likelihood-ratio audit surface

The proof of Theorem 2 in Appendix D (source lines 2272--2434) compares the
first remaining candidate under two identity-centred Mallows distributions.
Its displayed inequality (D.1) has the direction opposite to the preceding
claim that the relevant ratio has positive derivative in `φ`.  In the library
parameter `q = φ⁻¹`, a more accurate distribution has the smaller parameter.

`AppendixDCorrectedMallowsMLR` records the denominator-cleared version with
the direction compatible with that parameterization.  It deliberately remains
an obligation for arbitrary remaining sets: this file only exposes the cases
whose proofs are present in the library.  In particular, no use of this
definition may be read as a proof of the generic claim.

The source's asserted polynomial argument is not a proof of the generic
obligation: its displayed coefficients are normalized fibre probabilities and
therefore depend on `φ`.  The checked results below are useful restricted
repairs, while `AppendixDCorrectedMallowsMLR` is the exact all-subset target.
-/

open scoped BigOperators
open AppliedModelingLib

namespace KR21Monoculture

/--
The corrected, denominator-cleared likelihood-ratio claim corresponding to
KR21 Appendix D.  `qAccurate < qNoisy` represents `φAccurate > φNoisy`, so a
smaller centre rank has relatively more mass under the accurate distribution.

This has the source's universal quantification over every nonempty set of
remaining candidates.  It is an audit obligation, not a theorem asserted by
this module for arbitrary `remaining`.
-/
def AppendixDCorrectedMallowsMLR
    (n : ℕ) (qAccurate qNoisy : ℝ) : Prop :=
  ∀ {remaining : Finset (Candidate n)}, remaining.Nonempty →
    ∀ {better worse : Candidate n},
      better ∈ remaining → worse ∈ remaining → better < worse →
        0 ≤
          reflMallowsBestInSetWeight n qAccurate remaining better *
              reflMallowsBestInSetWeight n qNoisy remaining worse -
            reflMallowsBestInSetWeight n qAccurate remaining worse *
              reflMallowsBestInSetWeight n qNoisy remaining better

/-- The Appendix D audit obligation is definitionally the existing generic
best-in-set MLR obligation. -/
theorem appendixD_correctedMallowsMLR_iff_reflMallowsBestInSetWeightMLR
    (n : ℕ) (qAccurate qNoisy : ℝ) :
    AppendixDCorrectedMallowsMLR n qAccurate qNoisy ↔
      ReflMallowsBestInSetWeightMLR n qAccurate qNoisy :=
  Iff.rfl

/--
The corrected likelihood-ratio direction is strict when exactly two candidates
remain.  This is valid for every finite source candidate count.
-/
theorem appendixD_corrected_mlr_pair_strict
    (n : ℕ) {qAccurate qNoisy : ℝ} (hqAccurate_pos : 0 < qAccurate)
    (hq_lt : qAccurate < qNoisy) {better worse : Candidate n}
    (hbetter_worse : better < worse) :
    0 <
      reflMallowsBestInSetWeight n qAccurate
          ({better, worse} : Finset (Candidate n)) better *
        reflMallowsBestInSetWeight n qNoisy
          ({better, worse} : Finset (Candidate n)) worse -
      reflMallowsBestInSetWeight n qAccurate
          ({better, worse} : Finset (Candidate n)) worse *
        reflMallowsBestInSetWeight n qNoisy
          ({better, worse} : Finset (Candidate n)) better :=
  reflMallowsBestInSetWeight_pair_cross_pos
    n hqAccurate_pos hq_lt hbetter_worse

/--
For every source candidate count, the corrected likelihood-ratio direction is
proved for center-convex remaining sets.
-/
theorem appendixD_corrected_mlr_centerConvex
    (n : ℕ) {qAccurate qNoisy : ℝ} (hqAccurate_pos : 0 < qAccurate)
    (hq_lt : qAccurate < qNoisy) {remaining : Finset (Candidate n)}
    (hremaining : remaining.Nonempty) (hconvex : CenterConvex remaining)
    {better worse : Candidate n} (hbetter : better ∈ remaining)
    (hworse : worse ∈ remaining) (hbetter_worse : better < worse) :
    0 ≤
      reflMallowsBestInSetWeight n qAccurate remaining better *
          reflMallowsBestInSetWeight n qNoisy remaining worse -
        reflMallowsBestInSetWeight n qAccurate remaining worse *
          reflMallowsBestInSetWeight n qNoisy remaining better :=
  reflMallowsBestInSetWeight_cross_nonneg_centerConvex
    n hqAccurate_pos hq_lt hremaining hconvex hbetter hworse hbetter_worse

/--
The corrected all-subset MLR obligation is fully proved in the three-candidate
universe.  This is the first nontrivial finite-universe closure.
-/
theorem appendixD_corrected_mlr_three_candidates
    {qAccurate qNoisy : ℝ} (hqAccurate_pos : 0 < qAccurate)
    (hq_lt : qAccurate < qNoisy) :
    AppendixDCorrectedMallowsMLR 1 qAccurate qNoisy :=
  reflMallowsBestInSetWeightMLR_one hqAccurate_pos hq_lt

/--
When every candidate remains, the Appendix D likelihood-ratio direction
reduces to the first-choice Mallows calculation for every finite universe.
-/
theorem appendixD_corrected_mlr_full_remaining
    (n : ℕ) {qAccurate qNoisy : ℝ} (hqAccurate_pos : 0 < qAccurate)
    (hq_lt : qAccurate < qNoisy) {better worse : Candidate n}
    (hbetter_worse : better < worse) :
    0 ≤
      reflMallowsBestInSetWeight n qAccurate Finset.univ better *
          reflMallowsBestInSetWeight n qNoisy Finset.univ worse -
        reflMallowsBestInSetWeight n qAccurate Finset.univ worse *
          reflMallowsBestInSetWeight n qNoisy Finset.univ better :=
  reflMallowsBestInSetWeight_univ_cross_nonneg
    n hqAccurate_pos hq_lt hbetter_worse

/--
The inequality direction printed in Appendix D cannot be correct even in the
two-candidate instance.  This is its denominator-cleared reverse direction:
the source's ratio form is equivalent because its Mallows fibre weights are
strictly positive for the positive parameters used below.
-/
def AppendixDPrintedReverseMLR
    (n : ℕ) (qAccurate qNoisy : ℝ) : Prop :=
  ∀ {remaining : Finset (Candidate n)}, remaining.Nonempty →
    ∀ {better worse : Candidate n},
      better ∈ remaining → worse ∈ remaining → better < worse →
        reflMallowsBestInSetWeight n qAccurate remaining better *
            reflMallowsBestInSetWeight n qNoisy remaining worse -
          reflMallowsBestInSetWeight n qAccurate remaining worse *
            reflMallowsBestInSetWeight n qNoisy remaining better ≤ 0

/-- A concrete, machine-checked refutation of Appendix D's printed direction. -/
theorem appendixD_printed_reverse_mlr_false_two_candidates :
    ¬ AppendixDPrintedReverseMLR 0 ((1 : ℝ) / 2) ((3 : ℝ) / 4) := by
  intro hreverse
  have hpositive :=
    appendixD_corrected_mlr_pair_strict 0 (qAccurate := (1 : ℝ) / 2)
      (qNoisy := (3 : ℝ) / 4) (by norm_num) (by norm_num)
      (better := (0 : Candidate 0)) (worse := (1 : Candidate 0)) (by norm_num)
  have hnonpositive :=
    hreverse (remaining := ({(0 : Candidate 0), (1 : Candidate 0)} : Finset _))
      (better := (0 : Candidate 0)) (worse := (1 : Candidate 0))
      (by simp) (by simp) (by simp) (by norm_num)
  linarith

end KR21Monoculture
