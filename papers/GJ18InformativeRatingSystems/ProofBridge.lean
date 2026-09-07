import GJ18InformativeRatingSystems.ClarifiedSourceModel
import GJ18InformativeRatingSystems.SourceRatePositivity

/-!
# Human-Facing Paper Interface: Designing Informative Rating Systems

This is the source-facing review surface for Garg and Johari (2018).  It keeps
three semantic layers distinct:

* literal formulas over the source state `mu_k`;
* an explicit finite iid horizon completion, with the author-confirmed model
  additions exposed below rather than inferred from the source recurrence; and
* the corrected finite-support rate statement, which uses `WithTop Real` so a
  threshold outside a score support cannot be silently assigned a spurious
  real Legendre value.

The rows below are deliberately named by their source role, but auditing must
unfold their types and dependencies rather than relying on those names.
-/

namespace GJ18InformativeRatingSystems.ProofBridge

noncomputable section

open Filter AppliedModelingLib.Probability

/-- Source object: the paper's single-rating log-MGF `Lambda(z | theta)`. -/
abbrev sourcePaperLogMGF {Seller Rating : Type*} [Fintype Rating]
    [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (theta : Seller) (z : Real) : Real :=
  ratingLogMGF M theta z

/-- Literal real-valued display of the paper's Legendre transform. -/
abbrev sourcePaperRateFunction {Seller Rating : Type*} [Fintype Rating]
    [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (theta : Seller) (a : Real) : Real :=
  ratingRateFunction M theta a

/-- Corrected support-safe rate convention used by the checked asymptotics. -/
abbrev sourcePaperRateFunctionTop {Seller Rating : Type*} [Fintype Rating]
    [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (theta : Seller) (a : Real) :
    WithTop Real :=
  ratingRateFunctionTop M theta a

/--
Source definition `n_k(theta) = floor(k g(theta))`
(`adjectivesmodel.tex:26-29`).

Source status: retained source formula; the corrected governing model adds
strict positivity and the at-most-one-match upper bound explicitly.
-/
theorem source_definition_floor_sample_count_formula
    {Seller : Type*} (sampleRate : Seller -> Real) (theta : Seller) (k : Nat) :
    floorSampleCount sampleRate theta k =
      Nat.floor ((k : Real) * sampleRate theta) := by
  rfl

/--
Corrected aggregate-score formula (`adjectivesmodel.tex:54-59`).  The source
display has an off-by-one upper sum index; its text and denominator specify
exactly `n_k(theta)` observed ratings, represented here by `Fin n_k(theta)`.

Source status: author-approved index correction retaining the stated
`n_k(theta)`-observation average.
-/
theorem source_definition_aggregate_score_formula
    {n : Nat} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel (Fin n) Rating)
    (sampleRate : Fin n -> Real) (k : Nat)
    (sample : finiteChainJointFloorRatingSample Rating sampleRate k)
    (theta : Fin n) :
    finiteChainJointFloorAverageScore M sampleRate k sample theta =
      ((floorSampleCount sampleRate theta k : Nat) : Real)⁻¹ *
        (Finset.univ.sum fun i => M.score (sample theta i)) := by
  rfl

/--
Literal source-state `P_k` formula (`adjectivesmodel.tex:78-83`).  No iid law
is inserted into this row.

Source status: retained source formula; its corrected-model state law is made
explicit in the separate iid-state row below.
-/
theorem source_definition_pairwise_objective_formula
    {n : Nat} {Omega : Type*} [Fintype Omega] [DecidableEq Omega]
    (mu : PMF Omega) (score : Omega -> Fin n -> Real)
    (p : finiteChainOrderedPair n) :
    sourceStatePairwisePk mu score p =
      AppliedModelingLib.pmfProb mu
        (fun omega => score omega (finiteChainOrderedPairHi p) >
          score omega (finiteChainOrderedPairLo p)) -
        AppliedModelingLib.pmfProb mu
          (fun omega => score omega (finiteChainOrderedPairHi p) <
            score omega (finiteChainOrderedPairLo p)) := by
  rfl

/--
Literal source-state `W_k` normalization (`adjectivesmodel.tex:85-90`).

Source status: retained source formula over the explicit strict-pair carrier;
the corrected model requires at least two seller types.
-/
theorem source_definition_uniform_ranking_objective_formula
    {n : Nat} {Omega : Type*} [Fintype Omega] [DecidableEq Omega]
    (mu : PMF Omega) (score : Omega -> Fin n -> Real) :
    sourceStateWk mu score =
      (2 : Real) / ((n : Real) * ((n : Real) - 1)) *
        (Finset.univ.sum fun p : finiteChainOrderedPair n =>
          sourceStatePairwisePk mu score p) := by
  rfl

/--
The source coefficient is the exact uniform finite-pair weight for `n >= 2`.

Source status: checked finite normalization of the retained `W_k` formula.
-/
theorem source_definition_uniform_ranking_normalization
    {n : Nat} {Omega : Type*} [Fintype Omega] [DecidableEq Omega]
    (mu : PMF Omega) (score : Omega -> Fin n -> Real) (hn : 2 <= n) :
    sourceStateWk mu score = sourceStateUniformWk mu score := by
  exact sourceStateWk_eq_sourceStateUniformWk mu score hn

/--
Explicit iid completion bridge for source `P_k`.  This is a corrected model
completion, not a consequence of the printed `mu_k` recurrence
(`adjectivesmodel.tex:67-73`).

Source status: author-approved iid completion, not an archive-recurrence
derivation.
-/
theorem source_iid_completion_pairwise_objective_bridge
    {n : Nat} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    [DecidableEq (finiteChainOrderedPair n)]
    (M : FiniteRatingLDPModel (Fin n) Rating) (sampleRate : Fin n -> Real)
    (p : finiteChainOrderedPair n) (k : Nat) :
    sourceStatePairwisePk (iidFloorSourceStateLaw M sampleRate k)
        (iidFloorSourceStateScore M sampleRate k) p =
      twoSampleFloorPkObjectiveProb M sampleRate
        (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p) k := by
  exact sourceStatePairwisePk_iidFloorCompletion_eq_twoSampleFloorPkObjective
    M sampleRate p k

/--
Explicit iid completion bridge for the Appendix weak-inversion event
(`appendix_theory.tex:7-22`).

Source status: author-approved iid completion, not an archive-recurrence
derivation.
-/
theorem source_iid_completion_weak_inversion_bridge
    {n : Nat} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    [DecidableEq (finiteChainOrderedPair n)]
    (M : FiniteRatingLDPModel (Fin n) Rating) (sampleRate : Fin n -> Real)
    (p : finiteChainOrderedPair n) (k : Nat) :
    sourceStateScoreGapLeftTailProb (iidFloorSourceStateLaw M sampleRate k)
        (iidFloorSourceStateScore M sampleRate k) p =
      twoSampleFloorScoreGapLeftTailProb M sampleRate
        (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p) k := by
  exact
    sourceStateScoreGapLeftTailProb_iidFloorCompletion_eq_twoSampleFloorScoreGapLeftTailProb
      M sampleRate p k

/--
Under the explicit iid completion, source `W_k` is the finite uniform
floor-count objective.

Source status: author-approved iid completion, not an archive-recurrence
derivation.
-/
theorem source_iid_completion_uniform_ranking_objective_bridge
    {n : Nat} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    [DecidableEq (finiteChainOrderedPair n)]
    (M : FiniteRatingLDPModel (Fin n) Rating) (sampleRate : Fin n -> Real)
    (k : Nat) (hn : 2 <= n) :
    sourceStateWk (iidFloorSourceStateLaw M sampleRate k)
      (iidFloorSourceStateScore M sampleRate k) =
      finiteUniformFloorPkObjective M sampleRate
        finiteChainOrderedPairHi finiteChainOrderedPairLo k := by
  exact sourceStateWk_iidFloorCompletion_eq_finiteUniformFloorPkObjective
    M sampleRate k hn

/--
Author-confirmed clarification: the finite ordered seller carrier has an
explicit uniform type prior (`adjectivesmodel.tex:22`).  This is not a
derivation from the archive's later conditional state formulas.

Source status: author-confirmed governing clarification, not an archive
recurrence derivation.
-/
theorem author_confirmed_clarified_uniform_type_prior
    {n m : Nat}
    {M : FiniteRatingLDPModel (Fin n) (Fin (m + 1))}
    {sampleRate : Fin n -> Real}
    (model : ClarifiedSourceModel M sampleRate) :
    model.type_prior =
      clarifiedUniformTypePrior n model.seller_type_count_pos := by
  exact model.type_prior_eq_uniform

/--
Author-confirmed clarification: conditional iid rating histories and
cross-seller independence are represented by the explicit finite product state
law.  This is an additional model condition, not a theorem about the printed
`mu_k` recurrence (`adjectivesmodel.tex:67-73`).

Source status: author-confirmed governing clarification, not an archive
recurrence theorem.
-/
theorem author_confirmed_clarified_iid_state_law
    {n m : Nat}
    {M : FiniteRatingLDPModel (Fin n) (Fin (m + 1))}
    {sampleRate : Fin n -> Real}
    (model : ClarifiedSourceModel M sampleRate) (k : Nat) :
    model.stateLaw k = iidFloorSourceStateLaw M sampleRate k := by
  exact model.stateLaw_eq_iidFloorSourceStateLaw k

/--
Source `Lambda` formula (`adjectivesmodel.tex:111-121`).

Source status: retained source formula.
-/
theorem source_definition_log_mgf_formula
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (theta : Seller) (z : Real) :
    sourcePaperLogMGF M theta z =
      Real.log (Finset.univ.sum fun y : Rating =>
        ((M.typeLaw theta) y).toReal * Real.exp (z * M.score y)) := by
  exact ratingLogMGF_eq_finite_formula M theta z

/--
Literal real-valued source `I` display (`adjectivesmodel.tex:111-121`).

Source status: archived legacy display retained only for the checked
zero-versus-positive codomain diagnostic; it is not the governing corrected
rate definition.
-/
theorem source_definition_rate_function_formula
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (theta : Seller) (a : Real) :
    sourcePaperRateFunction M theta a =
      sSup (Set.range fun z : Real =>
        z * a - sourcePaperLogMGF M theta z) := by
  exact ratingRateFunction_eq_finite_formula M theta a

/--
Corrected extended-rate display.  It is needed because an out-of-support
threshold has infinite, not silently real, Legendre cost.

Source status: author-approved corrected codomain for Theorem 1 and the
Appendix rate statements.
-/
theorem source_definition_extended_rate_function_formula
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (theta : Seller) (a : Real) :
    sourcePaperRateFunctionTop M theta a =
      sSup (Set.range fun z : Real =>
        (z * a - sourcePaperLogMGF M theta z : WithTop Real)) := by
  rfl

/--
Source-fidelity diagnostic, not a theorem claim of the paper.  With the
source's `[0,1]` score bound, the literal unrestricted real `inf_a` wrapper
evaluates below the score hull and collapses to zero through `Real.sSup`'s
unbounded-set default.  Under the clarified nontrivial ordinal and positive
sampling conditions, the mathematically intended support-safe rate is instead
strictly positive.  This is why the checked Appendix and Theorem 1 rows use
`WithTop Real` rather than silently coercing the source display to `Real`.

Source status: checked source-fidelity diagnostic, not a literal source
theorem.
-/
theorem source_fidelity_diagnostic_unrestricted_real_pairwise_rate_mismatch
    {n m : Nat}
    [DecidableEq (finiteChainOrderedPair n)]
    (M : FiniteRatingLDPModel (Fin n) (Fin (m + 1)))
    (sampleRate : Fin n -> Real)
    (sourceModel : FiniteOrdinalSourceModel M sampleRate)
    (hpositive_sample : forall theta : Fin n, 0 < sampleRate theta)
    (hm : 1 <= m) (p : finiteChainOrderedPair n) :
    pairwiseSellerThresholdRate M sampleRate
        (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p) = 0 /\
      (0 : WithTop Real) <
        pairwiseSellerThresholdRateTop M sampleRate
          (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p) := by
  exact ⟨source_legacy_real_pairwiseThresholdRate_eq_zero
      M sampleRate sourceModel hpositive_sample p,
    source_pairwiseThresholdRateTop_pos M sampleRate sourceModel
      hpositive_sample (by omega) p⟩

/--
Corrected Appendix `problessthan` theorem for the explicit iid completion.
The finite ordinal source conditions are packaged structurally; positive match
rates and a nontrivial rating scale are visible additional obligations.

Source status: corrected iid and extended-rate result; not derived from the
archive recurrence.
-/
theorem source_appendix_problessthan_score_gap_rate_iid_completion
    {n m : Nat}
    [DecidableEq (finiteChainOrderedPair n)]
    (M : FiniteRatingLDPModel (Fin n) (Fin (m + 1)))
    (sampleRate : Fin n -> Real)
    (sourceModel : FiniteOrdinalSourceModel M sampleRate)
    (hpositive_sample : forall theta : Fin n, 0 < sampleRate theta)
    (hm : 1 <= m) (p : finiteChainOrderedPair n) :
    exists rate : Real,
      pairwiseSellerThresholdRateTop M sampleRate
        (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p) =
          (rate : WithTop Real) /\
        ExponentialRateCertificate
          (fun k => sourceStateScoreGapLeftTailProb
            (iidFloorSourceStateLaw M sampleRate k)
            (iidFloorSourceStateScore M sampleRate k) p)
          rate := by
  let C := ordinalSourcePairwiseLdpCertificate
    M sampleRate sourceModel hpositive_sample hm
  refine ⟨C.rate p, C.threshold_rate_top_eq p, ?_⟩
  have heq : forall k,
      sourceStateScoreGapLeftTailProb (iidFloorSourceStateLaw M sampleRate k)
          (iidFloorSourceStateScore M sampleRate k) p =
        twoSampleFloorScoreGapLeftTailProb M sampleRate
          (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p) k := by
    intro k
    exact source_iid_completion_weak_inversion_bridge M sampleRate p k
  refine { eventually_pos := ?_, has_rate := ?_ }
  · filter_upwards [C.leftTail p |>.eventually_pos] with k hk
    rw [heq k]
    exact hk
  · exact HasExponentialRate.congr_of_forall
      (fun k => (heq k).symm) (C.leftTail p).has_rate

/--
Corrected Appendix `Pk_LD` theorem for the explicit iid completion.  The
constant-factor transfer from weak inversion to `1 - P_k` is checked rather
than assumed from the displayed source rewrite.

Source status: corrected iid and extended-rate result; not derived from the
archive proof transfer.
-/
theorem source_appendix_pk_ld_complement_rate_iid_completion
    {n m : Nat}
    [DecidableEq (finiteChainOrderedPair n)]
    (M : FiniteRatingLDPModel (Fin n) (Fin (m + 1)))
    (sampleRate : Fin n -> Real)
    (sourceModel : FiniteOrdinalSourceModel M sampleRate)
    (hpositive_sample : forall theta : Fin n, 0 < sampleRate theta)
    (hm : 1 <= m) (p : finiteChainOrderedPair n) :
    exists rate : Real,
      pairwiseSellerThresholdRateTop M sampleRate
        (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p) =
          (rate : WithTop Real) /\
        ExponentialRateCertificate
          (fun k => 1 - sourceStatePairwisePk
            (iidFloorSourceStateLaw M sampleRate k)
            (iidFloorSourceStateScore M sampleRate k) p)
          rate := by
  let C := ordinalSourcePairwiseLdpCertificate
    M sampleRate sourceModel hpositive_sample hm
  let E := C.toFloorPkComplementErrorRateCertificate
    M sampleRate finiteChainOrderedPairHi finiteChainOrderedPairLo
  refine ⟨C.rate p, C.threshold_rate_top_eq p, ?_⟩
  have heq : forall k,
      1 - sourceStatePairwisePk (iidFloorSourceStateLaw M sampleRate k)
          (iidFloorSourceStateScore M sampleRate k) p =
        twoSampleFloorPkComplementErrorProb M sampleRate
          (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p) k := by
    intro k
    rw [source_iid_completion_pairwise_objective_bridge]
    exact (twoSampleFloorPkComplementErrorProb_eq_one_sub_pkObjectiveProb
      M sampleRate (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p) k).symm
  refine { eventually_pos := ?_, has_rate := ?_ }
  · filter_upwards [E.has_rate p |>.eventually_pos] with k hk
    rw [heq k]
    exact hk
  · exact HasExponentialRate.congr_of_forall
      (fun k => (heq k).symm) (E.has_rate p).has_rate

/--
The literal source claim `P_k -> 1`, proved for the explicit iid completion
from the positive rate established by strict ordinal tails and strict scores.

Source status: corrected iid-completion convergence result.
-/
theorem source_pairwise_objective_tendsto_one_iid_completion
    {n m : Nat}
    [DecidableEq (finiteChainOrderedPair n)]
    (M : FiniteRatingLDPModel (Fin n) (Fin (m + 1)))
    (sampleRate : Fin n -> Real)
    (sourceModel : FiniteOrdinalSourceModel M sampleRate)
    (hpositive_sample : forall theta : Fin n, 0 < sampleRate theta)
    (hm : 1 <= m) (p : finiteChainOrderedPair n) :
    Tendsto (fun k => sourceStatePairwisePk
      (iidFloorSourceStateLaw M sampleRate k)
      (iidFloorSourceStateScore M sampleRate k) p)
      atTop (nhds 1) := by
  let C := ordinalSourcePairwiseLdpCertificate
    M sampleRate sourceModel hpositive_sample hm
  let E := C.toFloorPkComplementErrorRateCertificate
    M sampleRate finiteChainOrderedPairHi finiteChainOrderedPairLo
  have hrate_top : (0 : WithTop Real) <
      pairwiseSellerThresholdRateTop M sampleRate
        (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p) :=
    source_pairwiseThresholdRateTop_pos M sampleRate sourceModel
      hpositive_sample (by omega) p
  rw [C.threshold_rate_top_eq p] at hrate_top
  have hrate : 0 < C.rate p := by
    exact_mod_cast hrate_top
  have heq : forall k,
      1 - sourceStatePairwisePk (iidFloorSourceStateLaw M sampleRate k)
          (iidFloorSourceStateScore M sampleRate k) p =
        twoSampleFloorPkComplementErrorProb M sampleRate
          (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p) k := by
    intro k
    rw [source_iid_completion_pairwise_objective_bridge]
    exact (twoSampleFloorPkComplementErrorProb_eq_one_sub_pkObjectiveProb
      M sampleRate (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p) k).symm
  have hsource_rate : ExponentialRateCertificate
      (fun k => 1 - sourceStatePairwisePk
        (iidFloorSourceStateLaw M sampleRate k)
        (iidFloorSourceStateScore M sampleRate k) p)
      (C.rate p) :=
    { eventually_pos := by
        filter_upwards [E.has_rate p |>.eventually_pos] with k hk
        rw [heq k]
        exact hk
      has_rate := HasExponentialRate.congr_of_forall
        (fun k => (heq k).symm) (E.has_rate p).has_rate }
  exact hsource_rate.tendsto_one_of_one_sub_pos_rate hrate

/--
The source prose `W_k -> 1`, now proved for the explicit iid completion.

Source status: corrected iid-completion convergence result.
-/
theorem source_uniform_ranking_objective_tendsto_one_iid_completion
    {n m : Nat}
    [DecidableEq (finiteChainOrderedPair n)]
    [Nonempty (finiteChainAdjacentIndex n)]
    (M : FiniteRatingLDPModel (Fin n) (Fin (m + 1)))
    (sampleRate : Fin n -> Real)
    (sourceModel : FiniteOrdinalSourceModel M sampleRate)
    (hpositive_sample : forall theta : Fin n, 0 < sampleRate theta)
    (hm : 1 <= m) :
    Tendsto (fun k => sourceStateWk
      (iidFloorSourceStateLaw M sampleRate k)
      (iidFloorSourceStateScore M sampleRate k))
      atTop (nhds 1) := by
  have hn : 2 <= n := by
    obtain ⟨i⟩ := (inferInstance : Nonempty (finiteChainAdjacentIndex n))
    omega
  letI : Nonempty (finiteChainOrderedPair n) := by
    obtain ⟨i⟩ := (inferInstance : Nonempty (finiteChainAdjacentIndex n))
    exact ⟨finiteChainAdjacentPair i⟩
  have hsum : Tendsto
      (fun k => ∑ p : finiteChainOrderedPair n,
        (Fintype.card (finiteChainOrderedPair n) : Real)⁻¹ *
          sourceStatePairwisePk (iidFloorSourceStateLaw M sampleRate k)
            (iidFloorSourceStateScore M sampleRate k) p)
      atTop
      (nhds (∑ p : finiteChainOrderedPair n,
        (Fintype.card (finiteChainOrderedPair n) : Real)⁻¹ * (1 : Real))) := by
    refine tendsto_finset_sum Finset.univ fun p _ => ?_
    exact Tendsto.const_mul _
      (source_pairwise_objective_tendsto_one_iid_completion
        M sampleRate sourceModel hpositive_sample hm p)
  have hlimit :
      (∑ p : finiteChainOrderedPair n,
        (Fintype.card (finiteChainOrderedPair n) : Real)⁻¹ * (1 : Real)) = 1 := by
    simpa [uniformPairWeight] using
      (uniformPairWeight_sum_eq_one (finiteChainOrderedPair n))
  have heq : (fun k => sourceStateWk
      (iidFloorSourceStateLaw M sampleRate k)
      (iidFloorSourceStateScore M sampleRate k)) =
      (fun k => sourceStateUniformWk
        (iidFloorSourceStateLaw M sampleRate k)
        (iidFloorSourceStateScore M sampleRate k)) := by
    funext k
    exact sourceStateWk_eq_sourceStateUniformWk _ _ hn
  rw [heq]
  simpa [sourceStateUniformWk, hlimit] using hsum

/--
Corrected Theorem 1 for the explicit iid completion.  It retains the actual
finite ordinal source primitives but exposes the needed positive-match-rate,
nontrivial-scale, iid, and extended-rate repairs.

Source status: corrected iid and extended-rate theorem; the literal source
theorem remains an archival delta.
-/
theorem source_theorem1_informative_rating_system_rate_iid_completion
    {n m : Nat}
    [DecidableEq (finiteChainOrderedPair n)]
    [Nonempty (finiteChainAdjacentIndex n)]
    (M : FiniteRatingLDPModel (Fin n) (Fin (m + 1)))
    (sampleRate : Fin n -> Real)
    (sourceModel : FiniteOrdinalSourceModel M sampleRate)
    (hpositive_sample : forall theta : Fin n, 0 < sampleRate theta)
    (hm : 1 <= m) :
    HasExtendedExponentialRate
      (fun k : Nat =>
        1 - finiteUniformFloorPkObjective M sampleRate
          finiteChainOrderedPairHi finiteChainOrderedPairLo k)
      (minFiniteChainAdjacentThresholdRateTop M sampleRate) := by
  exact
    finiteChainUniformFloorPkObjective_oneSub_hasExtendedExponentialRate_of_ordinal_source_model
      M sampleRate sourceModel hpositive_sample hm

/--
Corrected Theorem 1 under the author-confirmed finite iid source-model
clarification.  The theorem is stated over the literal state-level `W_k`; the
record visibly supplies at least two seller types, the uniform prior,
`0 < g(theta) <= 1`, a nontrivial scale, ordinal source primitives, and the
iid state-law completion.  Its rate is support-safe and extended-valued.

Source status: author-approved corrected governing model, recorded in
`docs/GOVERNING_CORRECTED_MODEL_2026-07-24.md`; it does not claim to derive the
archived `mu_k` recurrence.
-/
theorem author_confirmed_clarified_model_theorem1_state_rate
    {n m : Nat}
    [DecidableEq (finiteChainOrderedPair n)]
    {M : FiniteRatingLDPModel (Fin n) (Fin (m + 1))}
    {sampleRate : Fin n -> Real}
    (model : ClarifiedSourceModel M sampleRate) :
    HasExtendedExponentialRate
      (fun k : Nat =>
        1 - sourceStateWk (model.stateLaw k)
          (iidFloorSourceStateScore M sampleRate k))
      model.correctedTheorem1Rate := by
  exact model.sourceStateWk_oneSub_hasExtendedExponentialRate

/--
The author-approved corrected Theorem 1 has an ordinary finite real exponent:
the support-safe extended rate is finite under the corrected finite ordinal
model, and the displayed limit is the paper's `r` equation.

Source status: author-approved corrected governing model. The rate is a finite
representative of the extended rate, not the archived unrestricted `Real`
Legendre infimum.
-/
theorem author_approved_corrected_model_theorem1_finite_real_rate
    {n m : Nat}
    [DecidableEq (finiteChainOrderedPair n)]
    {M : FiniteRatingLDPModel (Fin n) (Fin (m + 1))}
    {sampleRate : Fin n -> Real}
    (model : ClarifiedSourceModel M sampleRate) :
    exists rate : Real,
      model.correctedTheorem1Rate = (rate : WithTop Real) /\
      HasExponentialRate
        (fun k : Nat =>
          1 - sourceStateWk (model.stateLaw k)
            (iidFloorSourceStateScore M sampleRate k))
        rate := by
  exact model.sourceStateWk_oneSub_hasExponentialRate_with_finite_rate

end
end GJ18InformativeRatingSystems.ProofBridge
