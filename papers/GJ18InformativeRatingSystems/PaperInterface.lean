import GJ18InformativeRatingSystems.ProofBridge

namespace GJ18InformativeRatingSystems

namespace PaperInterface

open Filter
open AppliedModelingLib.Probability
open GJ18InformativeRatingSystems.ProofBridge
noncomputable section

/-- Source-facing semantic target for `source_definition_floor_sample_count_formula`. -/
def source_definition_floor_sample_count_formulaSpec
    {Seller : Type*} (sampleRate : Seller -> Real) (theta : Seller) (k : Nat) : Prop :=
  floorSampleCount sampleRate theta k =
    Nat.floor ((k : Real) * sampleRate theta)

/-- Source-facing semantic target for `source_definition_aggregate_score_formula`. -/
def source_definition_aggregate_score_formulaSpec
    {n : Nat} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel (Fin n) Rating)
    (sampleRate : Fin n -> Real) (k : Nat)
    (sample : finiteChainJointFloorRatingSample Rating sampleRate k)
    (theta : Fin n) : Prop :=
  finiteChainJointFloorAverageScore M sampleRate k sample theta =
    ((floorSampleCount sampleRate theta k : Nat) : Real)⁻¹ *
      (Finset.univ.sum fun i => M.score (sample theta i))

/-- Source-facing semantic target for `source_definition_pairwise_objective_formula`. -/
def source_definition_pairwise_objective_formulaSpec
    {n : Nat} {Omega : Type*} [Fintype Omega] [DecidableEq Omega]
    (mu : PMF Omega) (score : Omega -> Fin n -> Real)
    (p : finiteChainOrderedPair n) : Prop :=
  sourceStatePairwisePk mu score p =
    AppliedModelingLib.pmfProb mu
      (fun omega => score omega (finiteChainOrderedPairHi p) >
        score omega (finiteChainOrderedPairLo p)) -
      AppliedModelingLib.pmfProb mu
        (fun omega => score omega (finiteChainOrderedPairHi p) <
          score omega (finiteChainOrderedPairLo p))

/-- Source-facing semantic target for `source_definition_uniform_ranking_objective_formula`. -/
def source_definition_uniform_ranking_objective_formulaSpec
    {n : Nat} {Omega : Type*} [Fintype Omega] [DecidableEq Omega]
    (mu : PMF Omega) (score : Omega -> Fin n -> Real) : Prop :=
  sourceStateWk mu score =
    (2 : Real) / ((n : Real) * ((n : Real) - 1)) *
      (Finset.univ.sum fun p : finiteChainOrderedPair n =>
        sourceStatePairwisePk mu score p)

/-- Source-facing semantic target for `source_definition_uniform_ranking_normalization`. -/
def source_definition_uniform_ranking_normalizationSpec
    {n : Nat} {Omega : Type*} [Fintype Omega] [DecidableEq Omega]
    (mu : PMF Omega) (score : Omega -> Fin n -> Real) (hn : 2 <= n) : Prop :=
  sourceStateWk mu score = sourceStateUniformWk mu score

/-- Source-facing semantic target for `source_iid_completion_pairwise_objective_bridge`. -/
def source_iid_completion_pairwise_objective_bridgeSpec
    {n : Nat} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    [DecidableEq (finiteChainOrderedPair n)]
    (M : FiniteRatingLDPModel (Fin n) Rating) (sampleRate : Fin n -> Real)
    (p : finiteChainOrderedPair n) (k : Nat) : Prop :=
  sourceStatePairwisePk (iidFloorSourceStateLaw M sampleRate k)
      (iidFloorSourceStateScore M sampleRate k) p =
    twoSampleFloorPkObjectiveProb M sampleRate
      (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p) k

/-- Source-facing semantic target for `source_iid_completion_weak_inversion_bridge`. -/
def source_iid_completion_weak_inversion_bridgeSpec
    {n : Nat} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    [DecidableEq (finiteChainOrderedPair n)]
    (M : FiniteRatingLDPModel (Fin n) Rating) (sampleRate : Fin n -> Real)
    (p : finiteChainOrderedPair n) (k : Nat) : Prop :=
  sourceStateScoreGapLeftTailProb (iidFloorSourceStateLaw M sampleRate k)
      (iidFloorSourceStateScore M sampleRate k) p =
    twoSampleFloorScoreGapLeftTailProb M sampleRate
      (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p) k

/-- Source-facing semantic target for `source_iid_completion_uniform_ranking_objective_bridge`. -/
def source_iid_completion_uniform_ranking_objective_bridgeSpec
    {n : Nat} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    [DecidableEq (finiteChainOrderedPair n)]
    (M : FiniteRatingLDPModel (Fin n) Rating) (sampleRate : Fin n -> Real)
    (k : Nat) (hn : 2 <= n) : Prop :=
  sourceStateWk (iidFloorSourceStateLaw M sampleRate k)
    (iidFloorSourceStateScore M sampleRate k) =
    finiteUniformFloorPkObjective M sampleRate
      finiteChainOrderedPairHi finiteChainOrderedPairLo k

/-- Source-facing semantic target for `author_confirmed_clarified_uniform_type_prior`. -/
def author_confirmed_clarified_uniform_type_priorSpec
    {n m : Nat}
    {M : FiniteRatingLDPModel (Fin n) (Fin (m + 1))}
    {sampleRate : Fin n -> Real}
    (model : ClarifiedSourceModel M sampleRate) : Prop :=
  model.type_prior =
    clarifiedUniformTypePrior n model.seller_type_count_pos

/-- Source-facing semantic target for `author_confirmed_clarified_iid_state_law`. -/
def author_confirmed_clarified_iid_state_lawSpec
    {n m : Nat}
    {M : FiniteRatingLDPModel (Fin n) (Fin (m + 1))}
    {sampleRate : Fin n -> Real}
    (model : ClarifiedSourceModel M sampleRate) (k : Nat) : Prop :=
  model.stateLaw k = iidFloorSourceStateLaw M sampleRate k

/-- Source-facing semantic target for `source_definition_log_mgf_formula`. -/
def source_definition_log_mgf_formulaSpec
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (theta : Seller) (z : Real) : Prop :=
  sourcePaperLogMGF M theta z =
    Real.log (Finset.univ.sum fun y : Rating =>
      ((M.typeLaw theta) y).toReal * Real.exp (z * M.score y))

/-- Source-facing semantic target for `source_definition_rate_function_formula`. -/
def source_definition_rate_function_formulaSpec
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (theta : Seller) (a : Real) : Prop :=
  sourcePaperRateFunction M theta a =
    sSup (Set.range fun z : Real =>
      z * a - sourcePaperLogMGF M theta z)

/-- Source-facing semantic target for `source_definition_extended_rate_function_formula`. -/
def source_definition_extended_rate_function_formulaSpec
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (theta : Seller) (a : Real) : Prop :=
  sourcePaperRateFunctionTop M theta a =
    sSup (Set.range fun z : Real =>
      (z * a - sourcePaperLogMGF M theta z : WithTop Real))

/-- Source-facing semantic target for `source_appendix_problessthan_score_gap_rate_iid_completion`. -/
def source_appendix_problessthan_score_gap_rate_iid_completionSpec
    {n m : Nat}
    [DecidableEq (finiteChainOrderedPair n)]
    (M : FiniteRatingLDPModel (Fin n) (Fin (m + 1)))
    (sampleRate : Fin n -> Real)
    (sourceModel : FiniteOrdinalSourceModel M sampleRate)
    (hpositive_sample : forall theta : Fin n, 0 < sampleRate theta)
    (hm : 1 <= m) (p : finiteChainOrderedPair n) : Prop :=
  exists rate : Real,
    pairwiseSellerThresholdRateTop M sampleRate
      (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p) =
        (rate : WithTop Real) /\
      ExponentialRateCertificate
        (fun k => sourceStateScoreGapLeftTailProb
          (iidFloorSourceStateLaw M sampleRate k)
          (iidFloorSourceStateScore M sampleRate k) p)
        rate

/-- Source-facing semantic target for `source_appendix_pk_ld_complement_rate_iid_completion`. -/
def source_appendix_pk_ld_complement_rate_iid_completionSpec
    {n m : Nat}
    [DecidableEq (finiteChainOrderedPair n)]
    (M : FiniteRatingLDPModel (Fin n) (Fin (m + 1)))
    (sampleRate : Fin n -> Real)
    (sourceModel : FiniteOrdinalSourceModel M sampleRate)
    (hpositive_sample : forall theta : Fin n, 0 < sampleRate theta)
    (hm : 1 <= m) (p : finiteChainOrderedPair n) : Prop :=
  exists rate : Real,
    pairwiseSellerThresholdRateTop M sampleRate
      (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p) =
        (rate : WithTop Real) /\
      ExponentialRateCertificate
        (fun k => 1 - sourceStatePairwisePk
          (iidFloorSourceStateLaw M sampleRate k)
          (iidFloorSourceStateScore M sampleRate k) p)
        rate

/-- Source-facing semantic target for `source_pairwise_objective_tendsto_one_iid_completion`. -/
def source_pairwise_objective_tendsto_one_iid_completionSpec
    {n m : Nat}
    [DecidableEq (finiteChainOrderedPair n)]
    (M : FiniteRatingLDPModel (Fin n) (Fin (m + 1)))
    (sampleRate : Fin n -> Real)
    (sourceModel : FiniteOrdinalSourceModel M sampleRate)
    (hpositive_sample : forall theta : Fin n, 0 < sampleRate theta)
    (hm : 1 <= m) (p : finiteChainOrderedPair n) : Prop :=
  Tendsto (fun k => sourceStatePairwisePk
    (iidFloorSourceStateLaw M sampleRate k)
    (iidFloorSourceStateScore M sampleRate k) p)
    atTop (nhds 1)

/-- Source-facing semantic target for `source_uniform_ranking_objective_tendsto_one_iid_completion`. -/
def source_uniform_ranking_objective_tendsto_one_iid_completionSpec
    {n m : Nat}
    [DecidableEq (finiteChainOrderedPair n)]
    [Nonempty (finiteChainAdjacentIndex n)]
    (M : FiniteRatingLDPModel (Fin n) (Fin (m + 1)))
    (sampleRate : Fin n -> Real)
    (sourceModel : FiniteOrdinalSourceModel M sampleRate)
    (hpositive_sample : forall theta : Fin n, 0 < sampleRate theta)
    (hm : 1 <= m) : Prop :=
  Tendsto (fun k => sourceStateWk
    (iidFloorSourceStateLaw M sampleRate k)
    (iidFloorSourceStateScore M sampleRate k))
    atTop (nhds 1)

/-- Source-facing semantic target for `author_approved_corrected_model_theorem1_finite_real_rate`. -/
def author_approved_corrected_model_theorem1_finite_real_rateSpec
    {n m : Nat}
    [DecidableEq (finiteChainOrderedPair n)]
    {M : FiniteRatingLDPModel (Fin n) (Fin (m + 1))}
    {sampleRate : Fin n -> Real}
    (model : ClarifiedSourceModel M sampleRate) : Prop :=
  exists rate : Real,
    model.correctedTheorem1Rate = (rate : WithTop Real) /\
    HasExponentialRate
      (fun k : Nat =>
        1 - sourceStateWk (model.stateLaw k)
          (iidFloorSourceStateScore M sampleRate k))
      rate

end

end PaperInterface
end GJ18InformativeRatingSystems
