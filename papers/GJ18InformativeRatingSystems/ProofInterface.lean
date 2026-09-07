import GJ18InformativeRatingSystems.PaperInterface

import GJ18InformativeRatingSystems.ProofBridge



namespace GJ18InformativeRatingSystems

namespace PaperInterface

open Filter
open AppliedModelingLib.Probability
open GJ18InformativeRatingSystems.ProofBridge
noncomputable section

theorem source_definition_floor_sample_count_formula
    {Seller : Type*} (sampleRate : Seller -> Real) (theta : Seller) (k : Nat) : source_definition_floor_sample_count_formulaSpec (Seller := Seller) (sampleRate := sampleRate) (theta := theta) (k := k) := by
  exact GJ18InformativeRatingSystems.ProofBridge.source_definition_floor_sample_count_formula (Seller := Seller) (sampleRate := sampleRate) (theta := theta) (k := k)

theorem source_definition_aggregate_score_formula
    {n : Nat} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel (Fin n) Rating)
    (sampleRate : Fin n -> Real) (k : Nat)
    (sample : finiteChainJointFloorRatingSample Rating sampleRate k)
    (theta : Fin n) : source_definition_aggregate_score_formulaSpec (n := n) (Rating := Rating) (M := M) (sampleRate := sampleRate) (k := k) (sample := sample) (theta := theta) := by
  exact GJ18InformativeRatingSystems.ProofBridge.source_definition_aggregate_score_formula (n := n) (Rating := Rating) (M := M) (sampleRate := sampleRate) (k := k) (sample := sample) (theta := theta)

theorem source_definition_pairwise_objective_formula
    {n : Nat} {Omega : Type*} [Fintype Omega] [DecidableEq Omega]
    (mu : PMF Omega) (score : Omega -> Fin n -> Real)
    (p : finiteChainOrderedPair n) : source_definition_pairwise_objective_formulaSpec (n := n) (Omega := Omega) (mu := mu) (score := score) (p := p) := by
  exact GJ18InformativeRatingSystems.ProofBridge.source_definition_pairwise_objective_formula (n := n) (Omega := Omega) (mu := mu) (score := score) (p := p)

theorem source_definition_uniform_ranking_objective_formula
    {n : Nat} {Omega : Type*} [Fintype Omega] [DecidableEq Omega]
    (mu : PMF Omega) (score : Omega -> Fin n -> Real) : source_definition_uniform_ranking_objective_formulaSpec (n := n) (Omega := Omega) (mu := mu) (score := score) := by
  exact GJ18InformativeRatingSystems.ProofBridge.source_definition_uniform_ranking_objective_formula (n := n) (Omega := Omega) (mu := mu) (score := score)

theorem source_definition_uniform_ranking_normalization
    {n : Nat} {Omega : Type*} [Fintype Omega] [DecidableEq Omega]
    (mu : PMF Omega) (score : Omega -> Fin n -> Real) (hn : 2 <= n) : source_definition_uniform_ranking_normalizationSpec (n := n) (Omega := Omega) (mu := mu) (score := score) (hn := hn) := by
  exact GJ18InformativeRatingSystems.ProofBridge.source_definition_uniform_ranking_normalization (n := n) (Omega := Omega) (mu := mu) (score := score) (hn := hn)

theorem source_iid_completion_pairwise_objective_bridge
    {n : Nat} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    [DecidableEq (finiteChainOrderedPair n)]
    (M : FiniteRatingLDPModel (Fin n) Rating) (sampleRate : Fin n -> Real)
    (p : finiteChainOrderedPair n) (k : Nat) : source_iid_completion_pairwise_objective_bridgeSpec (n := n) (Rating := Rating) (M := M) (sampleRate := sampleRate) (p := p) (k := k) := by
  exact GJ18InformativeRatingSystems.ProofBridge.source_iid_completion_pairwise_objective_bridge (n := n) (Rating := Rating) (M := M) (sampleRate := sampleRate) (p := p) (k := k)

theorem source_iid_completion_weak_inversion_bridge
    {n : Nat} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    [DecidableEq (finiteChainOrderedPair n)]
    (M : FiniteRatingLDPModel (Fin n) Rating) (sampleRate : Fin n -> Real)
    (p : finiteChainOrderedPair n) (k : Nat) : source_iid_completion_weak_inversion_bridgeSpec (n := n) (Rating := Rating) (M := M) (sampleRate := sampleRate) (p := p) (k := k) := by
  exact GJ18InformativeRatingSystems.ProofBridge.source_iid_completion_weak_inversion_bridge (n := n) (Rating := Rating) (M := M) (sampleRate := sampleRate) (p := p) (k := k)

theorem source_iid_completion_uniform_ranking_objective_bridge
    {n : Nat} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    [DecidableEq (finiteChainOrderedPair n)]
    (M : FiniteRatingLDPModel (Fin n) Rating) (sampleRate : Fin n -> Real)
    (k : Nat) (hn : 2 <= n) : source_iid_completion_uniform_ranking_objective_bridgeSpec (n := n) (Rating := Rating) (M := M) (sampleRate := sampleRate) (k := k) (hn := hn) := by
  exact GJ18InformativeRatingSystems.ProofBridge.source_iid_completion_uniform_ranking_objective_bridge (n := n) (Rating := Rating) (M := M) (sampleRate := sampleRate) (k := k) (hn := hn)

theorem author_confirmed_clarified_uniform_type_prior
    {n m : Nat}
    {M : FiniteRatingLDPModel (Fin n) (Fin (m + 1))}
    {sampleRate : Fin n -> Real}
    (model : ClarifiedSourceModel M sampleRate) : author_confirmed_clarified_uniform_type_priorSpec (n := n) (m := m) (M := M) (sampleRate := sampleRate) (model := model) := by
  exact GJ18InformativeRatingSystems.ProofBridge.author_confirmed_clarified_uniform_type_prior (n := n) (m := m) (M := M) (sampleRate := sampleRate) (model := model)

theorem author_confirmed_clarified_iid_state_law
    {n m : Nat}
    {M : FiniteRatingLDPModel (Fin n) (Fin (m + 1))}
    {sampleRate : Fin n -> Real}
    (model : ClarifiedSourceModel M sampleRate) (k : Nat) : author_confirmed_clarified_iid_state_lawSpec (n := n) (m := m) (M := M) (sampleRate := sampleRate) (model := model) (k := k) := by
  exact GJ18InformativeRatingSystems.ProofBridge.author_confirmed_clarified_iid_state_law (n := n) (m := m) (M := M) (sampleRate := sampleRate) (model := model) (k := k)

theorem source_definition_log_mgf_formula
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (theta : Seller) (z : Real) : source_definition_log_mgf_formulaSpec (Seller := Seller) (Rating := Rating) (M := M) (theta := theta) (z := z) := by
  exact GJ18InformativeRatingSystems.ProofBridge.source_definition_log_mgf_formula (Seller := Seller) (Rating := Rating) (M := M) (theta := theta) (z := z)

theorem source_definition_rate_function_formula
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (theta : Seller) (a : Real) : source_definition_rate_function_formulaSpec (Seller := Seller) (Rating := Rating) (M := M) (theta := theta) (a := a) := by
  exact GJ18InformativeRatingSystems.ProofBridge.source_definition_rate_function_formula (Seller := Seller) (Rating := Rating) (M := M) (theta := theta) (a := a)

theorem source_definition_extended_rate_function_formula
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (theta : Seller) (a : Real) : source_definition_extended_rate_function_formulaSpec (Seller := Seller) (Rating := Rating) (M := M) (theta := theta) (a := a) := by
  exact GJ18InformativeRatingSystems.ProofBridge.source_definition_extended_rate_function_formula (Seller := Seller) (Rating := Rating) (M := M) (theta := theta) (a := a)

theorem source_appendix_problessthan_score_gap_rate_iid_completion
    {n m : Nat}
    [DecidableEq (finiteChainOrderedPair n)]
    (M : FiniteRatingLDPModel (Fin n) (Fin (m + 1)))
    (sampleRate : Fin n -> Real)
    (sourceModel : FiniteOrdinalSourceModel M sampleRate)
    (hpositive_sample : forall theta : Fin n, 0 < sampleRate theta)
    (hm : 1 <= m) (p : finiteChainOrderedPair n) : source_appendix_problessthan_score_gap_rate_iid_completionSpec (n := n) (m := m) (M := M) (sampleRate := sampleRate) (sourceModel := sourceModel) (hpositive_sample := hpositive_sample) (hm := hm) (p := p) := by
  exact GJ18InformativeRatingSystems.ProofBridge.source_appendix_problessthan_score_gap_rate_iid_completion (n := n) (m := m) (M := M) (sampleRate := sampleRate) (sourceModel := sourceModel) (hpositive_sample := hpositive_sample) (hm := hm) (p := p)

theorem source_appendix_pk_ld_complement_rate_iid_completion
    {n m : Nat}
    [DecidableEq (finiteChainOrderedPair n)]
    (M : FiniteRatingLDPModel (Fin n) (Fin (m + 1)))
    (sampleRate : Fin n -> Real)
    (sourceModel : FiniteOrdinalSourceModel M sampleRate)
    (hpositive_sample : forall theta : Fin n, 0 < sampleRate theta)
    (hm : 1 <= m) (p : finiteChainOrderedPair n) : source_appendix_pk_ld_complement_rate_iid_completionSpec (n := n) (m := m) (M := M) (sampleRate := sampleRate) (sourceModel := sourceModel) (hpositive_sample := hpositive_sample) (hm := hm) (p := p) := by
  exact GJ18InformativeRatingSystems.ProofBridge.source_appendix_pk_ld_complement_rate_iid_completion (n := n) (m := m) (M := M) (sampleRate := sampleRate) (sourceModel := sourceModel) (hpositive_sample := hpositive_sample) (hm := hm) (p := p)

theorem source_pairwise_objective_tendsto_one_iid_completion
    {n m : Nat}
    [DecidableEq (finiteChainOrderedPair n)]
    (M : FiniteRatingLDPModel (Fin n) (Fin (m + 1)))
    (sampleRate : Fin n -> Real)
    (sourceModel : FiniteOrdinalSourceModel M sampleRate)
    (hpositive_sample : forall theta : Fin n, 0 < sampleRate theta)
    (hm : 1 <= m) (p : finiteChainOrderedPair n) : source_pairwise_objective_tendsto_one_iid_completionSpec (n := n) (m := m) (M := M) (sampleRate := sampleRate) (sourceModel := sourceModel) (hpositive_sample := hpositive_sample) (hm := hm) (p := p) := by
  exact GJ18InformativeRatingSystems.ProofBridge.source_pairwise_objective_tendsto_one_iid_completion (n := n) (m := m) (M := M) (sampleRate := sampleRate) (sourceModel := sourceModel) (hpositive_sample := hpositive_sample) (hm := hm) (p := p)

theorem source_uniform_ranking_objective_tendsto_one_iid_completion
    {n m : Nat}
    [DecidableEq (finiteChainOrderedPair n)]
    [Nonempty (finiteChainAdjacentIndex n)]
    (M : FiniteRatingLDPModel (Fin n) (Fin (m + 1)))
    (sampleRate : Fin n -> Real)
    (sourceModel : FiniteOrdinalSourceModel M sampleRate)
    (hpositive_sample : forall theta : Fin n, 0 < sampleRate theta)
    (hm : 1 <= m) : source_uniform_ranking_objective_tendsto_one_iid_completionSpec (n := n) (m := m) (M := M) (sampleRate := sampleRate) (sourceModel := sourceModel) (hpositive_sample := hpositive_sample) (hm := hm) := by
  exact GJ18InformativeRatingSystems.ProofBridge.source_uniform_ranking_objective_tendsto_one_iid_completion (n := n) (m := m) (M := M) (sampleRate := sampleRate) (sourceModel := sourceModel) (hpositive_sample := hpositive_sample) (hm := hm)

theorem author_approved_corrected_model_theorem1_finite_real_rate
    {n m : Nat}
    [DecidableEq (finiteChainOrderedPair n)]
    {M : FiniteRatingLDPModel (Fin n) (Fin (m + 1))}
    {sampleRate : Fin n -> Real}
    (model : ClarifiedSourceModel M sampleRate) : author_approved_corrected_model_theorem1_finite_real_rateSpec (n := n) (m := m) (M := M) (sampleRate := sampleRate) (model := model) := by
  exact GJ18InformativeRatingSystems.ProofBridge.author_approved_corrected_model_theorem1_finite_real_rate (n := n) (m := m) (M := M) (sampleRate := sampleRate) (model := model)

end

end PaperInterface
end GJ18InformativeRatingSystems
