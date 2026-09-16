import QX26AgenticDelegation.PaperInterface

/-!
# Proof Interface: Agentic Delegation and the Language Frontier of Software Developers

This file contains exact-type proof endpoints for the transparent propositions
in `PaperInterface.lean`. It is not a human semantic-review surface: one source
claim is reviewed once, against its expanded `...Spec : Prop` declaration.

The five Specs are mathlib-level statements. Proofs use the algebra already
in `MainTheorems.lean` (`Z_mono`, `Z_sub_eq_one_iff`, `cumulativeGap_nonneg`,
`specialist_expansion_of_constant_increment`).
-/

namespace QX26AgenticDelegation

open Finset

/--
Lean proof endpoint for `Proposition1_frontierExpansionSpec`.

This theorem is intentionally outside `PaperInterface.lean`: Lean Meta checks
that it has exactly the transparent Spec type, while source-to-Lean semantic
review compares the raw source bundle only to that Spec.
-/
theorem Proposition1_frontierExpansion :
    Proposition1_frontierExpansionSpec := by
  intro VS VC VD
  constructor
  · simpa [Z] using Z_mono (le_max_left (max VS VC) VD)
  · intro n VS' VC' VD'
    refine sum_le_sum fun k _ => ?_
    simpa [Z] using Z_mono (le_max_left (max (VS' k) (VC' k)) (VD' k))

/--
Lean proof endpoint for `Proposition2_activationBandSpec`.

This theorem is intentionally outside `PaperInterface.lean`: Lean Meta checks
that it has exactly the transparent Spec type, while source-to-Lean semantic
review compares the raw source bundle only to that Spec.
-/
theorem Proposition2_activationBand :
    Proposition2_activationBandSpec := by
  constructor
  · intro T_S gamma s rC h
    have : T_S ≤ T_S - (gamma * s - rC) := by linarith
    exact min_eq_left this
  · intro omega T_D T_S _hlt
    simpa [Z, sub_nonneg, sub_lt_zero] using
      Z_sub_eq_one_iff (omega - T_D) (omega - T_S)

/--
Lean proof endpoint for `Proposition3_dynamicCumulativeSpec`.

This theorem is intentionally outside `PaperInterface.lean`: Lean Meta checks
that it has exactly the transparent Spec type, while source-to-Lean semantic
review compares the raw source bundle only to that Spec.
-/
theorem Proposition3_dynamicCumulative :
    Proposition3_dynamicCumulativeSpec := by
  intro K U p1 p2 s hp
  simpa [cumulativeGap] using cumulativeGap_nonneg (K := K) U p1 p2 hp s

/--
Lean proof endpoint for `Proposition4_specialistHeterogeneitySpec`.

This theorem is intentionally outside `PaperInterface.lean`: Lean Meta checks
that it has exactly the transparent Spec type, while source-to-Lean semantic
review compares the raw source bundle only to that Spec.
-/
theorem Proposition4_specialistHeterogeneity :
    Proposition4_specialistHeterogeneitySpec := by
  intro K U delta p hp
  exact specialist_expansion_of_constant_increment (K := K) U delta p hp

/--
Lean proof endpoint for `Proposition5_repositoryExpansionSpec`.

This theorem is intentionally outside `PaperInterface.lean`: Lean Meta checks
that it has exactly the transparent Spec type, while source-to-Lean semantic
review compares the raw source bundle only to that Spec.
-/
theorem Proposition5_repositoryExpansion :
    Proposition5_repositoryExpansionSpec := by
  intro Repo Lang ell c1 c2 hc Omega Z1 Z2 hZ r hr
  rcases hr with ⟨hcost, hlang⟩
  exact ⟨le_trans (hc r) hcost, hZ (ell r) hlang⟩

end QX26AgenticDelegation
