import GJ18InformativeRatingSystems.SourceStateCompletion

/-!
# Author-Confirmed Clarified Model: GJ18 Informative Rating Systems

This module records the author-confirmed completion used to close the
finite-model proof obligation.  It is intentionally separate from the
literal source-state recurrence:

* seller types are the finite ordered carrier `Fin n`, with an explicit
  uniform prior and at least two types;
* every match rate satisfies `0 < g(theta) <= 1`;
* the ordinal rating carrier has at least two displayed levels; and
* conditional on seller type, rating draws are iid with law `M.typeLaw theta`,
  independently across seller histories.  The last point is stated as an
  equality to the finite product state law, rather than inferred from the
  paper's displayed recurrence.

No terminal full-support condition is included here.
-/

namespace GJ18InformativeRatingSystems

noncomputable section

open AppliedModelingLib.Probability

/-- The explicit uniform prior on a nonempty finite ordered seller carrier. -/
noncomputable def clarifiedUniformTypePrior (n : Nat) (hn : 0 < n) : PMF (Fin n) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact AppliedModelingLib.uniformPMF (Fin n)

/-- The author-confirmed positive, at-most-one-per-period rate condition. -/
abbrev clarifiedMatchRateBounds {n : Nat} (sampleRate : Fin n -> Real) : Prop :=
  forall theta : Fin n, 0 < sampleRate theta /\ sampleRate theta <= 1

/-- The author-confirmed requirement of at least two displayed rating levels. -/
abbrev clarifiedNontrivialRatingScale (m : Nat) : Prop :=
  1 <= m

/--
Author-confirmed completion of the finite GJ18 model.

The equality in `conditional_iid_ratings_and_independent_seller_histories` is
the semantic content of the IID assertion: `iidFloorSourceStateLaw` is the
product over seller types and, for each seller, the product of its
`M.typeLaw theta` rating draws.  It is not a theorem about the source's
literal `mu_k` recurrence.
-/
structure ClarifiedSourceModel
    {n m : Nat}
    (M : FiniteRatingLDPModel (Fin n) (Fin (m + 1)))
    (sampleRate : Fin n -> Real) where
  seller_type_count_pos : 0 < n
  at_least_two_seller_types : 2 <= n
  type_prior : PMF (Fin n)
  type_prior_uniform :
    type_prior = clarifiedUniformTypePrior n seller_type_count_pos
  match_rate_bounds : clarifiedMatchRateBounds sampleRate
  nontrivial_rating_scale : clarifiedNontrivialRatingScale m
  ordinal_source_model : FiniteOrdinalSourceModel M sampleRate
  stateLaw : (k : Nat) ->
    PMF (iidFloorSourceStateCarrier (Fin (m + 1)) sampleRate k)
  conditional_iid_ratings_and_independent_seller_histories :
    forall k : Nat, stateLaw k = iidFloorSourceStateLaw M sampleRate k

namespace ClarifiedSourceModel

/-- The recorded prior is the explicit uniform law on the finite type carrier. -/
theorem type_prior_eq_uniform
    {n m : Nat}
    {M : FiniteRatingLDPModel (Fin n) (Fin (m + 1))}
    {sampleRate : Fin n -> Real}
    (model : ClarifiedSourceModel M sampleRate) :
    model.type_prior =
      clarifiedUniformTypePrior n model.seller_type_count_pos :=
  model.type_prior_uniform

/-- The clarified rate bounds supply the positive-rate premise needed by the LDP. -/
theorem positive_match_rates
    {n m : Nat}
    {M : FiniteRatingLDPModel (Fin n) (Fin (m + 1))}
    {sampleRate : Fin n -> Real}
    (model : ClarifiedSourceModel M sampleRate) :
    assumption_positive_match_rates sampleRate := by
  intro theta
  exact (model.match_rate_bounds theta).1

/-- The clarified positive rate condition also supplies the source nonnegativity premise. -/
theorem nonnegative_match_rates
    {n m : Nat}
    {M : FiniteRatingLDPModel (Fin n) (Fin (m + 1))}
    {sampleRate : Fin n -> Real}
    (model : ClarifiedSourceModel M sampleRate) :
    source_nonnegative_match_rates sampleRate := by
  intro theta
  exact (model.match_rate_bounds theta).1.le

/-- The corrected ranking objective has a nonempty carrier of adjacent pairs. -/
theorem adjacent_index_nonempty
    {n m : Nat}
    {M : FiniteRatingLDPModel (Fin n) (Fin (m + 1))}
    {sampleRate : Fin n -> Real}
    (model : ClarifiedSourceModel M sampleRate) :
    Nonempty (finiteChainAdjacentIndex n) := by
  have htwo : 2 <= n := model.at_least_two_seller_types
  have hone : 1 < n := by omega
  exact ⟨⟨⟨0, by omega⟩, by simpa using hone⟩⟩

/--
The author-approved corrected Theorem 1 rate.  Its adjacent-pair carrier is
constructed from the visible `at_least_two_seller_types` model field instead
of appearing as an implicit typeclass premise in the paper theorem.
-/
noncomputable def correctedTheorem1Rate
    {n m : Nat}
    {M : FiniteRatingLDPModel (Fin n) (Fin (m + 1))}
    {sampleRate : Fin n -> Real}
    (model : ClarifiedSourceModel M sampleRate) : WithTop Real := by
  letI : Nonempty (finiteChainAdjacentIndex n) := model.adjacent_index_nonempty
  exact minFiniteChainAdjacentThresholdRateTop M sampleRate

/-- The state-law field is exactly the independent floor-rating completion. -/
theorem stateLaw_eq_iidFloorSourceStateLaw
    {n m : Nat}
    {M : FiniteRatingLDPModel (Fin n) (Fin (m + 1))}
    {sampleRate : Fin n -> Real}
    (model : ClarifiedSourceModel M sampleRate) (k : Nat) :
    model.stateLaw k = iidFloorSourceStateLaw M sampleRate k :=
  model.conditional_iid_ratings_and_independent_seller_histories k

/--
Under the clarified IID completion, the literal finite-state `P_k` has the
existing two-seller floor-sample objective as its exact marginal.
-/
theorem sourceStatePairwisePk_eq_twoSampleFloorPkObjective
    {n m : Nat} [DecidableEq (finiteChainOrderedPair n)]
    {M : FiniteRatingLDPModel (Fin n) (Fin (m + 1))}
    {sampleRate : Fin n -> Real}
    (model : ClarifiedSourceModel M sampleRate)
    (p : finiteChainOrderedPair n) (k : Nat) :
    sourceStatePairwisePk (model.stateLaw k)
        (iidFloorSourceStateScore M sampleRate k) p =
      twoSampleFloorPkObjectiveProb M sampleRate
        (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p) k := by
  rw [model.stateLaw_eq_iidFloorSourceStateLaw k]
  exact sourceStatePairwisePk_iidFloorCompletion_eq_twoSampleFloorPkObjective
    M sampleRate p k

/-- The clarified IID state law satisfies the source-state `P_k` marginal contract. -/
theorem stateLaw_hasFloorPkMarginals
    {n m : Nat} [DecidableEq (finiteChainOrderedPair n)]
    {M : FiniteRatingLDPModel (Fin n) (Fin (m + 1))}
    {sampleRate : Fin n -> Real}
    (model : ClarifiedSourceModel M sampleRate) (k : Nat) :
    sourceStateHasFloorPkMarginals M sampleRate (model.stateLaw k)
      (iidFloorSourceStateScore M sampleRate k) k := by
  rw [model.stateLaw_eq_iidFloorSourceStateLaw k]
  exact iidFloorSourceStateLaw_hasFloorPkMarginals M sampleRate k

/--
Under the clarified IID completion, the literal finite-state `W_k` equals the
existing uniform ordered-pair floor-sample objective.  The explicit `2 <= n`
premise is precisely the nonzero-denominator condition in the source formula.
-/
theorem sourceStateWk_eq_finiteUniformFloorPkObjective
    {n m : Nat} [DecidableEq (finiteChainOrderedPair n)]
    {M : FiniteRatingLDPModel (Fin n) (Fin (m + 1))}
    {sampleRate : Fin n -> Real}
    (model : ClarifiedSourceModel M sampleRate) (k : Nat) (hn : 2 <= n) :
    sourceStateWk (model.stateLaw k)
        (iidFloorSourceStateScore M sampleRate k) =
      finiteUniformFloorPkObjective M sampleRate
        finiteChainOrderedPairHi finiteChainOrderedPairLo k := by
  rw [model.stateLaw_eq_iidFloorSourceStateLaw k]
  exact sourceStateWk_iidFloorCompletion_eq_finiteUniformFloorPkObjective
    M sampleRate k hn

/--
The clarified model gives the corrected, support-safe Theorem 1 rate for the
literal state-level `W_k`.  This theorem relies on the explicit IID field
above; it makes no claim that the source recurrence proves that field.
-/
theorem sourceStateWk_oneSub_hasExtendedExponentialRate
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
  letI : Nonempty (finiteChainAdjacentIndex n) := model.adjacent_index_nonempty
  change HasExtendedExponentialRate
    (fun k : Nat =>
      1 - sourceStateWk (model.stateLaw k)
        (iidFloorSourceStateScore M sampleRate k))
    (minFiniteChainAdjacentThresholdRateTop M sampleRate)
  have hn : 2 <= n := model.at_least_two_seller_types
  have hstate :
      (fun k : Nat =>
        1 - sourceStateWk (model.stateLaw k)
          (iidFloorSourceStateScore M sampleRate k)) =
        (fun k : Nat =>
          1 - finiteUniformFloorPkObjective M sampleRate
            finiteChainOrderedPairHi finiteChainOrderedPairLo k) := by
    funext k
    rw [model.sourceStateWk_eq_finiteUniformFloorPkObjective k hn]
  rw [hstate]
  exact
    finiteChainUniformFloorPkObjective_oneSub_hasExtendedExponentialRate_of_ordinal_source_model
      M sampleRate model.ordinal_source_model model.positive_match_rates
      model.nontrivial_rating_scale

/--
The corrected support-safe adjacent rate is finite in the clarified model, so
the state-level convergence theorem has an ordinary real exponent as well.
This exponent is a representative of the `WithTop` rate; it is not identified
with the pinned source's unrestricted real Legendre infimum.
-/
theorem sourceStateWk_oneSub_hasExponentialRate_with_finite_rate
    {n m : Nat}
    [DecidableEq (finiteChainOrderedPair n)]
    {M : FiniteRatingLDPModel (Fin n) (Fin (m + 1))}
    {sampleRate : Fin n -> Real}
    (model : ClarifiedSourceModel M sampleRate) :
    exists rate : Real,
      model.correctedTheorem1Rate =
        (rate : WithTop Real) /\
      HasExponentialRate
        (fun k : Nat =>
          1 - sourceStateWk (model.stateLaw k)
            (iidFloorSourceStateScore M sampleRate k))
        rate := by
  letI : Nonempty (finiteChainAdjacentIndex n) := model.adjacent_index_nonempty
  change exists rate : Real,
    minFiniteChainAdjacentThresholdRateTop M sampleRate =
      (rate : WithTop Real) /\
    HasExponentialRate
      (fun k : Nat =>
        1 - sourceStateWk (model.stateLaw k)
          (iidFloorSourceStateScore M sampleRate k))
      rate
  obtain ⟨rate, hrate⟩ :=
    source_minFiniteChainAdjacentThresholdRateTop_has_finite_real_representative
      M sampleRate model.ordinal_source_model model.positive_match_rates
      model.nontrivial_rating_scale
  refine ⟨rate, hrate, ?_⟩
  have hext := model.sourceStateWk_oneSub_hasExtendedExponentialRate
  change HasExtendedExponentialRate
    (fun k : Nat =>
      1 - sourceStateWk (model.stateLaw k)
        (iidFloorSourceStateScore M sampleRate k))
    (minFiniteChainAdjacentThresholdRateTop M sampleRate) at hext
  rw [hrate] at hext
  exact HasExtendedExponentialRate.to_finite hext

end ClarifiedSourceModel

end

end GJ18InformativeRatingSystems
