import GJ18InformativeRatingSystems.SourceModelBridge

/-!
# Finite Source-State Completion: GJ18 Informative Rating Systems

The paper introduces a joint system state `mu_k(Theta, X)` and defines its
pairwise `P_k` and aggregate `W_k` from that state.  Its displayed recurrence
does not itself establish a finite product law for the rating histories.  This
module therefore keeps the two layers separate:

* `sourceStatePairwisePk` and `sourceStateWk` are literal finite-state
  readings of the displayed `P_k` and `W_k` formulas; and
* the independent floor-rating completion is an explicit, separately defined
  state law whose pairwise `P_k` is proved equal to the existing floor-count
  objective.

The state carrier is intentionally abstract but finite.  This represents a
finite support of aggregate-score configurations without incorrectly requiring
the ambient real score-vector type itself to be finite.
-/

namespace GJ18InformativeRatingSystems

noncomputable section

open scoped BigOperators
open AppliedModelingLib.Probability

/--
Literal finite-state version of the source's pairwise objective `P_k`.

The finite seller chain fixes the two seller types represented by `p`; `mu`
is the state law and `score` extracts every seller's current aggregate score
from a state.  The two events are strict exactly as in equation (8) of the
source.
-/
def sourceStatePairwisePk
    {n : Nat} {Omega : Type*} [Fintype Omega] [DecidableEq Omega]
    (mu : PMF Omega) (score : Omega -> Fin n -> Real)
    (p : finiteChainOrderedPair n) : Real :=
  AppliedModelingLib.pmfProb mu
      (fun omega => score omega (finiteChainOrderedPairHi p) >
        score omega (finiteChainOrderedPairLo p)) -
    AppliedModelingLib.pmfProb mu
      (fun omega => score omega (finiteChainOrderedPairHi p) <
        score omega (finiteChainOrderedPairLo p))

/--
Literal finite-state version of the non-strict comparison event in Appendix
Lemma `problessthan`.  This remains a state-level quantity until a separate
state-evolution completion identifies its law.
-/
def sourceStateScoreGapLeftTailProb
    {n : Nat} {Omega : Type*} [Fintype Omega] [DecidableEq Omega]
    (mu : PMF Omega) (score : Omega -> Fin n -> Real)
    (p : finiteChainOrderedPair n) : Real :=
  AppliedModelingLib.pmfProb mu
    (fun omega => score omega (finiteChainOrderedPairHi p) <=
      score omega (finiteChainOrderedPairLo p))

/--
Literal finite-chain version of the source's Kendall-style objective `W_k`.
The coefficient is the displayed `2 / (M (M - 1))`, and the summation carrier
is exactly the strict ordered comparison-pair carrier.
-/
def sourceStateWk
    {n : Nat} {Omega : Type*} [Fintype Omega] [DecidableEq Omega]
    (mu : PMF Omega) (score : Omega -> Fin n -> Real) : Real :=
  (2 : Real) / ((n : Real) * ((n : Real) - 1)) *
    ∑ p : finiteChainOrderedPair n, sourceStatePairwisePk mu score p

/-- The same finite state objective written with the exact uniform pair carrier. -/
def sourceStateUniformWk
    {n : Nat} {Omega : Type*} [Fintype Omega] [DecidableEq Omega]
    (mu : PMF Omega) (score : Omega -> Fin n -> Real) : Real :=
  ∑ p : finiteChainOrderedPair n,
    (Fintype.card (finiteChainOrderedPair n) : Real)⁻¹ *
      sourceStatePairwisePk mu score p

/--
The strict ordered-pair carrier is equivalent to choosing a high index and a
strictly lower index.  This makes the source's `M (M - 1) / 2` pair count
available as a checked finite-cardinality fact.
-/
def finiteChainOrderedPairEquivSigma (n : Nat) :
    finiteChainOrderedPair n ≃ Sigma (fun hi : Fin n => Fin hi.val) where
  toFun p :=
    ⟨finiteChainOrderedPairHi p,
      ⟨(finiteChainOrderedPairLo p).val, by simpa using p.2⟩⟩
  invFun q :=
    ⟨(q.1, ⟨q.2.val, Nat.lt_trans q.2.isLt q.1.isLt⟩), q.2.isLt⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · simp [finiteChainOrderedPairHi]
    · simp [finiteChainOrderedPairLo]
  right_inv q := by
    cases q
    rfl

/-- Exact cardinality of the paper's strict ordered comparison-pair carrier. -/
theorem finiteChainOrderedPair_card (n : Nat) :
    Fintype.card (finiteChainOrderedPair n) = n * (n - 1) / 2 := by
  rw [Fintype.card_congr (finiteChainOrderedPairEquivSigma n),
    Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Finset.sum_fin_eq_sum_range]
  calc
    (∑ x ∈ Finset.range n, if h : x < n then x else 0) =
        ∑ x ∈ Finset.range n, x := by
      apply Finset.sum_congr rfl
      intro x hx
      simp [Finset.mem_range.mp hx]
    _ = n * (n - 1) / 2 := Finset.sum_range_id n

/-- The source's displayed normalization is the exact uniform-pair weight. -/
theorem sourceState_pair_weight_eq_uniform_pair_weight {n : Nat} (hn : 2 <= n) :
    (2 : Real) / ((n : Real) * ((n : Real) - 1)) =
      (Fintype.card (finiteChainOrderedPair n) : Real)⁻¹ := by
  have hn1 : 1 <= n := by omega
  have hprod_pos : 0 < n * (n - 1) := by
    apply Nat.mul_pos
    · omega
    · omega
  have htwo_dvd : 2 ∣ n * (n - 1) := by
    exact (Nat.even_mul_pred_self n).two_dvd
  have hcard_nat := finiteChainOrderedPair_card n
  have hcard :
      (Fintype.card (finiteChainOrderedPair n) : Real) =
        ((n : Real) * ((n : Real) - 1)) / 2 := by
    rw [hcard_nat, Nat.cast_div htwo_dvd (by norm_num)]
    norm_num [Nat.cast_mul, Nat.cast_sub hn1]
  rw [hcard]
  have hden : (n : Real) * ((n : Real) - 1) ≠ 0 := by
    have hnreal : (1 : Real) < n := by exact_mod_cast hn
    exact ne_of_gt (mul_pos (by linarith) (by linarith))
  field_simp

/--
For at least two seller types, the source's displayed `W_k` coefficient is
exactly the uniform average over `finiteChainOrderedPair n`.
-/
theorem sourceStateWk_eq_sourceStateUniformWk
    {n : Nat} {Omega : Type*} [Fintype Omega] [DecidableEq Omega]
    (mu : PMF Omega) (score : Omega -> Fin n -> Real) (hn : 2 <= n) :
    sourceStateWk mu score = sourceStateUniformWk mu score := by
  unfold sourceStateWk sourceStateUniformWk
  rw [sourceState_pair_weight_eq_uniform_pair_weight hn, Finset.mul_sum]

/-- A finite score-state law has the pairwise floor-count marginals required by `P_k`. -/
def sourceStateHasFloorPkMarginals
    {n : Nat} {Rating Omega : Type*} [Fintype Rating] [DecidableEq Rating]
    [Fintype Omega] [DecidableEq Omega]
    (M : FiniteRatingLDPModel (Fin n) Rating) (sampleRate : Fin n -> Real)
    (mu : PMF Omega) (score : Omega -> Fin n -> Real) (k : Nat) : Prop :=
  forall p : finiteChainOrderedPair n,
    sourceStatePairwisePk mu score p =
      twoSampleFloorPkObjectiveProb M sampleRate
        (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p) k

/-- The independent floor-rating completion's finite state carrier. -/
abbrev iidFloorSourceStateCarrier
    {n : Nat} (Rating : Type*) (sampleRate : Fin n -> Real) (k : Nat) :=
  finiteChainJointFloorRatingSample Rating sampleRate k

/-- Scores in the corrected independent floor-rating state completion. -/
def iidFloorSourceStateScore
    {n : Nat} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel (Fin n) Rating) (sampleRate : Fin n -> Real)
    (k : Nat) :
    iidFloorSourceStateCarrier Rating sampleRate k -> Fin n -> Real :=
  fun sample theta => finiteChainJointFloorAverageScore M sampleRate k sample theta

/--
The explicit independent completion of the source state at horizon `k`.
This is an additional model completion, not a consequence of the displayed
source recurrence for `mu_k`.
-/
noncomputable def iidFloorSourceStateLaw
    {n : Nat} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel (Fin n) Rating) (sampleRate : Fin n -> Real)
    (k : Nat) : PMF (iidFloorSourceStateCarrier Rating sampleRate k) :=
  finiteChainJointFloorRatingLaw M sampleRate k

/-!
## Pairwise bridge for the independent completion

The proof below is deliberately a direct product-law calculation.  It does
not appeal to the source recurrence, which has neither an iid assertion nor a
well-typed finite state-law equality establishing this product distribution.
-/

theorem sourceStatePairwisePk_iidFloorCompletion_eq_twoSampleFloorPkObjective
    {n : Nat} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    [DecidableEq (finiteChainOrderedPair n)]
    (M : FiniteRatingLDPModel (Fin n) Rating) (sampleRate : Fin n -> Real)
    (p : finiteChainOrderedPair n) (k : Nat) :
    sourceStatePairwisePk (iidFloorSourceStateLaw M sampleRate k)
        (iidFloorSourceStateScore M sampleRate k) p =
      twoSampleFloorPkObjectiveProb M sampleRate
        (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p) k := by
  classical
  let hi := finiteChainOrderedPairHi p
  let lo := finiteChainOrderedPairLo p
  let nHi := floorSampleCount sampleRate hi k
  let nLo := floorSampleCount sampleRate lo k
  let cHi : Real := ((nHi : Nat) : Real)⁻¹
  let cLo : Real := ((nLo : Nat) : Real)⁻¹
  have hne : hi ≠ lo := by
    intro h
    have hp : lo.val < hi.val := by
      simpa [hi, lo] using p.2
    have hval : hi.val = lo.val := congrArg Fin.val h
    rw [hval] at hp
    exact (Nat.lt_irrefl lo.val) hp
  have hright_marginal :=
    AppliedModelingLib.pmfProb_pmfPi_twoCoord_eq_pmfProd_dependent
      (μ := fun theta : Fin n =>
        AppliedModelingLib.pmfProduct
          (Fin (floorSampleCount sampleRate theta k)) Rating (M.typeLaw theta))
      (i := hi) (j := lo) hne
      (p := fun hiSample loSample =>
        cHi * finiteIidScoreSum M.score hiSample >
          cLo * finiteIidScoreSum M.score loSample)
  have hleft_marginal :=
    AppliedModelingLib.pmfProb_pmfPi_twoCoord_eq_pmfProd_dependent
      (μ := fun theta : Fin n =>
        AppliedModelingLib.pmfProduct
          (Fin (floorSampleCount sampleRate theta k)) Rating (M.typeLaw theta))
      (i := hi) (j := lo) hne
      (p := fun hiSample loSample =>
        cHi * finiteIidScoreSum M.score hiSample <
          cLo * finiteIidScoreSum M.score loSample)
  have hright :
      AppliedModelingLib.pmfProb (iidFloorSourceStateLaw M sampleRate k)
          (fun sample =>
            iidFloorSourceStateScore M sampleRate k sample
                (finiteChainOrderedPairHi p) >
              iidFloorSourceStateScore M sampleRate k sample
                (finiteChainOrderedPairLo p)) =
        twoSampleScoreGapStrictRightProb M hi lo nHi nLo cHi cLo := by
    unfold iidFloorSourceStateLaw iidFloorSourceStateScore
    unfold twoSampleScoreGapStrictRightProb twoSampleRatingLaw
      twoSampleScoreGapSum
    simpa [finiteChainJointFloorRatingLaw, finiteChainJointFloorAverageScore,
      hi, lo, nHi, nLo, cHi, cLo] using hright_marginal
  have hleft :
      AppliedModelingLib.pmfProb (iidFloorSourceStateLaw M sampleRate k)
          (fun sample =>
            iidFloorSourceStateScore M sampleRate k sample
                (finiteChainOrderedPairHi p) <
              iidFloorSourceStateScore M sampleRate k sample
                (finiteChainOrderedPairLo p)) =
        twoSampleScoreGapStrictLeftProb M hi lo nHi nLo cHi cLo := by
    unfold iidFloorSourceStateLaw iidFloorSourceStateScore
    unfold twoSampleScoreGapStrictLeftProb twoSampleRatingLaw
      twoSampleScoreGapSum
    simpa [finiteChainJointFloorRatingLaw, finiteChainJointFloorAverageScore,
      hi, lo, nHi, nLo, cHi, cLo] using hleft_marginal
  unfold sourceStatePairwisePk twoSampleFloorPkObjectiveProb
  simpa [hi, lo, nHi, nLo, cHi, cLo] using congrArg₂ (· - ·) hright hleft

/--
The iid completion's literal source-state non-strict comparison event is the
finite floor-count left-tail probability used by the Appendix rate theorem.
-/
theorem sourceStateScoreGapLeftTailProb_iidFloorCompletion_eq_twoSampleFloorScoreGapLeftTailProb
    {n : Nat} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    [DecidableEq (finiteChainOrderedPair n)]
    (M : FiniteRatingLDPModel (Fin n) Rating) (sampleRate : Fin n -> Real)
    (p : finiteChainOrderedPair n) (k : Nat) :
    sourceStateScoreGapLeftTailProb (iidFloorSourceStateLaw M sampleRate k)
        (iidFloorSourceStateScore M sampleRate k) p =
      twoSampleFloorScoreGapLeftTailProb M sampleRate
        (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p) k := by
  classical
  let hi := finiteChainOrderedPairHi p
  let lo := finiteChainOrderedPairLo p
  let nHi := floorSampleCount sampleRate hi k
  let nLo := floorSampleCount sampleRate lo k
  let cHi : Real := ((nHi : Nat) : Real)⁻¹
  let cLo : Real := ((nLo : Nat) : Real)⁻¹
  have hne : hi ≠ lo := by
    intro h
    have hp : lo.val < hi.val := by
      simpa [hi, lo] using p.2
    have hval : hi.val = lo.val := congrArg Fin.val h
    rw [hval] at hp
    exact (Nat.lt_irrefl lo.val) hp
  have hmarginal :=
    AppliedModelingLib.pmfProb_pmfPi_twoCoord_eq_pmfProd_dependent
      (μ := fun theta : Fin n =>
        AppliedModelingLib.pmfProduct
          (Fin (floorSampleCount sampleRate theta k)) Rating (M.typeLaw theta))
      (i := hi) (j := lo) hne
      (p := fun hiSample loSample =>
        cHi * finiteIidScoreSum M.score hiSample <=
          cLo * finiteIidScoreSum M.score loSample)
  unfold sourceStateScoreGapLeftTailProb iidFloorSourceStateLaw
    iidFloorSourceStateScore
  unfold twoSampleFloorScoreGapLeftTailProb
  dsimp
  unfold twoSampleScoreGapLeftTailProb twoSampleRatingLaw
    twoSampleScoreGapSum
  simpa [finiteChainJointFloorRatingLaw, finiteChainJointFloorAverageScore,
    hi, lo, nHi, nLo, cHi, cLo] using hmarginal

/-- The explicit iid completion satisfies the semantic source-state marginal bridge. -/
theorem iidFloorSourceStateLaw_hasFloorPkMarginals
    {n : Nat} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    [DecidableEq (finiteChainOrderedPair n)]
    (M : FiniteRatingLDPModel (Fin n) Rating) (sampleRate : Fin n -> Real)
    (k : Nat) :
    sourceStateHasFloorPkMarginals M sampleRate
      (iidFloorSourceStateLaw M sampleRate k)
      (iidFloorSourceStateScore M sampleRate k) k := by
  intro p
  exact sourceStatePairwisePk_iidFloorCompletion_eq_twoSampleFloorPkObjective
    M sampleRate p k

/--
The iid completion identifies the paper's literal state-level `W_k` with the
finite uniform floor-count objective.  The `2 <= n` condition is exactly the
nonzero denominator condition in the source normalization.
-/
theorem sourceStateWk_iidFloorCompletion_eq_finiteUniformFloorPkObjective
    {n : Nat} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    [DecidableEq (finiteChainOrderedPair n)]
    (M : FiniteRatingLDPModel (Fin n) Rating) (sampleRate : Fin n -> Real)
    (k : Nat) (hn : 2 <= n) :
    sourceStateWk (iidFloorSourceStateLaw M sampleRate k)
      (iidFloorSourceStateScore M sampleRate k) =
      finiteUniformFloorPkObjective M sampleRate
        finiteChainOrderedPairHi finiteChainOrderedPairLo k := by
  rw [sourceStateWk_eq_sourceStateUniformWk _ _ hn]
  unfold sourceStateUniformWk finiteUniformFloorPkObjective
    finiteFloorPkObjective uniformPairWeight
  apply Finset.sum_congr rfl
  intro p _
  rw [sourceStatePairwisePk_iidFloorCompletion_eq_twoSampleFloorPkObjective]

end
end GJ18InformativeRatingSystems
