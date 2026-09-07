import GJ18InformativeRatingSystems.SourceModelBridge

/-!
# Strict Source-Model Separation: GJ18 Informative Rating Systems

The source prose says that the pairwise comparison probabilities converge to
one.  Before attempting that asymptotic claim, this module records the
strictly weaker but indispensable finite-law fact that the literal strict
ordinal-tail assumptions force a strictly positive expected-score gap for
each ordered seller pair.  The proof is a finite summation-by-parts argument:
strictly positive score increments weight the strict upper-tail gaps.

The nontrivial rating-scale premise is explicit.  On `Fin 1`, the source's
strict-tail predicates have no nonbottom cutoff and cannot imply separation.
-/

namespace GJ18InformativeRatingSystems

noncomputable section

open scoped BigOperators
open AppliedModelingLib.Probability

/-- The increment from ordinal level `k` to `k + 1`, zero outside the range. -/
private noncomputable def sourceOrdinalTailCoeff {m : Nat}
    (score : Fin (m + 1) -> Real) (k : Nat) : Real :=
  if hk : k < m then
    score ⟨k + 1, Nat.succ_lt_succ hk⟩ -
      score ⟨k, Nat.lt_trans hk (Nat.lt_succ_self m)⟩
  else 0

/-- The upper-tail threshold attached to an ordinal increment. -/
private def sourceOrdinalTailThreshold {m : Nat} (k : Nat) : Fin (m + 1) :=
  if hk : k < m then ⟨k + 1, Nat.succ_lt_succ hk⟩ else 0

private theorem sourceOrdinalTailCoeff_of_lt {m : Nat}
    (score : Fin (m + 1) -> Real) {k : Nat} (hk : k < m) :
    sourceOrdinalTailCoeff score k =
      score ⟨k + 1, Nat.succ_lt_succ hk⟩ -
        score ⟨k, Nat.lt_trans hk (Nat.lt_succ_self m)⟩ := by
  simp [sourceOrdinalTailCoeff, hk]

private theorem sourceOrdinalTailThreshold_of_lt {m : Nat} {k : Nat}
    (hk : k < m) :
    sourceOrdinalTailThreshold (m := m) k =
      ⟨k + 1, Nat.succ_lt_succ hk⟩ := by
  simp [sourceOrdinalTailThreshold, hk]

/-- Pointwise ordinal score decomposition into upper-tail indicators. -/
private theorem source_ordinal_tail_score_eq_score_zero_add_sum {m : Nat}
    (score : Fin (m + 1) -> Real) (r : Fin (m + 1)) :
    score r =
      score 0 + ∑ k ∈ Finset.range m,
        if k < r.val then sourceOrdinalTailCoeff score k else 0 := by
  let fNat : Nat -> Real := fun k =>
    if hk : k < m + 1 then score ⟨k, hk⟩ else 0
  have htel := Finset.sum_range_sub fNat r.val
  have hr_le_m : r.val ≤ m := Nat.lt_succ_iff.mp r.isLt
  have hfilter :
      (Finset.range m).filter (fun k => k < r.val) = Finset.range r.val := by
    ext k
    constructor
    · intro hk
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hk).2
    · intro hk
      have hk_lt_r : k < r.val := Finset.mem_range.mp hk
      have hk_lt_m : k < m := Nat.lt_of_lt_of_le hk_lt_r hr_le_m
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk_lt_m, hk_lt_r⟩
  have hsum_filter :
      (∑ k ∈ Finset.range m,
          if k < r.val then sourceOrdinalTailCoeff score k else 0) =
        ∑ k ∈ Finset.range r.val, sourceOrdinalTailCoeff score k := by
    calc
      (∑ k ∈ Finset.range m,
          if k < r.val then sourceOrdinalTailCoeff score k else 0)
          = ∑ k ∈ (Finset.range m).filter (fun k => k < r.val),
              sourceOrdinalTailCoeff score k := by
              rw [Finset.sum_filter]
      _ = ∑ k ∈ Finset.range r.val, sourceOrdinalTailCoeff score k := by
            rw [hfilter]
  have hcoeff_sum :
      (∑ k ∈ Finset.range r.val, sourceOrdinalTailCoeff score k) =
        ∑ k ∈ Finset.range r.val, (fNat (k + 1) - fNat k) := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hk_lt_r : k < r.val := Finset.mem_range.mp hk
    have hk_lt_m : k < m := Nat.lt_of_lt_of_le hk_lt_r hr_le_m
    have hk_succ_lt : k + 1 < m + 1 := Nat.succ_lt_succ hk_lt_m
    have hk_lt_succ : k < m + 1 := Nat.lt_trans hk_lt_m (Nat.lt_succ_self m)
    rw [sourceOrdinalTailCoeff_of_lt score hk_lt_m]
    dsimp [fNat]
    rw [dif_pos hk_succ_lt, dif_pos hk_lt_succ]
  have hr_f : fNat r.val = score r := by
    dsimp [fNat]
    simp [r.isLt]
  have hzero_f : fNat 0 = score 0 := by
    simp [fNat]
  have hsum_eq :
      (∑ k ∈ Finset.range m,
          if k < r.val then sourceOrdinalTailCoeff score k else 0) =
        score r - score 0 := by
    rw [hsum_filter, hcoeff_sum, htel, hr_f, hzero_f]
  linarith

/-- Finite expected ordinal score as a weighted sum of upper-tail masses. -/
private theorem pmfExp_source_ordinal_tail_decomposition {m : Nat}
    (mu : PMF (Fin (m + 1))) (score : Fin (m + 1) -> Real) :
    AppliedModelingLib.pmfExp mu score =
      score 0 + ∑ k ∈ Finset.range m,
        sourceOrdinalTailCoeff score k *
          AppliedModelingLib.pmfProb mu (fun r : Fin (m + 1) =>
            sourceOrdinalTailThreshold (m := m) k ≤ r) := by
  classical
  calc
    AppliedModelingLib.pmfExp mu score =
        AppliedModelingLib.pmfExp mu (fun r : Fin (m + 1) =>
          score 0 + ∑ k ∈ Finset.range m,
            if k < r.val then sourceOrdinalTailCoeff score k else 0) := by
          refine AppliedModelingLib.pmfExp_congr mu ?_
          intro r
          exact source_ordinal_tail_score_eq_score_zero_add_sum score r
    _ = score 0 +
        AppliedModelingLib.pmfExp mu (fun r : Fin (m + 1) =>
          ∑ k ∈ Finset.range m,
            if k < r.val then sourceOrdinalTailCoeff score k else 0) := by
          rw [AppliedModelingLib.pmfExp_add, AppliedModelingLib.pmfExp_const]
    _ = score 0 + ∑ k ∈ Finset.range m,
        AppliedModelingLib.pmfExp mu (fun r : Fin (m + 1) =>
          if k < r.val then sourceOrdinalTailCoeff score k else 0) := by
          rw [AppliedModelingLib.pmfExp_finset_sum]
    _ = score 0 + ∑ k ∈ Finset.range m,
        sourceOrdinalTailCoeff score k *
          AppliedModelingLib.pmfProb mu (fun r : Fin (m + 1) =>
            sourceOrdinalTailThreshold (m := m) k ≤ r) := by
          refine congrArg (fun x => score 0 + x) ?_
          refine Finset.sum_congr rfl ?_
          intro k hk_mem
          have hk : k < m := Finset.mem_range.mp hk_mem
          have hthreshold :
              sourceOrdinalTailThreshold (m := m) k =
                (⟨k + 1, Nat.succ_lt_succ hk⟩ : Fin (m + 1)) :=
            sourceOrdinalTailThreshold_of_lt hk
          calc
            AppliedModelingLib.pmfExp mu (fun r : Fin (m + 1) =>
                if k < r.val then sourceOrdinalTailCoeff score k else 0)
                =
                AppliedModelingLib.pmfExp mu (fun r : Fin (m + 1) =>
                  sourceOrdinalTailCoeff score k *
                    (if sourceOrdinalTailThreshold (m := m) k ≤ r then
                      (1 : Real) else 0)) := by
                  refine AppliedModelingLib.pmfExp_congr mu ?_
                  intro r
                  have hevent :
                      (sourceOrdinalTailThreshold (m := m) k ≤ r) ↔
                        k < r.val := by
                    rw [hthreshold]
                    change k + 1 ≤ r.val ↔ k < r.val
                    exact Nat.succ_le_iff
                  by_cases hkr : k < r.val
                  · have htail : sourceOrdinalTailThreshold (m := m) k ≤ r :=
                      hevent.2 hkr
                    simp [hkr, htail]
                  · have htail : ¬ sourceOrdinalTailThreshold (m := m) k ≤ r :=
                      fun hle => hkr (hevent.1 hle)
                    simp [hkr, htail]
            _ = sourceOrdinalTailCoeff score k *
                AppliedModelingLib.pmfProb mu (fun r : Fin (m + 1) =>
                  sourceOrdinalTailThreshold (m := m) k ≤ r) := by
                  rw [AppliedModelingLib.pmfExp_const_mul]
                  rfl

private theorem sourceOrdinalTailCoeff_nonneg_of_strictMono {m : Nat}
    {score : Fin (m + 1) -> Real} (hstrict : StrictMono score)
    {k : Nat} (hk : k < m) :
    0 ≤ sourceOrdinalTailCoeff score k := by
  rw [sourceOrdinalTailCoeff_of_lt score hk]
  exact sub_nonneg.mpr (hstrict.monotone (Nat.le_succ k))

private theorem sourceOrdinalTailCoeff_zero_pos_of_strictMono {m : Nat}
    {score : Fin (m + 1) -> Real} (hstrict : StrictMono score)
    (hm : 0 < m) :
    0 < sourceOrdinalTailCoeff score 0 := by
  rw [sourceOrdinalTailCoeff_of_lt score hm]
  apply sub_pos.mpr
  apply hstrict
  change 0 < 1
  omega

/--
Literal strict source quality tails, together with a strictly increasing
rating score, yield a strict expected-score gap for every ordered seller pair.
The explicit `0 < m` premise rules out the vacuous one-rating model.
-/
theorem source_strict_expected_score_gap
    {n m : Nat}
    (M : FiniteRatingLDPModel (Fin n) (Fin (m + 1)))
    (sampleRate : Fin n -> Real)
    (sourceModel : FiniteOrdinalSourceModel M sampleRate)
    (hm : 0 < m)
    (p : finiteChainOrderedPair n) :
    AppliedModelingLib.pmfExp (M.typeLaw (finiteChainOrderedPairLo p)) M.score <
      AppliedModelingLib.pmfExp (M.typeLaw (finiteChainOrderedPairHi p)) M.score := by
  classical
  rw [pmfExp_source_ordinal_tail_decomposition,
    pmfExp_source_ordinal_tail_decomposition]
  have hsum :
      (∑ k ∈ Finset.range m,
          sourceOrdinalTailCoeff M.score k *
            AppliedModelingLib.pmfProb (M.typeLaw (finiteChainOrderedPairLo p))
              (fun r : Fin (m + 1) =>
                sourceOrdinalTailThreshold (m := m) k ≤ r)) <
        ∑ k ∈ Finset.range m,
          sourceOrdinalTailCoeff M.score k *
            AppliedModelingLib.pmfProb (M.typeLaw (finiteChainOrderedPairHi p))
              (fun r : Fin (m + 1) =>
                sourceOrdinalTailThreshold (m := m) k ≤ r) := by
    refine Finset.sum_lt_sum ?_ ?_
    · intro k hk_mem
      have hk : k < m := Finset.mem_range.mp hk_mem
      have hcoeff : 0 ≤ sourceOrdinalTailCoeff M.score k :=
        sourceOrdinalTailCoeff_nonneg_of_strictMono
          sourceModel.scores_strictly_increasing hk
      have htail :=
        sourceModel.quality_tails_strictly_increase_above_bottom p
          (sourceOrdinalTailThreshold (m := m) k) (by
            rw [sourceOrdinalTailThreshold_of_lt hk]
            simp)
      unfold sourceOrdinalUpperTail at htail
      exact mul_le_mul_of_nonneg_left
        htail.le
        hcoeff
    · refine ⟨0, Finset.mem_range.mpr hm, ?_⟩
      have htail :
          AppliedModelingLib.pmfProb (M.typeLaw (finiteChainOrderedPairLo p))
              (fun r : Fin (m + 1) =>
                sourceOrdinalTailThreshold (m := m) 0 ≤ r) <
            AppliedModelingLib.pmfProb (M.typeLaw (finiteChainOrderedPairHi p))
              (fun r : Fin (m + 1) =>
                sourceOrdinalTailThreshold (m := m) 0 ≤ r) :=
        by
          have htail :=
            sourceModel.quality_tails_strictly_increase_above_bottom p
              (sourceOrdinalTailThreshold (m := m) 0) (by
                rw [sourceOrdinalTailThreshold_of_lt hm]
                simp)
          unfold sourceOrdinalUpperTail at htail
          exact htail
      exact mul_lt_mul_of_pos_left htail
        (sourceOrdinalTailCoeff_zero_pos_of_strictMono
          sourceModel.scores_strictly_increasing hm)
  simpa [add_comm] using add_lt_add_left hsum (M.score 0)

/-- The strict expected-score gap holds uniformly over the paper's ordered-pair carrier. -/
theorem source_strict_expected_score_gaps
    {n m : Nat}
    (M : FiniteRatingLDPModel (Fin n) (Fin (m + 1)))
    (sampleRate : Fin n -> Real)
    (sourceModel : FiniteOrdinalSourceModel M sampleRate)
    (hm : 0 < m) :
    forall p : finiteChainOrderedPair n,
      AppliedModelingLib.pmfExp (M.typeLaw (finiteChainOrderedPairLo p)) M.score <
        AppliedModelingLib.pmfExp (M.typeLaw (finiteChainOrderedPairHi p)) M.score := by
  intro p
  exact source_strict_expected_score_gap M sampleRate sourceModel hm p

/--
The literal unrestricted real `inf_a` wrapper is not the source's intended
large-deviation rate in a finite score model.  Since the source constrains
scores to `[0,1]`, evaluating its legacy real Legendre API below zero makes
both one-law suprema use `Real.sSup`'s unbounded-set default.  The resulting
real pairwise infimum is therefore zero.

This is a diagnostic theorem about the formal real codomain, not an assertion
that the paper's mathematical exponent is zero; the checked exponent below
uses `WithTop Real` precisely to retain the required infinite off-support
costs.
-/
theorem source_legacy_real_pairwiseThresholdRate_eq_zero
    {n m : Nat}
    (M : FiniteRatingLDPModel (Fin n) (Fin (m + 1)))
    (sampleRate : Fin n -> Real)
    (sourceModel : FiniteOrdinalSourceModel M sampleRate)
    (hpositive_sample : forall theta : Fin n, 0 < sampleRate theta)
    (p : finiteChainOrderedPair n) :
    pairwiseSellerThresholdRate M sampleRate
      (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p) = 0 := by
  exact pairwiseSellerThresholdRate_eq_zero_of_score_lower_bound
    M sampleRate (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p) 0
    (hpositive_sample (finiteChainOrderedPairHi p)).le
    (hpositive_sample (finiteChainOrderedPairLo p)).le
    (fun r => (sourceModel.scores_in_unit_interval r).1)

/--
Every literal nontrivial finite-ordinal source pair has a strictly positive
support-safe threshold exponent when sellers have positive sample rates. This
uses the strict expected-score separation proved above and the generic finite
Fenchel lower bound; it does not add terminal-label full support.
-/
theorem source_pairwiseThresholdRateTop_pos
    {n m : Nat}
    (M : FiniteRatingLDPModel (Fin n) (Fin (m + 1)))
    (sampleRate : Fin n -> Real)
    (sourceModel : FiniteOrdinalSourceModel M sampleRate)
    (hpositive_sample : forall theta : Fin n, 0 < sampleRate theta)
    (hm : 0 < m)
    (p : finiteChainOrderedPair n) :
    (0 : WithTop Real) <
      pairwiseSellerThresholdRateTop M sampleRate
        (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p) :=
  pairwiseSellerThresholdRateTop_pos_of_expected_score_gap
    M sampleRate (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p)
    (hpositive_sample (finiteChainOrderedPairHi p))
    (hpositive_sample (finiteChainOrderedPairLo p))
    (source_strict_expected_score_gap M sampleRate sourceModel hm p)

/--
For every nontrivial clarified source pair, the literal real wrapper cannot
equal the support-safe threshold rate: the former is zero by its `Real.sSup`
default while the latter is strictly positive.  Positive match rates repair
the sampling premise, but cannot repair this codomain mismatch.
-/
theorem source_legacy_real_pairwiseThresholdRate_ne_support_safe_rate
    {n m : Nat}
    (M : FiniteRatingLDPModel (Fin n) (Fin (m + 1)))
    (sampleRate : Fin n -> Real)
    (sourceModel : FiniteOrdinalSourceModel M sampleRate)
    (hpositive_sample : forall theta : Fin n, 0 < sampleRate theta)
    (hm : 0 < m)
    (p : finiteChainOrderedPair n) :
    pairwiseSellerThresholdRateTop M sampleRate
        (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p) ≠
      (pairwiseSellerThresholdRate M sampleRate
        (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p) : WithTop Real) := by
  intro heq
  have hpositive := source_pairwiseThresholdRateTop_pos
    M sampleRate sourceModel hpositive_sample hm p
  have hlegacy := source_legacy_real_pairwiseThresholdRate_eq_zero
    M sampleRate sourceModel hpositive_sample p
  rw [hlegacy] at heq
  rw [heq] at hpositive
  exact (lt_irrefl _ hpositive)

/-- The positive source threshold exponent holds uniformly over the ordered-pair carrier. -/
theorem source_pairwiseThresholdRateTop_pos_all
    {n m : Nat}
    (M : FiniteRatingLDPModel (Fin n) (Fin (m + 1)))
    (sampleRate : Fin n -> Real)
    (sourceModel : FiniteOrdinalSourceModel M sampleRate)
    (hpositive_sample : forall theta : Fin n, 0 < sampleRate theta)
    (hm : 0 < m) :
    forall p : finiteChainOrderedPair n,
      (0 : WithTop Real) <
        pairwiseSellerThresholdRateTop M sampleRate
          (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p) := by
  intro p
  exact source_pairwiseThresholdRateTop_pos
    M sampleRate sourceModel hpositive_sample hm p

/--
Binary boundary subfamily: when the lower seller has no terminal-rating mass,
the support-safe pairwise threshold rate is strictly positive.  The terminal
zero premise is deliberately an additional restriction, not a consequence of
the literal GJ18 source-tail contract.
-/
theorem source_binary_pairwiseThresholdRateTop_pos_of_low_terminal_mass_zero
    {n : Nat}
    (M : FiniteRatingLDPModel (Fin n) (Fin 2))
    (sampleRate : Fin n -> Real)
    (sourceModel : FiniteOrdinalSourceModel M sampleRate)
    (hpositive_sample : forall theta : Fin n, 0 < sampleRate theta)
    (p : finiteChainOrderedPair n)
    (hlow_terminal_zero :
      (M.typeLaw (finiteChainOrderedPairLo p) (Fin.last 1)).toReal = 0) :
    (0 : WithTop Real) <
      M.pairwiseThresholdRateTop sampleRate
        (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p) := by
  let hi := finiteChainOrderedPairHi p
  let lo := finiteChainOrderedPairLo p
  have hrating : forall r : Fin 2, r = 0 ∨ r = Fin.last 1 := by
    intro r
    fin_cases r <;> simp
  have hscore_lt : M.score (0 : Fin 2) < M.score (Fin.last 1) := by
    apply sourceModel.scores_strictly_increasing
    decide
  have hhi_bottom : 0 < (M.typeLaw hi (0 : Fin 2)).toReal := by
    let r : Fin 1 := 0
    have hmass :=
      mass_pos_of_source_strict_ordinal_cumulative_tail_decrease_at_displayed_cutoffs
        M sourceModel.tails_strictly_decrease_at_displayed_cutoffs hi r
    simpa [hi, r] using hmass
  have hhi_top : 0 < (M.typeLaw hi (Fin.last 1)).toReal := by
    have hmass :=
      mass_pos_last_of_source_strict_ordinal_quality_tail_increase_above_bottom
        M sourceModel.quality_tails_strictly_increase_above_bottom p (by omega)
    simpa [hi] using hmass
  have hrate_pos : 0 < sampleRate hi *
      (-Real.log (AppliedModelingLib.pmfProb (M.typeLaw hi)
        (fun r => M.score r = M.score (0 : Fin 2)))) :=
    binaryBottomTopBoundaryRate_pos
      M sampleRate hi (0 : Fin 2) (Fin.last 1)
      (hpositive_sample hi) hscore_lt hhi_bottom hhi_top
  have hrate_eq :
      M.pairwiseThresholdRateTop sampleRate hi lo =
        (sampleRate hi *
          (-Real.log (AppliedModelingLib.pmfProb (M.typeLaw hi)
            (fun r => M.score r = M.score (0 : Fin 2))) : WithTop Real)) :=
    pairwiseSellerThresholdRateTop_eq_binary_bottom_top_boundary
      M sampleRate hi lo (0 : Fin 2) (Fin.last 1)
      (hpositive_sample hi) (hpositive_sample lo) hrating hscore_lt
      hhi_bottom (by simpa [lo] using hlow_terminal_zero)
  rw [show finiteChainOrderedPairHi p = hi by rfl,
    show finiteChainOrderedPairLo p = lo by rfl, hrate_eq]
  exact_mod_cast hrate_pos

end
end GJ18InformativeRatingSystems
