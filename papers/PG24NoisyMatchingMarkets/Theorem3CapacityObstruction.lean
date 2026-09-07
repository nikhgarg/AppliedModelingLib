import PG24NoisyMatchingMarkets.Assumptions

/-!
# Theorem 3 Quantile-Capacity Obstruction

The active pointwise-capacity route for PG24 Theorem 3 deletes
`floor ((epsilon / 2) * (C + 1))` cutoffs and selects a quantile whose strict
upper tail is at most `epsilon / (2 * (C + 1))`.  This file records the
resulting quantitative obstruction without adding any paper assumption.

The source theorem permits every `epsilon > 0` while fixing total supply in
`(0, 1)` (`source_tex/model.tex:10-15, 54-63`).  Its coalition proof instead
uses the two dense-cluster / large-gap cases (`source_tex/proofs-extended.tex:5-17`),
not this quantile-capacity contradiction.  Consequently, this helper is a
guardrail for the current implementation route, not a normalization of a
source theorem statement.
-/

open Filter
open AppliedModelingLib.Matching

namespace PG24NoisyMatchingMarkets

universe u

/--
Elementary union-bound form for identical crossing probabilities.  It is used
only to audit the quantitative strength of the current split-power route.
-/
theorem one_sub_pow_le_natCast_mul
    {p : ℝ} (hp_nonneg : 0 ≤ p) (hp_le_one : p ≤ 1) (n : ℕ) :
    1 - (1 - p) ^ n ≤ (n : ℝ) * p := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      have hbase_nonneg : 0 ≤ 1 - p := by linarith
      have hbase_le_one : 1 - p ≤ 1 := by linarith
      have hpow_le_one : (1 - p) ^ n ≤ 1 :=
        pow_le_one₀ hbase_nonneg hbase_le_one
      have hpow_mul_le : (1 - p) ^ n * p ≤ 1 * p :=
        mul_le_mul_of_nonneg_right hpow_le_one hp_nonneg
      calc
        1 - (1 - p) ^ (n + 1) =
            (1 - (1 - p) ^ n) + (1 - p) ^ n * p := by
              rw [pow_succ]
              ring
        _ ≤ (n : ℝ) * p + (1 - p) ^ n * p :=
              by
                simpa [add_comm] using
                  (add_le_add_right ih ((1 - p) ^ n * p))
        _ ≤ (n : ℝ) * p + 1 * p :=
              add_le_add_right hpow_mul_le ((n : ℝ) * p)
        _ = ((n + 1 : ℕ) : ℝ) * p := by
              norm_num
              ring

/--
The strict upper-tail crossing probability at the explicit Theorem 3 quantile
is eventually at most `epsilon^2 / 4 + epsilon / 2`.  This uses the quantile's
*upper* bracket only, so it holds for every probability law, including atomic
laws; no max-concentration or nonatomicity is used.
-/
theorem theorem3LowTailQuantile_split_crossing_le_quadratic_eventually
    (noiseLaw : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure noiseLaw]
    {epsilon : ℝ} (hepsilon_pos : 0 < epsilon) :
    ∀ᶠ C : ℕ in atTop,
      1 -
          (1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
            (theorem3LowTailQuantile noiseLaw epsilon C)) ^
            (epsilonFloorSplitIndex (epsilon / 2) C + 1) ≤
        epsilon ^ 2 / 4 + epsilon / 2 := by
  filter_upwards
    [theorem3LowTailQuantile_upperTailMass_le_eventually noiseLaw hepsilon_pos]
    with C htail_upper
  let tail : ℝ :=
    AppliedModelingLib.Probability.upperTailMass noiseLaw
      (theorem3LowTailQuantile noiseLaw epsilon C)
  let count : ℕ := epsilonFloorSplitIndex (epsilon / 2) C + 1
  let den : ℝ := (((C + 1 : ℕ) : ℝ))
  have hden_pos : 0 < den := by
    dsimp [den]
    exact_mod_cast Nat.succ_pos C
  have hden_one : 1 ≤ den := by
    dsimp [den]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le C)
  have htail_nonneg : 0 ≤ tail := by
    dsimp [tail]
    exact AppliedModelingLib.Probability.upperTailMass_nonneg noiseLaw _
  have htail_le_one : tail ≤ 1 := by
    dsimp [tail]
    exact AppliedModelingLib.Probability.upperTailMass_le_one noiseLaw _
  have htail_bound : tail ≤ epsilon / (2 * den) := by
    simpa [tail, den, Nat.cast_add, Nat.cast_one] using htail_upper
  have htarget_nonneg : 0 ≤ epsilon / (2 * den) := by
    positivity
  have hsplit : (epsilonFloorSplitIndex (epsilon / 2) C : ℝ) ≤
      (epsilon / 2) * den := by
    simpa [den] using
      (epsilonFloorSplitIndex_le (epsilon / 2) C (by positivity))
  have hcount_bound : (count : ℝ) ≤ (epsilon / 2) * den + 1 := by
    dsimp [count]
    norm_num [Nat.cast_add, Nat.cast_one]
    linarith
  have hcross_le_count_tail :
      1 - (1 - tail) ^ count ≤ (count : ℝ) * tail :=
    one_sub_pow_le_natCast_mul htail_nonneg htail_le_one count
  have hcount_tail_le :
      (count : ℝ) * tail ≤ (count : ℝ) * (epsilon / (2 * den)) :=
    mul_le_mul_of_nonneg_left htail_bound (Nat.cast_nonneg _)
  have hcount_target_le :
      (count : ℝ) * (epsilon / (2 * den)) ≤
        ((epsilon / 2) * den + 1) * (epsilon / (2 * den)) :=
    mul_le_mul_of_nonneg_right hcount_bound htarget_nonneg
  have hinv_le_one : 1 / den ≤ 1 := by
    rw [div_le_iff₀ hden_pos]
    simpa using hden_one
  have hepsilon_half_nonneg : 0 ≤ epsilon / 2 := by positivity
  have hquadratic :
      ((epsilon / 2) * den + 1) * (epsilon / (2 * den)) ≤
        epsilon ^ 2 / 4 + epsilon / 2 := by
    have hrewrite :
        ((epsilon / 2) * den + 1) * (epsilon / (2 * den)) =
          epsilon ^ 2 / 4 + (epsilon / 2) * (1 / den) := by
      field_simp [ne_of_gt hden_pos]
      ring
    rw [hrewrite]
    calc
      epsilon ^ 2 / 4 + (epsilon / 2) * (1 / den) ≤
          epsilon ^ 2 / 4 + (epsilon / 2) * 1 :=
        add_le_add_right
          (mul_le_mul_of_nonneg_left hinv_le_one hepsilon_half_nonneg) _
      _ = epsilon ^ 2 / 4 + epsilon / 2 := by ring
  change
    1 - (1 - tail) ^ count ≤ epsilon ^ 2 / 4 + epsilon / 2
  exact hcross_le_count_tail.trans (hcount_tail_le.trans (hcount_target_le.trans hquadratic))

/--
If the current Theorem 3 quantile split-power capacity premise holds for an
eventually nonempty family of selected outcomes, it forces a supply upper
bound that is absent from the source model.  In particular, for a fixed
positive source supply one may choose a sufficiently small theorem tolerance
that contradicts this bound.

The eventual-nonemptiness premise is not an added model condition: it makes
the otherwise vacuous Lean proposition semantically correspond to the source's
stable-matchings/economies quantified in `source_tex/model.tex:77-93`.
-/
theorem theorem3_quantile_split_capacity_forces_supply_le_quadratic
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    {Admissible : ℕ → Type u}
    (noiseLaw : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure noiseLaw]
    {epsilon totalSupply : ℝ}
    (hepsilon_pos : 0 < epsilon)
    (hadmissible_nonempty : ∀ᶠ C : ℕ in atTop, Nonempty (Admissible C))
    {threshold : ∀ C : ℕ, Admissible C → ℝ}
    (hcapacity :
      source_assumption_market_low_cutoff_upper_tail_split_pow_exceeds_supply
        Mseq noiseLaw
        (fun C : ℕ => epsilonFloorSplitIndex (epsilon / 2) C)
        (fun C a =>
          threshold C a - epsilon + theorem3LowTailQuantile noiseLaw epsilon C)
        (fun C a => threshold C a - epsilon)
        totalSupply) :
    totalSupply ≤ epsilon ^ 2 / 4 + epsilon / 2 := by
  by_contra hnot
  have hsupply_gt : epsilon ^ 2 / 4 + epsilon / 2 < totalSupply :=
    lt_of_not_ge hnot
  have hquantile :=
    theorem3LowTailQuantile_split_crossing_le_quadratic_eventually
      noiseLaw hepsilon_pos
  have himpossible : ∀ᶠ C : ℕ in atTop, False := by
    filter_upwards [hcapacity, hadmissible_nonempty, hquantile] with
      C hcapacityC hnonemptyC hquantileC
    let a : Admissible C := Classical.choice hnonemptyC
    have hcross := hcapacityC a
    have hshift :
        (threshold C a - epsilon + theorem3LowTailQuantile noiseLaw epsilon C) -
            (threshold C a - epsilon) = theorem3LowTailQuantile noiseLaw epsilon C := by
      ring
    rw [hshift] at hcross
    linarith
  rcases Filter.eventually_atTop.1 himpossible with ⟨C, hC⟩
  exact hC C (le_refl C)

end PG24NoisyMatchingMarkets
