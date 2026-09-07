import ZhouChenLi2014OptimalPACMultipleArm.QuartileElimination

/-!
# Finite termination of tie-broken Quartile-Elimination

The source writes QE rounds until the active set is small.  With the explicit
tie repair, every nontrivial round has an exact cardinality recurrence.  This
file supplies a finite stopping theorem independent of the empirical scores.
-/

namespace ZhouChenLi2014OptimalPACMultipleArm

/-- Iterate the deterministic rounded survivor-count recurrence. -/
def quartileSurvivorCountIter : ℕ → ℕ → ℕ
  | 0, activeCount => activeCount
  | roundCount + 1, activeCount =>
      quartileSurvivorCountIter roundCount (quartileSurvivorCount activeCount)

/-- The rounded recurrence commutes with one additional QE update. -/
theorem quartileSurvivorCountIter_commute_update :
    ∀ roundCount activeCount,
      quartileSurvivorCountIter roundCount (quartileSurvivorCount activeCount) =
        quartileSurvivorCount
          (quartileSurvivorCountIter roundCount activeCount) := by
  intro roundCount
  induction roundCount with
  | zero =>
      intro activeCount
      rfl
  | succ roundCount ih =>
      intro activeCount
      rw [quartileSurvivorCountIter, ih]
      rw [quartileSurvivorCountIter, ih]

/-- The next iterate is the rounded update of the preceding iterate. -/
theorem quartileSurvivorCountIter_succ_eq_update
    (roundCount activeCount : ℕ) :
    quartileSurvivorCountIter (roundCount + 1) activeCount =
      quartileSurvivorCount (quartileSurvivorCountIter roundCount activeCount) := by
  rw [quartileSurvivorCountIter]
  exact quartileSurvivorCountIter_commute_update roundCount activeCount

/-- At an active-set size below four, the rounded QE count is unchanged. -/
theorem quartileSurvivorCount_eq_of_lt_four {activeCount : ℕ}
    (hactiveCount : activeCount < 4) :
    quartileSurvivorCount activeCount = activeCount := by
  unfold quartileSurvivorCount
  omega

/--
Above the three-arm fixed point, one tie-broken QE round contracts the excess
cardinality by the source's `3 / 4` factor, with all integer rounding explicit.
-/
theorem four_mul_quartileSurvivorCount_sub_three_le_three_mul_sub_three
    {activeCount : ℕ} (hactiveCount : 3 ≤ activeCount) :
    4 * (quartileSurvivorCount activeCount - 3) ≤ 3 * (activeCount - 3) := by
  unfold quartileSurvivorCount
  omega

/-- The rounded survivor count never drops below the three-arm fixed point. -/
theorem three_le_quartileSurvivorCount {activeCount : ℕ}
    (hactiveCount : 3 ≤ activeCount) :
    3 ≤ quartileSurvivorCount activeCount := by
  unfold quartileSurvivorCount
  omega

/-- Repeated QE leaves every already-small active set unchanged. -/
theorem quartileSurvivorCountIter_eq_of_le_three
    (roundCount activeCount : ℕ) (hactiveCount : activeCount ≤ 3) :
    quartileSurvivorCountIter roundCount activeCount = activeCount := by
  induction roundCount with
  | zero => rfl
  | succ roundCount ih =>
      rw [quartileSurvivorCountIter, quartileSurvivorCount_eq_of_lt_four (by omega), ih]

/-- Every iterate above the three-arm fixed point remains above that fixed point. -/
theorem three_le_quartileSurvivorCountIter :
    ∀ roundCount activeCount, 3 ≤ activeCount →
      3 ≤ quartileSurvivorCountIter roundCount activeCount := by
  intro roundCount
  induction roundCount with
  | zero =>
      intro activeCount hactiveCount
      simpa [quartileSurvivorCountIter] using hactiveCount
  | succ roundCount ih =>
      intro activeCount hactiveCount
      rw [quartileSurvivorCountIter]
      exact ih (quartileSurvivorCount activeCount)
        (three_le_quartileSurvivorCount hactiveCount)

/--
The exact rounded recurrence has the geometric `3/4` contraction claimed by
the source after subtracting its three-arm integer fixed point.
-/
theorem quartileSurvivorCountIter_potential_contract :
    ∀ roundCount activeCount, 3 ≤ activeCount →
      4 ^ roundCount * (quartileSurvivorCountIter roundCount activeCount - 3) ≤
        3 ^ roundCount * (activeCount - 3) := by
  intro roundCount
  induction roundCount with
  | zero =>
      intro activeCount _
      simp [quartileSurvivorCountIter]
  | succ roundCount ih =>
      intro activeCount hactiveCount
      have hsurvivors : 3 ≤ quartileSurvivorCount activeCount :=
        three_le_quartileSurvivorCount hactiveCount
      have hintermediate := ih (quartileSurvivorCount activeCount) hsurvivors
      have hscaledIntermediate := Nat.mul_le_mul_left 4 hintermediate
      have hround := four_mul_quartileSurvivorCount_sub_three_le_three_mul_sub_three
        hactiveCount
      have hscaledRound := Nat.mul_le_mul_left (3 ^ roundCount) hround
      calc
        4 ^ (roundCount + 1) *
            (quartileSurvivorCountIter (roundCount + 1) activeCount - 3) =
            4 * (4 ^ roundCount *
              (quartileSurvivorCountIter roundCount
                (quartileSurvivorCount activeCount) - 3)) := by
              simp [quartileSurvivorCountIter, pow_succ, mul_assoc, mul_comm]
        _ ≤ 4 * (3 ^ roundCount * (quartileSurvivorCount activeCount - 3)) :=
          hscaledIntermediate
        _ = 3 ^ roundCount * (4 * (quartileSurvivorCount activeCount - 3)) := by
          ring
        _ ≤ 3 ^ roundCount * (3 * (activeCount - 3)) := hscaledRound
        _ = 3 ^ (roundCount + 1) * (activeCount - 3) := by
          ring

/--
The exact integer recurrence is bounded by a `3/4` geometric envelope around
the three-arm fixed point.  This is the rounded replacement for the source's
unqualified `|S_r| ≤ (3/4)^r n` display.
-/
theorem quartileSurvivorCountIter_real_le_three_add_geometric
    (roundCount activeCount : ℕ) (hactiveCount : 3 ≤ activeCount) :
    (quartileSurvivorCountIter roundCount activeCount : ℝ) ≤
      3 + ((3 : ℝ) / 4) ^ roundCount * ((activeCount : ℝ) - 3) := by
  have hnat := quartileSurvivorCountIter_potential_contract roundCount activeCount
    hactiveCount
  have hiter : 3 ≤ quartileSurvivorCountIter roundCount activeCount :=
    three_le_quartileSurvivorCountIter roundCount activeCount hactiveCount
  have hreal : (4 : ℝ) ^ roundCount *
      ((quartileSurvivorCountIter roundCount activeCount : ℝ) - 3) ≤
        (3 : ℝ) ^ roundCount * ((activeCount : ℝ) - 3) := by
    calc
      (4 : ℝ) ^ roundCount *
          ((quartileSurvivorCountIter roundCount activeCount : ℝ) - 3) =
          ((4 ^ roundCount *
            (quartileSurvivorCountIter roundCount activeCount - 3) : ℕ) : ℝ) := by
            rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hiter]
            norm_num
      _ ≤ ((3 ^ roundCount * (activeCount - 3) : ℕ) : ℝ) := by
        exact_mod_cast hnat
      _ = (3 : ℝ) ^ roundCount * ((activeCount : ℝ) - 3) := by
        rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hactiveCount]
        norm_num
  have hfourPositive : 0 < (4 : ℝ) ^ roundCount := pow_pos (by norm_num) _
  have hdiv : (quartileSurvivorCountIter roundCount activeCount : ℝ) - 3 ≤
      ((3 : ℝ) ^ roundCount * ((activeCount : ℝ) - 3)) / (4 : ℝ) ^ roundCount := by
    apply (le_div_iff₀ hfourPositive).mpr
    simpa [mul_comm] using hreal
  have hformula :
      ((3 : ℝ) ^ roundCount * ((activeCount : ℝ) - 3)) / (4 : ℝ) ^ roundCount =
        ((3 : ℝ) / 4) ^ roundCount * ((activeCount : ℝ) - 3) := by
    rw [div_pow]
    ring
  calc
    (quartileSurvivorCountIter roundCount activeCount : ℝ) =
        3 + ((quartileSurvivorCountIter roundCount activeCount : ℝ) - 3) := by ring
    _ ≤ 3 + ((3 : ℝ) ^ roundCount * ((activeCount : ℝ) - 3)) /
        (4 : ℝ) ^ roundCount := by linarith
    _ = _ := by rw [hformula]

/--
At most one round per initially active arm suffices to reach a set of at most
three arms.  This is a score-independent finite stopping certificate; the
sharper geometric source horizon is a later resource refinement.
-/
theorem quartileSurvivorCountIter_le_three_of_le_roundCount :
    ∀ roundCount activeCount, activeCount ≤ roundCount →
      quartileSurvivorCountIter roundCount activeCount ≤ 3 := by
  intro roundCount
  induction roundCount with
  | zero =>
      intro activeCount hactiveCount
      simp [quartileSurvivorCountIter] at hactiveCount ⊢
      omega
  | succ roundCount ih =>
      intro activeCount hactiveCount
      by_cases hsmall : activeCount ≤ 3
      · calc
          quartileSurvivorCountIter (roundCount + 1) activeCount = activeCount :=
            quartileSurvivorCountIter_eq_of_le_three (roundCount + 1) activeCount hsmall
          _ ≤ 3 := hsmall
      · have hlarge : 4 ≤ activeCount := by omega
        rw [quartileSurvivorCountIter]
        apply ih
        have hstrict : quartileSurvivorCount activeCount < activeCount :=
          quartileSurvivorCount_lt hlarge
        omega

/-- Iterate the tie-broken QE update under arbitrary round- and state-dependent scores. -/
noncomputable def quartileEliminationIter {Arm : Type*} [Fintype Arm]
    (score : ℕ → Finset Arm → Arm → ℝ) : ℕ → Finset Arm → Finset Arm
  | 0, active => active
  | roundCount + 1, active =>
      quartileEliminationIter score roundCount
        (quartileEliminationSurvivors active (score roundCount active))

/-- The active cardinality follows the deterministic rounded count recurrence. -/
theorem quartileEliminationIter_card {Arm : Type*} [Fintype Arm]
    (score : ℕ → Finset Arm → Arm → ℝ) :
    ∀ (roundCount : ℕ) (active : Finset Arm),
      (quartileEliminationIter score roundCount active).card =
        quartileSurvivorCountIter roundCount active.card := by
  intro roundCount
  induction roundCount with
  | zero =>
      intro active
      rfl
  | succ roundCount ih =>
      intro active
      rw [quartileEliminationIter, ih, quartileEliminationSurvivors_card,
        quartileSurvivorCountIter]

/-- The finite score-independent QE stopping certificate on actual active sets. -/
theorem quartileEliminationIter_card_le_three_of_card_le_roundCount
    {Arm : Type*} [Fintype Arm] (score : ℕ → Finset Arm → Arm → ℝ)
    (roundCount : ℕ) (active : Finset Arm) (hroundCount : active.card ≤ roundCount) :
    (quartileEliminationIter score roundCount active).card ≤ 3 := by
  rw [quartileEliminationIter_card]
  exact quartileSurvivorCountIter_le_three_of_le_roundCount roundCount active.card hroundCount

end ZhouChenLi2014OptimalPACMultipleArm
