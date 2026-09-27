import MSVV07AdWords.AuditInterface
import Mathlib.Tactic

/-!
# Source-faithful runners and accounting objects for MSVV07

The reusable `AdWordsInstance.runAssignment` runner uses query identifiers as
assignment keys.  That is the right model when a finite query set is enumerated
once, but Sections 2--6 of MSVV07 describe a *sequence of occurrences* in which
the same query word may appear many times.  This file therefore gives each list
position its own decision record.  It also threads the feasibility-test and
score-comparison counts through the finite maximum scan that actually chooses
the advertiser.

The cost claims below use the paper's natural unit-cost exact-real oracle model:
one bid/budget feasibility test and one real score comparison each cost one.
They do not claim bit complexity for evaluating `Real.exp`.
-/

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

open scoped BigOperators Topology
open Filter

namespace AppliedModelingLib
namespace Online
namespace MSVV07PaperFacing
namespace SourceRunner

variable {Advertiser Query : Type*}

/-! ## Sections 2--3: source definitions -/

/--
Re-index a concrete arrival list by its positions.  This is the faithful
finite query universe for MSVV's online model: two equal query *words* at
different times become distinct `Fin history.length` occurrences while retain
their original bid vector.  It is deliberately not a deduplication.
-/
def occurrenceIndexedInstance
    (I : PaperInstance Advertiser Query) (history : List Query) :
    PaperInstance Advertiser (Fin history.length) where
  budget := I.budget
  bid a t := I.bid a (history.get t)

@[simp]
theorem occurrenceIndexedInstance_budget
    (I : PaperInstance Advertiser Query) (history : List Query) (a : Advertiser) :
    (occurrenceIndexedInstance I history).budget a = I.budget a :=
  rfl

@[simp]
theorem occurrenceIndexedInstance_bid
    (I : PaperInstance Advertiser Query) (history : List Query)
    (a : Advertiser) (t : Fin history.length) :
    (occurrenceIndexedInstance I history).bid a t = I.bid a (history.get t) :=
  rfl

theorem occurrenceIndexedInstance_nonnegativeBids
    (I : PaperInstance Advertiser Query) (history : List Query)
    (hbid : I.NonnegativeBids) :
    (occurrenceIndexedInstance I history).NonnegativeBids := by
  intro a t
  exact hbid a (history.get t)

theorem occurrenceIndexedInstance_positiveBudgets
    (I : PaperInstance Advertiser Query) (history : List Query)
    (hbudget : I.PositiveBudgets) :
    (occurrenceIndexedInstance I history).PositiveBudgets := by
  intro a
  simpa using hbudget a

theorem occurrenceIndexedInstance_smallBids
    (I : PaperInstance Advertiser Query) (history : List Query) {epsilon : ℝ}
    (hsmall : paperSmallBids I epsilon) :
    paperSmallBids (occurrenceIndexedInstance I history) epsilon := by
  intro a t
  simpa using hsmall a (history.get t)

/--
Section 6 delayed entry, represented on a concrete arrival sequence.  An
advertiser is unavailable before its one entry time and remains available from
then on; this deliberately rules out disappearance and re-entry.
-/
def availableFromEntry {n : ℕ}
    (entryTime : Advertiser → Fin (n + 1)) :
    Advertiser → Fin n → Prop :=
  fun a t => entryTime a ≤ t.castSucc

/-- Section 2's ratio definition, including its universal quantifier over inputs. -/
def IsAlphaCompetitive {Instance : Type*}
    (onlineRevenue offlineRevenue : Instance → ℝ) (α : ℝ) : Prop :=
  ∀ I, α ≤ onlineRevenue I / offlineRevenue I

/-- The temporary Section 2 normalization that every advertiser budget is one. -/
def EqualUnitBudgets {Advertiser Query : Type*}
    (I : PaperInstance Advertiser Query) : Prop :=
  ∀ a, I.budget a = 1

/-- The temporary Section 2 assumption that the chosen offline allocation exhausts all budgets. -/
def ExhaustsEveryBudget
    {Advertiser Query : Type*} [Fintype Query] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (A : PaperAssignment Advertiser Query) : Prop :=
  ∀ a, paperSpend I A a = I.budget a

/-- Section 3's finite tradeoff, with Lean index `i` representing source slab `i+1`. -/
noncomputable def discreteTradeoff (k : ℕ) (i : Fin k) : ℝ :=
  1 - Real.exp (-(1 - (((i.val + 1 : ℕ) : ℝ) / (k : ℝ))))

/-- The finite geometric tradeoff induced by Theorem 8's displayed dual point.
The last slab has zero weight; the preceding `k - 1` weights are the suffix
sums of the factor-revealing LP dual. -/
noncomputable def theorem8DiscreteTradeoff (k : ℕ) (i : Fin k) : ℝ :=
  1 - (1 - 1 / (k : ℝ)) ^ (k - (i.val + 1))

/-- On every preterminal slab, the geometric source tradeoff is exactly the
suffix weight induced by the paper's factor-revealing dual candidate. -/
theorem theorem8DiscreteTradeoff_castSucc_eq_paperRoutePsiCandidate
    (m : ℕ) (i : Fin m) :
    theorem8DiscreteTradeoff (m + 1) i.castSucc =
      MSVV07SourceLemmas.paperRoutePsiCandidate i := by
  rw [MSVV07SourceLemmas.paperRoutePsiCandidate_eq_closed_form]
  simp [theorem8DiscreteTradeoff]

/-- The finite geometric tradeoff is decreasing in the source slab order. -/
theorem theorem8DiscreteTradeoff_antitone (k : ℕ) :
    Antitone (theorem8DiscreteTradeoff k) := by
  intro i j hij
  have hkNat : 0 < k := Nat.zero_lt_of_lt i.isLt
  have hkReal : 0 < (k : ℝ) := by exact_mod_cast hkNat
  have hkOne : (1 : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast hkNat
  have hinv : 1 / (k : ℝ) ≤ 1 := by
    rw [one_div]
    exact (inv_le_one₀ hkReal).2 hkOne
  have hbase_nonneg : 0 ≤ 1 - 1 / (k : ℝ) := by linarith
  have hbase_le_one : 1 - 1 / (k : ℝ) ≤ 1 := by
    have : 0 ≤ 1 / (k : ℝ) := by positivity
    linarith
  have hexp : k - (j.val + 1) ≤ k - (i.val + 1) :=
    Nat.sub_le_sub_left (Nat.add_le_add_right hij 1) k
  have hpow :
      (1 - 1 / (k : ℝ)) ^ (k - (i.val + 1)) ≤
        (1 - 1 / (k : ℝ)) ^ (k - (j.val + 1)) := by
    exact pow_le_pow_of_le_one hbase_nonneg hbase_le_one hexp
  unfold theorem8DiscreteTradeoff
  linarith

/--
Successive finite Theorem 8 slab weights differ by at most `1/k`.  This is the
per-budget unit used to charge the sole right-endpoint mismatch between a
source final type and an active runner slab.
-/
theorem theorem8DiscreteTradeoff_drop_to_succ_le_one_div
    {k : ℕ} (i : Fin k) (hi : i.val + 1 < k) :
    theorem8DiscreteTradeoff k i -
      theorem8DiscreteTradeoff k ⟨i.val + 1, hi⟩ ≤ 1 / (k : ℝ) := by
  have hk : 0 < k := Nat.zero_lt_of_lt i.isLt
  have hkReal : 0 < (k : ℝ) := by exact_mod_cast hk
  let r : ℝ := 1 - 1 / (k : ℝ)
  have hrnonneg : 0 ≤ r := by
    dsimp [r]
    apply sub_nonneg.mpr
    rw [one_div]
    have hkone : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    exact (inv_le_one₀ hkReal).2 hkone
  have hrleone : r ≤ 1 := by
    dsimp [r]
    have : 0 ≤ 1 / (k : ℝ) := by positivity
    linarith
  let n : ℕ := k - (i.val + 2)
  have hfirst : k - (i.val + 1) = n + 1 := by
    dsimp [n]
    omega
  have hsecond : k - ((i.val + 1) + 1) = n := by
    rfl
  have hpow : r ^ n ≤ 1 := pow_le_one₀ hrnonneg hrleone
  have hinv : 0 ≤ 1 / (k : ℝ) := by positivity
  change (1 - r ^ (k - (i.val + 1))) -
      (1 - r ^ (k - ((i.val + 1) + 1))) ≤ 1 / (k : ℝ)
  rw [hfirst, hsecond, pow_succ]
  nlinarith [mul_le_mul_of_nonneg_right hpow hinv]

/-- The displayed finite tradeoff is antitone in the slab number. -/
theorem discreteTradeoff_antitone (k : ℕ) :
    Antitone (discreteTradeoff k) := by
  intro i j hij
  have hkNat : 0 < k := Nat.zero_lt_of_lt i.isLt
  have hk : 0 < (k : ℝ) := by exact_mod_cast hkNat
  have hijNat : i.val + 1 ≤ j.val + 1 := Nat.add_le_add_right hij 1
  have hijReal : ((i.val + 1 : ℕ) : ℝ) ≤ ((j.val + 1 : ℕ) : ℝ) := by
    exact_mod_cast hijNat
  have hfrac :
      ((i.val + 1 : ℕ) : ℝ) / (k : ℝ) ≤
        ((j.val + 1 : ℕ) : ℝ) / (k : ℝ) :=
    (div_le_div_iff_of_pos_right hk).2 hijReal
  have hexp :
      Real.exp (-(1 - (((i.val + 1 : ℕ) : ℝ) / (k : ℝ)))) ≤
        Real.exp (-(1 - (((j.val + 1 : ℕ) : ℝ) / (k : ℝ)))) :=
    Real.exp_le_exp.mpr (by linarith)
  unfold discreteTradeoff
  linarith

/-- The finite tradeoff is strictly decreasing on its finite slab domain. -/
theorem discreteTradeoff_strictAnti (k : ℕ) :
    StrictAnti (discreteTradeoff k) := by
  intro i j hij
  have hkNat : 0 < k := Nat.zero_lt_of_lt i.isLt
  have hk : 0 < (k : ℝ) := by exact_mod_cast hkNat
  have hijNat : i.val + 1 < j.val + 1 := Nat.add_lt_add_right hij 1
  have hijReal : ((i.val + 1 : ℕ) : ℝ) < ((j.val + 1 : ℕ) : ℝ) := by
    exact_mod_cast hijNat
  have hfrac :
      ((i.val + 1 : ℕ) : ℝ) / (k : ℝ) <
        ((j.val + 1 : ℕ) : ℝ) / (k : ℝ) :=
    (div_lt_div_iff_of_pos_right hk).2 hijReal
  have hexp :
      Real.exp (-(1 - (((i.val + 1 : ℕ) : ℝ) / (k : ℝ)))) <
        Real.exp (-(1 - (((j.val + 1 : ℕ) : ℝ) / (k : ℝ)))) :=
    Real.exp_lt_exp.mpr (by linarith)
  unfold discreteTradeoff
  linarith

/--
Source-shaped convergence bridge.  Whenever the fractions represented by a
sequence of one-indexed slabs converge to `s`, their finite weights converge to
the continuous Section 3 weight at `s`.
-/
theorem discreteTradeoff_converges_along_slab_fractions
    (slab : ℕ → ℕ) (s : ℝ)
    (hfraction :
      Tendsto (fun k : ℕ => ((slab k + 1 : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ))
        atTop (nhds s)) :
    Sequence.SeqTendsTo
      (fun k : ℕ =>
        1 - Real.exp
          (-(1 - (((slab k + 1 : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ)))))
      (1 - Real.exp (-(1 - s))) := by
  apply MSVV07SourceLemmas.seqTendsTo_of_tendsto
  have hcontinuous : Continuous (fun x : ℝ => 1 - Real.exp (-(1 - x))) := by
    fun_prop
  exact hcontinuous.continuousAt.tendsto.comp hfraction

/-! ## Section 3 greedy tight example in the paper's small-bid fluid scaling -/

/-- Aggregate revenues of the explicit two-bidder, two-word greedy example. -/
structure GreedyTwoWordFluidOutcome where
  greedyFirstPhase : ℝ
  greedySecondPhase : ℝ
  offlineFirstPhase : ℝ
  offlineSecondPhase : ℝ

/--
The first word has bids `c` and `c+epsilon` and total mass `1/(c+epsilon)`;
the second has bids `0` and `c` and total mass `1/c`.
-/
noncomputable def greedyTwoWordFluidOutcome (c epsilon : ℝ) :
    GreedyTwoWordFluidOutcome where
  greedyFirstPhase := (c + epsilon) * (1 / (c + epsilon))
  greedySecondPhase := 0
  offlineFirstPhase := c * (1 / (c + epsilon))
  offlineSecondPhase := c * (1 / c)

/-- Total online revenue in the fluid example. -/
noncomputable def greedyTwoWordOnlineRevenue (c epsilon : ℝ) : ℝ :=
  (greedyTwoWordFluidOutcome c epsilon).greedyFirstPhase +
    (greedyTwoWordFluidOutcome c epsilon).greedySecondPhase

/-- Revenue of the source's cross-phase offline assignment. -/
noncomputable def greedyTwoWordOfflineRevenue (c epsilon : ℝ) : ℝ :=
  (greedyTwoWordFluidOutcome c epsilon).offlineFirstPhase +
    (greedyTwoWordFluidOutcome c epsilon).offlineSecondPhase

/--
Construction-level calculation: greedy exhausts bidder two in phase one,
earns nothing in phase two, while the cross-phase offline assignment is
budget-feasible and obtains the displayed larger revenue.
-/
theorem greedyTwoWordFluidOutcome_fields
    {c epsilon : ℝ} (hc : 0 < c) (hepsilon : 0 < epsilon) :
    c < c + epsilon ∧
      greedyTwoWordOnlineRevenue c epsilon = 1 ∧
      greedyTwoWordOfflineRevenue c epsilon = 1 + c / (c + epsilon) ∧
      c / (c + epsilon) ≤ 1 ∧
      greedyTwoWordOnlineRevenue c epsilon /
          greedyTwoWordOfflineRevenue c epsilon =
        (c + epsilon) / (2 * c + epsilon) := by
  have hcne : c ≠ 0 := ne_of_gt hc
  have hsum : 0 < c + epsilon := by linarith
  have hsumne : c + epsilon ≠ 0 := ne_of_gt hsum
  have hden : 0 < 2 * c + epsilon := by linarith
  refine ⟨by linarith, ?_, ?_, ?_, ?_⟩
  · unfold greedyTwoWordOnlineRevenue greedyTwoWordFluidOutcome
    field_simp [hsumne]
    norm_num
  · unfold greedyTwoWordOfflineRevenue greedyTwoWordFluidOutcome
    field_simp [hcne, hsumne]
    ring
  · exact (div_le_one hsum).2 (by linarith)
  · rw [show greedyTwoWordOnlineRevenue c epsilon = 1 by
      unfold greedyTwoWordOnlineRevenue greedyTwoWordFluidOutcome
      field_simp [hsumne]
      norm_num]
    rw [show greedyTwoWordOfflineRevenue c epsilon =
        1 + c / (c + epsilon) by
      unfold greedyTwoWordOfflineRevenue greedyTwoWordFluidOutcome
      field_simp [hcne, hsumne]
      ring]
    field_simp [hsumne, ne_of_gt hden]
    ring

/--
The active zero-based slab for a nonnegative spent fraction.  The `min` maps a
fully spent bidder to the last slab; source slab numbers are this value plus one.
-/
noncomputable def activeSlab
    (k : ℕ) (hk : 0 < k) (spentFraction : ℝ) : Fin k :=
  ⟨min (Nat.floor (max 0 ((k : ℝ) * spentFraction))) (k - 1), by
    have hlast : k - 1 < k := Nat.sub_lt hk (by omega)
    exact lt_of_le_of_lt (Nat.min_le_right _ _) hlast⟩

/-- The active slab in a general-budget state, using the spent-budget fraction. -/
noncomputable def activeBudgetSlab
    (k : ℕ) (hk : 0 < k) (spent budget : ℝ) : Fin k :=
  activeSlab k hk (spent / budget)

/-- The finite Theorem 8 tradeoff as a function of a spent-budget fraction. -/
noncomputable def theorem8DiscreteSlabTradeoff
    (k : ℕ) (hk : 0 < k) : ℝ → ℝ :=
  fun spentFraction => theorem8DiscreteTradeoff k (activeSlab k hk spentFraction)

/-- Paper-facing expansion of the current-slab computation. -/
theorem activeSlab_val_formula
    (k : ℕ) (hk : 0 < k) (spentFraction : ℝ) :
    (activeSlab k hk spentFraction).val =
      min (Nat.floor (max 0 ((k : ℝ) * spentFraction))) (k - 1) := by
  rfl

/-- The runner's zero-based active slab is monotone in the spent fraction. -/
theorem activeSlab_monotone
    (k : ℕ) (hk : 0 < k) :
    Monotone (activeSlab k hk) := by
  intro x y hxy
  change min (Nat.floor (max 0 ((k : ℝ) * x))) (k - 1) ≤
    min (Nat.floor (max 0 ((k : ℝ) * y))) (k - 1)
  exact min_le_min_right _ <|
    Nat.floor_mono <| max_le_max le_rfl
      (mul_le_mul_of_nonneg_left hxy (Nat.cast_nonneg k))

/-- With a positive budget, the active budget slab is monotone in spend. -/
theorem activeBudgetSlab_monotone_spent
    (k : ℕ) (hk : 0 < k) (budget : ℝ) (hbudget : 0 < budget)
    {spent spent' : ℝ} (hspent : spent ≤ spent') :
    activeBudgetSlab k hk spent budget ≤ activeBudgetSlab k hk spent' budget := by
  apply activeSlab_monotone k hk
  exact div_le_div_of_nonneg_right hspent hbudget.le

/-- A feasible nonnegative spent fraction lies in the interval of its active slab. -/
theorem activeSlab_bounds
    {k : ℕ} (hk : 0 < k) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    let i := activeSlab k hk x
    ((i.val : ℝ) / (k : ℝ) ≤ x) ∧
      (x ≤ ((i.val + 1 : ℕ) : ℝ) / (k : ℝ)) := by
  dsimp only
  let n := Nat.floor (max 0 ((k : ℝ) * x))
  let i := activeSlab k hk x
  have hkReal : 0 < (k : ℝ) := by exact_mod_cast hk
  have hprod : 0 ≤ (k : ℝ) * x :=
    mul_nonneg (Nat.cast_nonneg k) hx0
  have hmax : max 0 ((k : ℝ) * x) = (k : ℝ) * x :=
    max_eq_right hprod
  have hfloor_le : (n : ℝ) ≤ (k : ℝ) * x := by
    rw [← hmax]
    exact Nat.floor_le (le_max_left _ _)
  have hfloor_lt : (k : ℝ) * x < (n : ℝ) + 1 := by
    rw [← hmax]
    exact Nat.lt_floor_add_one _
  have hi : i.val = min n (k - 1) := by
    rfl
  constructor
  · apply (div_le_iff₀ hkReal).2
    calc
      (i.val : ℝ) ≤ (n : ℝ) := by
        rw [hi]
        exact_mod_cast Nat.min_le_left n (k - 1)
      _ ≤ (k : ℝ) * x := hfloor_le
      _ = x * (k : ℝ) := by ring
  · apply (le_div_iff₀ hkReal).2
    by_cases hfloor : n ≤ k - 1
    · have hieval : i.val = n := by
        rw [hi]
        exact Nat.min_eq_left hfloor
      rw [hieval]
      simpa [Nat.cast_add, mul_comm] using hfloor_lt.le
    · have hkminus : k - 1 ≤ n := by omega
      have hieval : i.val = k - 1 := by
        rw [hi]
        exact Nat.min_eq_right hkminus
      rw [hieval]
      have hkcast : ((k - 1 + 1 : ℕ) : ℝ) = (k : ℝ) := by
        congr 1
        omega
      calc
        x * (k : ℝ) ≤ (k : ℝ) * 1 :=
          by simpa [mul_comm] using
            (mul_le_mul_of_nonneg_left hx1 hkReal.le)
        _ = ((k - 1 + 1 : ℕ) : ℝ) := by simp [hkcast]

/-- A feasible nonnegative spend lies in the interval of its active budget slab. -/
theorem activeBudgetSlab_bounds
    {k : ℕ} (hk : 0 < k) (spent budget : ℝ)
    (hspent : 0 ≤ spent) (hbudget : 0 < budget) (hfeasible : spent ≤ budget) :
    let i := activeBudgetSlab k hk spent budget
    (budget * (i.val : ℝ) / (k : ℝ) ≤ spent) ∧
      (spent ≤ budget * ((i.val + 1 : ℕ) : ℝ) / (k : ℝ)) := by
  have hfrac0 : 0 ≤ spent / budget := div_nonneg hspent hbudget.le
  have hfrac1 : spent / budget ≤ 1 := (div_le_one₀ hbudget).2 hfeasible
  obtain ⟨hlower, hupper⟩ := activeSlab_bounds hk (spent / budget) hfrac0 hfrac1
  constructor
  · have hmul := (le_div_iff₀ hbudget).mp hlower
    calc
      budget * ((activeBudgetSlab k hk spent budget).val : ℝ) / (k : ℝ) =
          ((activeBudgetSlab k hk spent budget).val : ℝ) / (k : ℝ) * budget := by
            ring
      _ ≤ spent := hmul
  · have hmul := (div_le_iff₀ hbudget).mp hupper
    calc
      spent ≤ ((activeBudgetSlab k hk spent budget).val + 1 : ℕ) / (k : ℝ) * budget :=
        hmul
      _ = budget * ((activeBudgetSlab k hk spent budget).val + 1 : ℕ) / (k : ℝ) := by
        ring

/-- Lower endpoint of one scalar budget slab. -/
noncomputable def theorem8SlabLower (k : ℕ) (budget : ℝ) (i : Fin k) : ℝ :=
  budget * (i.val : ℝ) / (k : ℝ)

/-- Upper endpoint of one scalar budget slab. -/
noncomputable def theorem8SlabUpper (k : ℕ) (budget : ℝ) (i : Fin k) : ℝ :=
  budget * ((i.val + 1 : ℕ) : ℝ) / (k : ℝ)

/-- The part of a scalar final spend lying in one budget slab. -/
noncomputable def theorem8SlabSpent (k : ℕ) (budget spent : ℝ) (i : Fin k) : ℝ :=
  min spent (theorem8SlabUpper k budget i) -
    min spent (theorem8SlabLower k budget i)

/-- Split-payment potential at finite Theorem 8 slab weights. -/
noncomputable def theorem8SlabPotential
    (k : ℕ) (budget : ℝ) (psi : Fin k → ℝ) (spent : ℝ) : ℝ :=
  ∑ i : Fin k, psi i * theorem8SlabSpent k budget spent i

/-- A nonnegative-budget slab has ordered endpoints. -/
theorem theorem8SlabLower_le_upper
    {k : ℕ} (budget : ℝ) (hbudget : 0 ≤ budget) (i : Fin k) :
    theorem8SlabLower k budget i ≤ theorem8SlabUpper k budget i := by
  have hk : 0 < (k : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt i.isLt)
  unfold theorem8SlabLower theorem8SlabUpper
  apply (div_le_div_iff_of_pos_right hk).2
  exact mul_le_mul_of_nonneg_left (by norm_num) hbudget

/-- A spend below a slab's lower endpoint contributes nothing to that slab. -/
theorem theorem8SlabSpent_eq_zero_of_le_lower
    {k : ℕ} (budget spent : ℝ) (i : Fin k)
    (hbudget : 0 ≤ budget) (hspent : spent ≤ theorem8SlabLower k budget i) :
    theorem8SlabSpent k budget spent i = 0 := by
  unfold theorem8SlabSpent
  have hupper := theorem8SlabLower_le_upper budget hbudget i
  rw [min_eq_left hspent, min_eq_left (hspent.trans hupper)]
  ring

/-- A spend above a slab's upper endpoint fills exactly one slab width. -/
theorem theorem8SlabSpent_eq_width_of_upper_le
    {k : ℕ} (budget spent : ℝ) (i : Fin k)
    (hbudget : 0 ≤ budget) (hspent : theorem8SlabUpper k budget i ≤ spent) :
    theorem8SlabSpent k budget spent i = budget / (k : ℝ) := by
  have hlower := (theorem8SlabLower_le_upper budget hbudget i).trans hspent
  change min spent (theorem8SlabUpper k budget i) -
    min spent (theorem8SlabLower k budget i) = _
  rw [min_eq_right hspent, min_eq_right hlower]
  unfold theorem8SlabUpper theorem8SlabLower
  push_cast
  ring

/-- Within one slab, split spend is final spend minus the slab lower endpoint. -/
theorem theorem8SlabSpent_eq_sub_lower_of_mem
    {k : ℕ} (budget spent : ℝ) (i : Fin k)
    (hlower : theorem8SlabLower k budget i ≤ spent)
    (hupper : spent ≤ theorem8SlabUpper k budget i) :
    theorem8SlabSpent k budget spent i = spent - theorem8SlabLower k budget i := by
  unfold theorem8SlabSpent
  rw [min_eq_left hupper, min_eq_right hlower]

/-- Earlier slab upper endpoints lie below later slab lower endpoints. -/
theorem theorem8_upper_le_lower_of_lt
    {k : ℕ} (budget : ℝ) (hbudget : 0 ≤ budget) {i j : Fin k} (hij : i < j) :
    theorem8SlabUpper k budget i ≤ theorem8SlabLower k budget j := by
  have hk : 0 < (k : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt i.isLt)
  have hindex : i.val + 1 ≤ j.val := by omega
  unfold theorem8SlabUpper theorem8SlabLower
  apply (div_le_div_iff_of_pos_right hk).2
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hindex) hbudget

/--
If a nonnegative payment does not straddle its active slab, its source-weighted
charge is exactly the increment in split-payment slab potential.
-/
theorem theorem8SlabPotential_increment_no_straddle
    {k : ℕ} (budget spent payment : ℝ) (psi : Fin k → ℝ) (i : Fin k)
    (hbudget : 0 ≤ budget) (hlower : theorem8SlabLower k budget i ≤ spent)
    (hpayment : 0 ≤ payment)
    (hupper : spent + payment ≤ theorem8SlabUpper k budget i) :
    theorem8SlabPotential k budget psi (spent + payment) =
      theorem8SlabPotential k budget psi spent + psi i * payment := by
  have hcomponent : ∀ j : Fin k,
      theorem8SlabSpent k budget (spent + payment) j =
        theorem8SlabSpent k budget spent j + if j = i then payment else 0 := by
    intro j
    rcases lt_trichotomy j i with hj | hji | hj
    · have hji' : theorem8SlabUpper k budget j ≤ theorem8SlabLower k budget i :=
        theorem8_upper_le_lower_of_lt budget hbudget hj
      have hspent : theorem8SlabUpper k budget j ≤ spent := hji'.trans hlower
      have htotal : theorem8SlabUpper k budget j ≤ spent + payment := by linarith
      rw [theorem8SlabSpent_eq_width_of_upper_le budget (spent + payment) j hbudget htotal,
        theorem8SlabSpent_eq_width_of_upper_le budget spent j hbudget hspent]
      simp [hj.ne]
    · subst j
      have hlower' : theorem8SlabLower k budget i ≤ spent + payment := by linarith
      rw [theorem8SlabSpent_eq_sub_lower_of_mem budget (spent + payment) i hlower' hupper]
      have hspentUpper : spent ≤ theorem8SlabUpper k budget i := by linarith
      rw [theorem8SlabSpent_eq_sub_lower_of_mem budget spent i hlower hspentUpper]
      simp
      ring
    · have hij' : theorem8SlabUpper k budget i ≤ theorem8SlabLower k budget j :=
        theorem8_upper_le_lower_of_lt budget hbudget hj
      have htotal : spent + payment ≤ theorem8SlabLower k budget j := hupper.trans hij'
      have hspent : spent ≤ theorem8SlabLower k budget j := by linarith
      rw [theorem8SlabSpent_eq_zero_of_le_lower budget (spent + payment) j hbudget htotal,
        theorem8SlabSpent_eq_zero_of_le_lower budget spent j hbudget hspent]
      simp [hj.ne']
  unfold theorem8SlabPotential
  calc
    (∑ j : Fin k, psi j * theorem8SlabSpent k budget (spent + payment) j) =
        ∑ j : Fin k, psi j *
          (theorem8SlabSpent k budget spent j + if j = i then payment else 0) := by
            apply Finset.sum_congr rfl
            intro j _
            rw [hcomponent j]
    _ = (∑ j : Fin k, psi j * theorem8SlabSpent k budget spent j) + psi i * payment := by
      simp only [mul_add]
      rw [Finset.sum_add_distrib]
      simp

/-- The upper endpoint of a terminal slab is the complete budget. -/
theorem theorem8SlabUpper_terminal
    {k : ℕ} (i : Fin k) (budget : ℝ) (hterminal : i.val + 1 = k) :
    theorem8SlabUpper k budget i = budget := by
  unfold theorem8SlabUpper
  rw [hterminal]
  have hk : (k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt i.isLt))
  field_simp

/-- The upper endpoint of one slab is the lower endpoint of its successor. -/
theorem theorem8SlabUpper_eq_next_lower
    {k : ℕ} (i : Fin k) (budget : ℝ) (hi : i.val + 1 < k) :
    theorem8SlabUpper k budget i =
      theorem8SlabLower k budget ⟨i.val + 1, hi⟩ := by
  unfold theorem8SlabUpper theorem8SlabLower
  rfl

/-- Moving one complete slab advances the upper endpoint by `budget / k`. -/
theorem theorem8SlabUpper_next
    {k : ℕ} (i : Fin k) (budget : ℝ) (hi : i.val + 1 < k) :
    theorem8SlabUpper k budget ⟨i.val + 1, hi⟩ =
      theorem8SlabUpper k budget i + budget / (k : ℝ) := by
  unfold theorem8SlabUpper
  push_cast
  ring

/--
A feasible payment of at most one slab loses at most `payment / k` against
its split-payment potential.  This formalizes the finite no-straddling
rounding estimate used in the source Lemma 7 accounting.
-/
theorem theorem8SlabPotential_increment_le_start_weight
    {k : ℕ} (budget spent payment : ℝ) (psi : Fin k → ℝ) (i : Fin k)
    (hbudget : 0 ≤ budget) (hlower : theorem8SlabLower k budget i ≤ spent)
    (hspentUpper : spent ≤ theorem8SlabUpper k budget i)
    (hpayment : 0 ≤ payment) (hpayment_le : payment ≤ budget / (k : ℝ))
    (hfeasible : spent + payment ≤ budget)
    (hdrop : ∀ (j : Fin k) (hj : j.val + 1 < k),
      psi j - psi ⟨j.val + 1, hj⟩ ≤ 1 / (k : ℝ)) :
    payment * psi i ≤
      theorem8SlabPotential k budget psi (spent + payment) -
        theorem8SlabPotential k budget psi spent + payment / (k : ℝ) := by
  have hk : 0 < (k : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt i.isLt)
  by_cases hnostraddle : spent + payment ≤ theorem8SlabUpper k budget i
  · have hpotential := theorem8SlabPotential_increment_no_straddle
      budget spent payment psi i hbudget hlower hpayment hnostraddle
    rw [hpotential]
    have herr : 0 ≤ payment * (k : ℝ)⁻¹ := by
      simpa [div_eq_mul_inv] using (div_nonneg hpayment hk.le)
    ring_nf
    linarith
  · have hnext : i.val + 1 < k := by
      by_contra hnot
      have hterminal : i.val + 1 = k := by omega
      have hupper := theorem8SlabUpper_terminal i budget hterminal
      rw [hupper] at hnostraddle
      exact hnostraddle hfeasible
    let next : Fin k := ⟨i.val + 1, hnext⟩
    let first : ℝ := theorem8SlabUpper k budget i - spent
    let second : ℝ := spent + payment - theorem8SlabUpper k budget i
    have hfirst0 : 0 ≤ first := by dsimp [first]; linarith
    have hsecond0 : 0 ≤ second := by dsimp [second]; linarith
    have hsplit : payment = first + second := by
      dsimp [first, second]
      ring
    have hfirstEnd : spent + first = theorem8SlabUpper k budget i := by
      dsimp [first]
      ring
    have hnextLower : theorem8SlabLower k budget next = theorem8SlabUpper k budget i := by
      symm
      exact theorem8SlabUpper_eq_next_lower i budget hnext
    have hnextUpper : theorem8SlabUpper k budget next =
        theorem8SlabUpper k budget i + budget / (k : ℝ) := by
      exact theorem8SlabUpper_next i budget hnext
    have hsecondEnd : theorem8SlabUpper k budget i + second = spent + payment := by
      dsimp [second]
      ring
    have hsecondUpper : theorem8SlabUpper k budget i + second ≤
        theorem8SlabUpper k budget next := by
      rw [hsecondEnd, hnextUpper]
      linarith
    have hfirstPotential := theorem8SlabPotential_increment_no_straddle
      budget spent first psi i hbudget hlower hfirst0 (by rw [hfirstEnd])
    have hsecondPotential := theorem8SlabPotential_increment_no_straddle
      budget (theorem8SlabUpper k budget i) second psi next hbudget
      (by rw [← hnextLower]) hsecond0 hsecondUpper
    have hpotential : theorem8SlabPotential k budget psi (spent + payment) =
        theorem8SlabPotential k budget psi spent + psi i * first + psi next * second := by
      calc
        theorem8SlabPotential k budget psi (spent + payment) =
            theorem8SlabPotential k budget psi
              (theorem8SlabUpper k budget i + second) := by rw [hsecondEnd]
        _ = theorem8SlabPotential k budget psi
              (theorem8SlabUpper k budget i) + psi next * second := hsecondPotential
        _ = (theorem8SlabPotential k budget psi spent + psi i * first) +
              psi next * second := by rw [← hfirstEnd, hfirstPotential]
        _ = _ := by ring
    have hsecond_le : second ≤ payment := by
      dsimp [second]
      linarith
    have hgap := hdrop i hnext
    have hgapScaled : second * (psi i - psi next) ≤ second * (1 / (k : ℝ)) :=
      mul_le_mul_of_nonneg_left hgap hsecond0
    have hround : second * (1 / (k : ℝ)) ≤ payment / (k : ℝ) := by
      calc
        second * (1 / (k : ℝ)) = second / (k : ℝ) := by ring
        _ ≤ payment / (k : ℝ) :=
          div_le_div_of_nonneg_right hsecond_le hk.le
    rw [hpotential]
    nlinarith [hgapScaled, hround]

/-! ## An actual finite maximum scan with a cost ledger -/

/-- Result and exact unit-cost counters returned by a finite maximum scan. -/
structure FiniteMaxScanResult (Advertiser : Type*) where
  winner : Option Advertiser
  candidateTests : ℕ
  scoreComparisons : ℕ

/--
A right-to-left scan of a concrete advertiser list.  Every element incurs one
feasibility test.  A score comparison is incurred exactly when the element is
feasible and the already-scanned suffix has a feasible winner.
-/
noncomputable def finiteMaxScan {Advertiser : Type*}
    (feasible : Advertiser → Prop) (score : Advertiser → ℝ) :
    List Advertiser → FiniteMaxScanResult Advertiser
  | [] => ⟨none, 0, 0⟩
  | a :: as =>
      let tail := finiteMaxScan feasible score as
      if ha : feasible a then
        match tail.winner with
        | none => ⟨some a, tail.candidateTests + 1, tail.scoreComparisons⟩
        | some b =>
            if score b ≤ score a then
              ⟨some a, tail.candidateTests + 1, tail.scoreComparisons + 1⟩
            else
              ⟨some b, tail.candidateTests + 1, tail.scoreComparisons + 1⟩
      else
        ⟨tail.winner, tail.candidateTests + 1, tail.scoreComparisons⟩

/-- The candidate counter is the exact number of list elements inspected. -/
theorem finiteMaxScan_candidateTests {Advertiser : Type*}
    (feasible : Advertiser → Prop) (score : Advertiser → ℝ)
    (xs : List Advertiser) :
    (finiteMaxScan feasible score xs).candidateTests = xs.length := by
  classical
  induction xs with
  | nil => rfl
  | cons a as ih =>
      by_cases ha : feasible a
      · rw [finiteMaxScan]
        simp only [ha, dite_true]
        cases htail : (finiteMaxScan feasible score as).winner with
        | none => simp [htail, ih]
        | some b =>
            by_cases hscore : score b ≤ score a <;>
              simp [htail, hscore, ih]
      · rw [finiteMaxScan]
        simp [ha, ih]

/-- A scan performs at most one score comparison per inspected candidate. -/
theorem finiteMaxScan_scoreComparisons_le {Advertiser : Type*}
    (feasible : Advertiser → Prop) (score : Advertiser → ℝ)
    (xs : List Advertiser) :
    (finiteMaxScan feasible score xs).scoreComparisons ≤ xs.length := by
  classical
  induction xs with
  | nil => simp [finiteMaxScan]
  | cons a as ih =>
      by_cases ha : feasible a
      · rw [finiteMaxScan]
        simp only [ha, dite_true]
        cases htail : (finiteMaxScan feasible score as).winner with
        | none =>
            simp only [htail, List.length_cons]
            omega
        | some b =>
            by_cases hscore : score b ≤ score a <;>
              simp [htail, hscore, ih]
      · rw [finiteMaxScan]
        simp only [ha, dite_false, List.length_cons]
        omega

/-- Complete semantic specification of the recursive scan's selected winner. -/
theorem finiteMaxScan_winner_spec {Advertiser : Type*}
    (feasible : Advertiser → Prop) (score : Advertiser → ℝ)
    (xs : List Advertiser) :
    let result := finiteMaxScan feasible score xs
    (result.winner = none ↔ ∀ a ∈ xs, ¬ feasible a) ∧
      ∀ w, result.winner = some w →
        w ∈ xs ∧ feasible w ∧
          ∀ a ∈ xs, feasible a → score a ≤ score w := by
  classical
  induction xs with
  | nil => simp [finiteMaxScan]
  | cons a as ih =>
      dsimp only
      by_cases ha : feasible a
      · cases htail : (finiteMaxScan feasible score as).winner with
        | none =>
            have ihNone : ∀ b ∈ as, ¬ feasible b :=
              (ih.1).1 htail
            simp only [finiteMaxScan, ha, dite_true, htail]
            constructor
            · constructor
              · intro hnone
                simp at hnone
              · intro hall
                exact False.elim ((hall a (by simp)) ha)
            · intro w hw
              have hw' : a = w := by simpa using hw
              subst w
              refine ⟨by simp, ha, ?_⟩
              intro b hb hbfeas
              simp only [List.mem_cons] at hb
              rcases hb with hba | hb
              · subst b
                exact le_rfl
              · exact False.elim (ihNone b hb hbfeas)
        | some b =>
            have ihSome := ih.2 b htail
            by_cases hscore : score b ≤ score a
            · simp only [finiteMaxScan, ha, dite_true, htail, hscore, if_pos]
              constructor
              · constructor
                · intro hnone
                  simp at hnone
                · intro hall
                  exact False.elim ((hall a (by simp)) ha)
              · intro w hw
                have hw' : a = w := by simpa using hw
                subst w
                refine ⟨by simp, ha, ?_⟩
                intro c hc hcfeas
                simp only [List.mem_cons] at hc
                rcases hc with hca | hc
                · subst c
                  exact le_rfl
                · exact (ihSome.2.2 c hc hcfeas).trans hscore
            · have ha_le_b : score a ≤ score b := le_of_not_ge hscore
              simp only [finiteMaxScan, ha, dite_true, htail, hscore, if_false]
              constructor
              · constructor
                · intro hnone
                  simp at hnone
                · intro hall
                  exact False.elim ((hall a (by simp)) ha)
              · intro w hw
                have hw' : b = w := by simpa using hw
                subst w
                refine ⟨by simp [ihSome.1], ihSome.2.1, ?_⟩
                intro c hc hcfeas
                simp only [List.mem_cons] at hc
                rcases hc with hca | hc
                · subst c
                  exact ha_le_b
                · exact ihSome.2.2 c hc hcfeas
      · simp only [finiteMaxScan, ha, dite_false]
        constructor
        · constructor
          · intro hnone
            have hnoneTail :
                (finiteMaxScan feasible score as).winner = none := hnone
            intro b hb
            simp only [List.mem_cons] at hb
            rcases hb with hba | hb
            · subst b
              exact ha
            · exact (ih.1.1 hnoneTail) b hb
          · intro hall
            exact ih.1.2 (fun b hb => hall b (by simp [hb]))
        · intro w hw
          have hspec := ih.2 w hw
          exact ⟨by simp [hspec.1], hspec.2.1, by
            intro b hb hbfeas
            simp only [List.mem_cons] at hb
            rcases hb with hba | hb
            · subst b
              exact False.elim (ha hbfeas)
            · exact hspec.2.2 b hb hbfeas⟩

/-! ## Occurrence-indexed online execution -/

/-- One source-sequence decision, including the spend vector before the arrival. -/
structure OccurrenceDecision (Advertiser Query : Type*) where
  query : Query
  winner : Option Advertiser
  spentBefore : Advertiser → ℝ

/-- State of an occurrence-indexed online execution. -/
structure OccurrenceState (Advertiser Query : Type*) where
  spent : Advertiser → ℝ
  revenue : ℝ
  decisionsRev : List (OccurrenceDecision Advertiser Query)
  candidateTests : ℕ
  scoreComparisons : ℕ

/-- Empty occurrence-indexed state. -/
def initialOccurrenceState : OccurrenceState Advertiser Query where
  spent := fun _ => 0
  revenue := 0
  decisionsRev := []
  candidateTests := 0
  scoreComparisons := 0

/-- Every advertiser's accumulated charge remains within her budget. -/
def occurrenceStateBudgetFeasible
    (I : PaperInstance Advertiser Query)
    (S : OccurrenceState Advertiser Query) : Prop :=
  ∀ a, S.spent a ≤ I.budget a

/-- Every accumulated charge is nonnegative. -/
def occurrenceStateNonnegativeSpend
    (S : OccurrenceState Advertiser Query) : Prop :=
  ∀ a, 0 ≤ S.spent a

/-- Decision queries in chronological order, extracted from the reverse ledger. -/
def occurrenceDecisionQueries
    (S : OccurrenceState Advertiser Query) : List Query :=
  S.decisionsRev.reverse.map OccurrenceDecision.query

/-- The aggregate advertiser charge recorded in an occurrence state. -/
noncomputable def occurrenceStateTotalSpend
    [Fintype Advertiser]
    (S : OccurrenceState Advertiser Query) : ℝ :=
  ∑ a : Advertiser, S.spent a

/-- The empty occurrence state is budget feasible under nonnegative budgets. -/
theorem initialOccurrenceState_budget_feasible
    (I : PaperInstance Advertiser Query)
    (hbudget : I.NonnegativeBudgets) :
    occurrenceStateBudgetFeasible I initialOccurrenceState := by
  intro a
  simpa [initialOccurrenceState] using hbudget a

/-- The empty occurrence state has nonnegative spend. -/
theorem initialOccurrenceState_nonnegative_spend :
    occurrenceStateNonnegativeSpend
      (initialOccurrenceState : OccurrenceState Advertiser Query) := by
  intro a
  rfl

/-- Feasibility of assigning the next occurrence in an occurrence state. -/
def occurrenceCanAssign
    (I : PaperInstance Advertiser Query)
    (S : OccurrenceState Advertiser Query) (q : Query) (a : Advertiser) : Prop :=
  S.spent a + I.bid a q ≤ I.budget a

/-- Continuous MSVV scaled bid computed from the occurrence state's actual spend. -/
noncomputable def occurrenceBalanceScore
    (I : PaperInstance Advertiser Query)
    (S : OccurrenceState Advertiser Query) (q : Query) (a : Advertiser) : ℝ :=
  I.bid a q * (1 - Real.exp (S.spent a / I.budget a - 1))

/--
The score used by the Section 5 algorithm with an arbitrary tradeoff function
`psi`: a bid times `psi` of the bidder's current spent-budget fraction.
-/
noncomputable def occurrenceTradeoffScore
    (psi : ℝ → ℝ) (I : PaperInstance Advertiser Query)
    (S : OccurrenceState Advertiser Query) (q : Query) (a : Advertiser) : ℝ :=
  I.bid a q * psi (S.spent a / I.budget a)

/-- Discrete Section 3 score computed from the currently active budget slab. -/
noncomputable def occurrenceDiscreteScore
    (k : ℕ) (hk : 0 < k)
    (I : PaperInstance Advertiser Query)
    (S : OccurrenceState Advertiser Query) (q : Query) (a : Advertiser) : ℝ :=
  I.bid a q * discreteTradeoff k
    (activeBudgetSlab k hk (S.spent a) (I.budget a))

/-- Theorem 8's finite geometric score at the currently active budget slab. -/
noncomputable def occurrenceTheorem8DiscreteScore
    (k : ℕ) (hk : 0 < k)
    (I : PaperInstance Advertiser Query)
    (S : OccurrenceState Advertiser Query) (q : Query) (a : Advertiser) : ℝ :=
  I.bid a q * theorem8DiscreteTradeoff k
    (activeBudgetSlab k hk (S.spent a) (I.budget a))

/-- The finite Theorem 8 score is an ordinary source tradeoff score. -/
theorem occurrenceTheorem8DiscreteScore_eq_tradeoffScore
    (k : ℕ) (hk : 0 < k)
    (I : PaperInstance Advertiser Query)
    (S : OccurrenceState Advertiser Query) (q : Query) (a : Advertiser) :
    occurrenceTheorem8DiscreteScore k hk I S q a =
      occurrenceTradeoffScore (theorem8DiscreteSlabTradeoff k hk) I S q a := by
  rfl

/-- A discrete Section 3 choice is feasible and maximizes the `psi_k` score. -/
def occurrenceDiscreteBalanceChoice
    (k : ℕ) (hk : 0 < k)
    (I : PaperInstance Advertiser Query)
    (S : OccurrenceState Advertiser Query) (q : Query) (a : Advertiser) : Prop :=
  occurrenceCanAssign I S q a ∧
    ∀ b, occurrenceCanAssign I S q b →
      occurrenceDiscreteScore k hk I S q b ≤ occurrenceDiscreteScore k hk I S q a

/-- A finite Theorem 8 choice is feasible and maximizes its geometric dual score. -/
def occurrenceTheorem8DiscreteChoice
    (k : ℕ) (hk : 0 < k)
    (I : PaperInstance Advertiser Query)
    (S : OccurrenceState Advertiser Query) (q : Query) (a : Advertiser) : Prop :=
  occurrenceCanAssign I S q a ∧
    ∀ b, occurrenceCanAssign I S q b →
      occurrenceTheorem8DiscreteScore k hk I S q b ≤
        occurrenceTheorem8DiscreteScore k hk I S q a

/-- The actual finite scan used for one continuous Balance/MSVV decision. -/
noncomputable def balanceScan
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (S : OccurrenceState Advertiser Query) (q : Query) :
    FiniteMaxScanResult Advertiser :=
  finiteMaxScan (occurrenceCanAssign I S q) (occurrenceBalanceScore I S q)
    (Finset.univ : Finset Advertiser).toList

/--
The deterministic finite scan for the source algorithm with tradeoff `psi`.
It makes the source's resulting allocation, and hence its final type counts,
an explicit function of the instance, arrival history, and tradeoff.
-/
noncomputable def tradeoffScan
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (psi : ℝ → ℝ) (I : PaperInstance Advertiser Query)
    (S : OccurrenceState Advertiser Query) (q : Query) :
    FiniteMaxScanResult Advertiser :=
  finiteMaxScan (occurrenceCanAssign I S q) (occurrenceTradeoffScore psi I S q)
    (Finset.univ : Finset Advertiser).toList

/-- The actual finite scan used for one discrete Section 3 decision. -/
noncomputable def discreteBalanceScan
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (k : ℕ) (hk : 0 < k)
    (I : PaperInstance Advertiser Query)
    (S : OccurrenceState Advertiser Query) (q : Query) :
    FiniteMaxScanResult Advertiser :=
  finiteMaxScan (occurrenceCanAssign I S q) (occurrenceDiscreteScore k hk I S q)
    (Finset.univ : Finset Advertiser).toList

/-- The finite scan for the geometric tradeoff induced by Theorem 8. -/
noncomputable def theorem8DiscreteScan
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (k : ℕ) (hk : 0 < k)
    (I : PaperInstance Advertiser Query)
    (S : OccurrenceState Advertiser Query) (q : Query) :
    FiniteMaxScanResult Advertiser :=
  finiteMaxScan (occurrenceCanAssign I S q)
    (occurrenceTheorem8DiscreteScore k hk I S q)
    (Finset.univ : Finset Advertiser).toList

/-- The finite Theorem 8 scan is the generic source scan at its dual tradeoff. -/
theorem theorem8DiscreteScan_eq_tradeoffScan
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (k : ℕ) (hk : 0 < k)
    (I : PaperInstance Advertiser Query)
    (S : OccurrenceState Advertiser Query) (q : Query) :
    theorem8DiscreteScan k hk I S q =
      tradeoffScan (theorem8DiscreteSlabTradeoff k hk) I S q := by
  rfl

/-- Apply one already-computed finite scan result and thread both costs. -/
noncomputable def applyScanDecision
    {Advertiser Query : Type*} [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (S : OccurrenceState Advertiser Query) (q : Query)
    (scan : FiniteMaxScanResult Advertiser) :
    OccurrenceState Advertiser Query :=
  let charge := fun a => I.bid a q
  { spent := fun a =>
      match scan.winner with
      | none => S.spent a
      | some winner => if a = winner then S.spent a + charge winner else S.spent a
    revenue :=
      match scan.winner with
      | none => S.revenue
      | some winner => S.revenue + charge winner
    decisionsRev :=
      ⟨q, scan.winner, S.spent⟩ :: S.decisionsRev
    candidateTests := S.candidateTests + scan.candidateTests
    scoreComparisons := S.scoreComparisons + scan.scoreComparisons }

/-- A scan whose winner is affordable preserves occurrence-state feasibility. -/
theorem applyScanDecision_preserves_budget_feasible
    [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (S : OccurrenceState Advertiser Query) (q : Query)
    (scan : FiniteMaxScanResult Advertiser)
    (hstate : occurrenceStateBudgetFeasible I S)
    (hscan : ∀ a, scan.winner = some a → occurrenceCanAssign I S q a) :
    occurrenceStateBudgetFeasible I (applyScanDecision I S q scan) := by
  intro a
  cases hwinner : scan.winner with
  | none =>
      simpa [applyScanDecision, hwinner] using hstate a
  | some winner =>
      by_cases howner : a = winner
      · subst a
        simpa [applyScanDecision, hwinner] using hscan winner hwinner
      · simpa [applyScanDecision, hwinner, howner] using hstate a

/-- With nonnegative bids, applying a scan preserves nonnegative spend. -/
theorem applyScanDecision_preserves_nonnegative_spend
    [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (S : OccurrenceState Advertiser Query) (q : Query)
    (scan : FiniteMaxScanResult Advertiser)
    (hstate : occurrenceStateNonnegativeSpend S)
    (hbid : I.NonnegativeBids) :
    occurrenceStateNonnegativeSpend (applyScanDecision I S q scan) := by
  intro a
  cases hwinner : scan.winner with
  | none =>
      simpa [applyScanDecision, hwinner] using hstate a
  | some winner =>
      by_cases howner : a = winner
      · subst a
        simpa [applyScanDecision, hwinner] using
          add_nonneg (hstate winner) (hbid winner q)
      · simpa [applyScanDecision, hwinner, howner] using hstate a

/-- With nonnegative bids, applying a scan never lowers any bidder's spend. -/
theorem applyScanDecision_spent_le
    [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (S : OccurrenceState Advertiser Query) (q : Query)
    (scan : FiniteMaxScanResult Advertiser) (hbid : I.NonnegativeBids)
    (a : Advertiser) :
    S.spent a ≤ (applyScanDecision I S q scan).spent a := by
  cases hwinner : scan.winner with
  | none => simp [applyScanDecision, hwinner]
  | some winner =>
      by_cases howner : a = winner
      · subst a
        simpa [applyScanDecision, hwinner] using
          (show S.spent winner ≤ S.spent winner + I.bid winner q by
            linarith [hbid winner q])
      · simp [applyScanDecision, hwinner, howner]

/-- Applying a scan appends precisely the arriving query to the decision ledger. -/
theorem applyScanDecision_decisionQueries
    [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (S : OccurrenceState Advertiser Query) (q : Query)
    (scan : FiniteMaxScanResult Advertiser) :
    occurrenceDecisionQueries (applyScanDecision I S q scan) =
      occurrenceDecisionQueries S ++ [q] := by
  simp [occurrenceDecisionQueries, applyScanDecision]

/-- A scan changes aggregate spend by exactly the revenue charged to its winner. -/
theorem applyScanDecision_totalSpend
    [Fintype Advertiser] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (S : OccurrenceState Advertiser Query) (q : Query)
    (scan : FiniteMaxScanResult Advertiser) :
    occurrenceStateTotalSpend (applyScanDecision I S q scan) =
      occurrenceStateTotalSpend S +
        match scan.winner with
        | none => 0
        | some a => I.bid a q := by
  cases hwinner : scan.winner with
  | none => simp [occurrenceStateTotalSpend, applyScanDecision, hwinner]
  | some winner =>
      have hsum :
          (∑ a : Advertiser,
            if a = winner then S.spent a + I.bid winner q else S.spent a) =
            (∑ a : Advertiser, S.spent a) + I.bid winner q := by
        calc
          (∑ a : Advertiser,
              if a = winner then S.spent a + I.bid winner q else S.spent a) =
            ∑ a : Advertiser, (S.spent a +
              if a = winner then I.bid winner q else 0) := by
                apply Finset.sum_congr rfl
                intro a _
                by_cases ha : a = winner <;> simp [ha]
          _ = (∑ a : Advertiser, S.spent a) +
              ∑ a : Advertiser, if a = winner then I.bid winner q else 0 := by
                rw [Finset.sum_add_distrib]
          _ = (∑ a : Advertiser, S.spent a) + I.bid winner q := by
                rw [Fintype.sum_ite_eq']
      simpa [occurrenceStateTotalSpend, applyScanDecision, hwinner] using hsum

/-- If aggregate spend equals revenue before a scan, it does so afterwards. -/
theorem applyScanDecision_totalSpend_eq_revenue
    [Fintype Advertiser] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (S : OccurrenceState Advertiser Query) (q : Query)
    (scan : FiniteMaxScanResult Advertiser)
    (haccounting : occurrenceStateTotalSpend S = S.revenue) :
    occurrenceStateTotalSpend (applyScanDecision I S q scan) =
      (applyScanDecision I S q scan).revenue := by
  cases hwinner : scan.winner with
  | none => simpa [applyScanDecision, hwinner] using haccounting
  | some winner =>
      have htotal := applyScanDecision_totalSpend I S q scan
      have htotal' : occurrenceStateTotalSpend (applyScanDecision I S q scan) =
          occurrenceStateTotalSpend S + I.bid winner q := by
        simpa [hwinner] using htotal
      calc
        occurrenceStateTotalSpend (applyScanDecision I S q scan) =
            occurrenceStateTotalSpend S + I.bid winner q := htotal'
        _ = S.revenue + I.bid winner q := by rw [haccounting]
        _ = (applyScanDecision I S q scan).revenue := by
          simp [applyScanDecision, hwinner]

/-- One occurrence step of the continuous Balance/MSVV runner. -/
noncomputable def balanceStep
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (S : OccurrenceState Advertiser Query) (q : Query) :
    OccurrenceState Advertiser Query :=
  applyScanDecision I S q (balanceScan I S q)

/-- One occurrence step of the source algorithm using the supplied tradeoff. -/
noncomputable def tradeoffStep
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (psi : ℝ → ℝ) (I : PaperInstance Advertiser Query)
    (S : OccurrenceState Advertiser Query) (q : Query) :
    OccurrenceState Advertiser Query :=
  applyScanDecision I S q (tradeoffScan psi I S q)

/-- One occurrence step of the discrete Section 3 runner. -/
noncomputable def discreteBalanceStep
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (k : ℕ) (hk : 0 < k)
    (I : PaperInstance Advertiser Query)
    (S : OccurrenceState Advertiser Query) (q : Query) :
    OccurrenceState Advertiser Query :=
  applyScanDecision I S q (discreteBalanceScan k hk I S q)

/-- One occurrence step of the finite geometric Theorem 8 runner. -/
noncomputable def theorem8DiscreteStep
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (k : ℕ) (hk : 0 < k)
    (I : PaperInstance Advertiser Query)
    (S : OccurrenceState Advertiser Query) (q : Query) :
    OccurrenceState Advertiser Query :=
  applyScanDecision I S q (theorem8DiscreteScan k hk I S q)

/-- A Theorem 8 step is the generic source step at its dual tradeoff. -/
theorem theorem8DiscreteStep_eq_tradeoffStep
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (k : ℕ) (hk : 0 < k)
    (I : PaperInstance Advertiser Query)
    (S : OccurrenceState Advertiser Query) (q : Query) :
    theorem8DiscreteStep k hk I S q =
      tradeoffStep (theorem8DiscreteSlabTradeoff k hk) I S q := by
  rfl

/-- Execute a step function on every occurrence, including repeated query words. -/
noncomputable def runOccurrencesFrom
    (step : OccurrenceState Advertiser Query → Query →
      OccurrenceState Advertiser Query) :
    OccurrenceState Advertiser Query → List Query →
      OccurrenceState Advertiser Query
  | S, [] => S
  | S, q :: qs => runOccurrencesFrom step (step S q) qs

/-- Executing a concatenated occurrence history is execution of its prefix then suffix. -/
theorem runOccurrencesFrom_append
    (step : OccurrenceState Advertiser Query → Query →
      OccurrenceState Advertiser Query)
    (before after : List Query) (S : OccurrenceState Advertiser Query) :
    runOccurrencesFrom step S (before ++ after) =
      runOccurrencesFrom step (runOccurrencesFrom step S before) after := by
  induction before generalizing S with
  | nil => simp [runOccurrencesFrom]
  | cons q qs ih =>
      simp only [List.cons_append, runOccurrencesFrom]
      exact ih (step S q)

/--
Any step that does not lower individual spend leaves every initial spend below
the final spend.  This provides the chronological monotonicity needed when a
final type is used to reason about an earlier arrival.
-/
theorem runOccurrencesFrom_spent_le
    (step : OccurrenceState Advertiser Query → Query →
      OccurrenceState Advertiser Query)
    (hstep : ∀ S q a, S.spent a ≤ (step S q).spent a)
    (history : List Query) (S : OccurrenceState Advertiser Query)
    (a : Advertiser) :
    S.spent a ≤ (runOccurrencesFrom step S history).spent a := by
  induction history generalizing S with
  | nil => simp [runOccurrencesFrom]
  | cons q qs ih =>
      rw [runOccurrencesFrom]
      exact (hstep S q a).trans (ih (step S q))

/-- Any step function that preserves budgets yields a budget-feasible run. -/
theorem runOccurrencesFrom_preserves_budget_feasible
    (I : PaperInstance Advertiser Query)
    (step : OccurrenceState Advertiser Query → Query →
      OccurrenceState Advertiser Query)
    (hstep : ∀ S q, occurrenceStateBudgetFeasible I S →
      occurrenceStateBudgetFeasible I (step S q))
    (history : List Query) (S : OccurrenceState Advertiser Query)
    (hstate : occurrenceStateBudgetFeasible I S) :
    occurrenceStateBudgetFeasible I (runOccurrencesFrom step S history) := by
  induction history generalizing S with
  | nil => simpa [runOccurrencesFrom]
  | cons q qs ih =>
      rw [runOccurrencesFrom]
      exact ih (step S q) (hstep S q hstate)

/-- Any step function preserving nonnegative spend yields a nonnegative run. -/
theorem runOccurrencesFrom_preserves_nonnegative_spend
    (step : OccurrenceState Advertiser Query → Query →
      OccurrenceState Advertiser Query)
    (hstep : ∀ S q, occurrenceStateNonnegativeSpend S →
      occurrenceStateNonnegativeSpend (step S q))
    (history : List Query) (S : OccurrenceState Advertiser Query)
    (hstate : occurrenceStateNonnegativeSpend S) :
    occurrenceStateNonnegativeSpend (runOccurrencesFrom step S history) := by
  induction history generalizing S with
  | nil => simpa [runOccurrencesFrom]
  | cons q qs ih =>
      rw [runOccurrencesFrom]
      exact ih (step S q) (hstep S q hstate)

/-- A stepwise ledger records every arrival once and in chronological order. -/
theorem runOccurrencesFrom_decisionQueries
    (step : OccurrenceState Advertiser Query → Query →
      OccurrenceState Advertiser Query)
    (hstep : ∀ S q,
      occurrenceDecisionQueries (step S q) = occurrenceDecisionQueries S ++ [q])
    (history : List Query) (S : OccurrenceState Advertiser Query) :
    occurrenceDecisionQueries (runOccurrencesFrom step S history) =
      occurrenceDecisionQueries S ++ history := by
  induction history generalizing S with
  | nil => simp [runOccurrencesFrom]
  | cons q qs ih =>
      rw [runOccurrencesFrom, ih, hstep]
      simp only [List.append_assoc, List.cons_append, List.nil_append]

/-- Source-faithful continuous Balance/MSVV run. -/
noncomputable def runBalanceOccurrences
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query) (history : List Query) :
    OccurrenceState Advertiser Query :=
  runOccurrencesFrom (balanceStep I) initialOccurrenceState history

/--
The Section 5 run for an arbitrary tradeoff `psi` on a concrete AdWords
instance and finite arrival history.
-/
noncomputable def runTradeoffOccurrences
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (psi : ℝ → ℝ) (I : PaperInstance Advertiser Query) (history : List Query) :
    OccurrenceState Advertiser Query :=
  runOccurrencesFrom (tradeoffStep psi I) initialOccurrenceState history

/-- Source-faithful discrete Section 3 run. -/
noncomputable def runDiscreteBalanceOccurrences
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (k : ℕ) (hk : 0 < k)
    (I : PaperInstance Advertiser Query) (history : List Query) :
    OccurrenceState Advertiser Query :=
  runOccurrencesFrom (discreteBalanceStep k hk I) initialOccurrenceState history

/-- Source-faithful run of the finite geometric tradeoff from Theorem 8. -/
noncomputable def runTheorem8DiscreteOccurrences
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (k : ℕ) (hk : 0 < k)
    (I : PaperInstance Advertiser Query) (history : List Query) :
    OccurrenceState Advertiser Query :=
  runOccurrencesFrom (theorem8DiscreteStep k hk I) initialOccurrenceState history

/-- The actual source-runner state immediately before occurrence `t`. -/
noncomputable def theorem8StateBefore
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (k : ℕ) (hk : 0 < k) (I : PaperInstance Advertiser Query)
    (history : List Query) (t : Fin history.length) :
    OccurrenceState Advertiser Query :=
  runOccurrencesFrom (theorem8DiscreteStep k hk I) initialOccurrenceState
    (history.take t.val)

/--
The state immediately before one occurrence in the Section 4 continuous
BALANCE execution.  This is the actual chronological runner state, not a
caller-supplied allocation snapshot.
-/
noncomputable def balanceStateBefore
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query) (history : List Query)
    (t : Fin history.length) : OccurrenceState Advertiser Query :=
  runOccurrencesFrom (balanceStep I) initialOccurrenceState (history.take t.val)

/--
Every continuous-BALANCE pre-occurrence spend is bounded by the final spend of
the same actual run.  This is the chronological monotonicity bridge used when
Section 4 applies a final bidder type at an earlier OPT occurrence.
-/
theorem balanceStateBefore_spent_le_final
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query) (history : List Query)
    (t : Fin history.length) (hbid : I.NonnegativeBids) (a : Advertiser) :
    (balanceStateBefore I history t).spent a ≤
      (runBalanceOccurrences I history).spent a := by
  let step := balanceStep I
  let S := runOccurrencesFrom step initialOccurrenceState (history.take t.val)
  have hhistory : history.take t.val ++ history.drop t.val = history :=
    List.take_append_drop t.val history
  have hsplit : runOccurrencesFrom step initialOccurrenceState history =
      runOccurrencesFrom step S (history.drop t.val) := by
    calc
      runOccurrencesFrom step initialOccurrenceState history =
          runOccurrencesFrom step initialOccurrenceState
            (history.take t.val ++ history.drop t.val) := by rw [hhistory]
      _ = runOccurrencesFrom step
          (runOccurrencesFrom step initialOccurrenceState (history.take t.val))
          (history.drop t.val) :=
        runOccurrencesFrom_append step (history.take t.val) (history.drop t.val)
          initialOccurrenceState
      _ = runOccurrencesFrom step S (history.drop t.val) := by rfl
  change S.spent a ≤ (runOccurrencesFrom step initialOccurrenceState history).spent a
  rw [hsplit]
  apply runOccurrencesFrom_spent_le (balanceStep I)
  intro T q b
  exact applyScanDecision_spent_le I T q (balanceScan I T q) hbid b

/-- The active source slab of bidder `a` immediately before occurrence `t`. -/
noncomputable def theorem8CurrentSlabAt
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (k : ℕ) (hk : 0 < k) (I : PaperInstance Advertiser Query)
    (history : List Query) (t : Fin history.length) (a : Advertiser) : Fin k :=
  activeBudgetSlab k hk ((theorem8StateBefore k hk I history t).spent a)
    (I.budget a)

/--
Along a source tradeoff execution, each bidder's spend is chronologically
nondecreasing when bids are nonnegative.
-/
theorem runTradeoffOccurrencesFrom_spent_le
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (psi : ℝ → ℝ) (I : PaperInstance Advertiser Query)
    (history : List Query) (S : OccurrenceState Advertiser Query)
    (hbid : I.NonnegativeBids) (a : Advertiser) :
    S.spent a ≤
      (runOccurrencesFrom (tradeoffStep psi I) S history).spent a := by
  apply runOccurrencesFrom_spent_le (tradeoffStep psi I)
  intro T q b
  exact applyScanDecision_spent_le I T q (tradeoffScan psi I T q) hbid b

/--
The geometric Theorem 8 execution has the same chronological spend
monotonicity from any intermediate occurrence state.
-/
theorem runTheorem8DiscreteOccurrencesFrom_spent_le
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (k : ℕ) (hk : 0 < k) (I : PaperInstance Advertiser Query)
    (history : List Query) (S : OccurrenceState Advertiser Query)
    (hbid : I.NonnegativeBids) (a : Advertiser) :
    S.spent a ≤
      (runOccurrencesFrom (theorem8DiscreteStep k hk I) S history).spent a := by
  simpa [theorem8DiscreteStep_eq_tradeoffStep] using
    runTradeoffOccurrencesFrom_spent_le
      (theorem8DiscreteSlabTradeoff k hk) I history S hbid a

/--
At every intermediate state of a finite Theorem 8 execution, a bidder's
current active slab is no later than that bidder's final active slab.  This
uses the runner's actual chronological state, not a stipulated trajectory.
-/
theorem runTheorem8DiscreteOccurrencesFrom_currentSlab_le_finalActiveSlab
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (k : ℕ) (hk : 0 < k) (I : PaperInstance Advertiser Query)
    (history : List Query) (S : OccurrenceState Advertiser Query)
    (hbid : I.NonnegativeBids) (hbudget : I.PositiveBudgets)
    (a : Advertiser) :
    activeBudgetSlab k hk (S.spent a) (I.budget a) ≤
      activeBudgetSlab k hk
        ((runOccurrencesFrom (theorem8DiscreteStep k hk I) S history).spent a)
        (I.budget a) := by
  apply activeBudgetSlab_monotone_spent k hk (I.budget a) (hbudget a)
  exact runTheorem8DiscreteOccurrencesFrom_spent_le
    k hk I history S hbid a

/-- Every actual pre-occurrence state has spend no larger than the full run's final spend. -/
theorem theorem8StateBefore_spent_le_final
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (k : ℕ) (hk : 0 < k) (I : PaperInstance Advertiser Query)
    (history : List Query) (t : Fin history.length)
    (hbid : I.NonnegativeBids) (a : Advertiser) :
    (theorem8StateBefore k hk I history t).spent a ≤
      (runTheorem8DiscreteOccurrences k hk I history).spent a := by
  let step := theorem8DiscreteStep k hk I
  let S := runOccurrencesFrom step initialOccurrenceState (history.take t.val)
  have hhistory : history.take t.val ++ history.drop t.val = history :=
    List.take_append_drop t.val history
  have hsplit : runOccurrencesFrom step initialOccurrenceState history =
      runOccurrencesFrom step S (history.drop t.val) := by
    calc
      runOccurrencesFrom step initialOccurrenceState history =
          runOccurrencesFrom step initialOccurrenceState
            (history.take t.val ++ history.drop t.val) := by rw [hhistory]
      _ = runOccurrencesFrom step
          (runOccurrencesFrom step initialOccurrenceState (history.take t.val))
          (history.drop t.val) :=
        runOccurrencesFrom_append step (history.take t.val) (history.drop t.val)
          initialOccurrenceState
      _ = runOccurrencesFrom step S (history.drop t.val) := by rfl
  change S.spent a ≤ (runOccurrencesFrom step initialOccurrenceState history).spent a
  rw [hsplit]
  exact runTheorem8DiscreteOccurrencesFrom_spent_le
    k hk I (history.drop t.val) S hbid a

/-- The actual pre-occurrence active slab is no later than the full run's final active slab. -/
theorem theorem8CurrentSlabAt_le_finalActiveSlab
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (k : ℕ) (hk : 0 < k) (I : PaperInstance Advertiser Query)
    (history : List Query) (t : Fin history.length)
    (hbid : I.NonnegativeBids) (hbudget : I.PositiveBudgets)
    (a : Advertiser) :
    theorem8CurrentSlabAt k hk I history t a ≤
      activeBudgetSlab k hk
        ((runTheorem8DiscreteOccurrences k hk I history).spent a) (I.budget a) := by
  apply activeBudgetSlab_monotone_spent k hk (I.budget a) (hbudget a)
  exact theorem8StateBefore_spent_le_final k hk I history t hbid a

/-- The actual Theorem 8 run is the generic tradeoff run at its dual weights. -/
theorem runTheorem8DiscreteOccurrences_eq_tradeoffRun
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (k : ℕ) (hk : 0 < k)
    (I : PaperInstance Advertiser Query) (history : List Query) :
    runTheorem8DiscreteOccurrences k hk I history =
      runTradeoffOccurrences (theorem8DiscreteSlabTradeoff k hk) I history := by
  rfl

/-- The generic tradeoff runner's ledger covers its input history exactly. -/
theorem runTradeoffOccurrences_decisionQueries
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (psi : ℝ → ℝ) (I : PaperInstance Advertiser Query) (history : List Query) :
    occurrenceDecisionQueries (runTradeoffOccurrences psi I history) = history := by
  unfold runTradeoffOccurrences
  simpa [occurrenceDecisionQueries, initialOccurrenceState] using
    runOccurrencesFrom_decisionQueries (tradeoffStep psi I)
      (fun S q => applyScanDecision_decisionQueries I S q (tradeoffScan psi I S q))
      history initialOccurrenceState

/-- The finite Theorem 8 runner's decision ledger covers every arrival exactly once. -/
theorem runTheorem8DiscreteOccurrences_decisionQueries
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (k : ℕ) (hk : 0 < k) (I : PaperInstance Advertiser Query)
    (history : List Query) :
    occurrenceDecisionQueries (runTheorem8DiscreteOccurrences k hk I history) = history := by
  rw [runTheorem8DiscreteOccurrences_eq_tradeoffRun]
  exact runTradeoffOccurrences_decisionQueries
    (theorem8DiscreteSlabTradeoff k hk) I history

/-- The generic tradeoff runner records total advertiser spend as its revenue. -/
theorem runTradeoffOccurrences_totalSpend_eq_revenue
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (psi : ℝ → ℝ) (I : PaperInstance Advertiser Query) (history : List Query) :
    occurrenceStateTotalSpend (runTradeoffOccurrences psi I history) =
      (runTradeoffOccurrences psi I history).revenue := by
  unfold runTradeoffOccurrences
  have hgeneral : ∀ (S : OccurrenceState Advertiser Query),
      occurrenceStateTotalSpend S = S.revenue →
        occurrenceStateTotalSpend (runOccurrencesFrom (tradeoffStep psi I) S history) =
          (runOccurrencesFrom (tradeoffStep psi I) S history).revenue := by
    induction history with
    | nil =>
        intro S hS
        simpa [runOccurrencesFrom] using hS
    | cons q qs ih =>
        intro S hS
        rw [runOccurrencesFrom]
        apply ih
        exact applyScanDecision_totalSpend_eq_revenue
          I S q (tradeoffScan psi I S q) hS
  apply hgeneral initialOccurrenceState
  simp [occurrenceStateTotalSpend, initialOccurrenceState]

/-- The finite Theorem 8 runner records total advertiser spend as its revenue. -/
theorem runTheorem8DiscreteOccurrences_totalSpend_eq_revenue
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (k : ℕ) (hk : 0 < k) (I : PaperInstance Advertiser Query)
    (history : List Query) :
    occurrenceStateTotalSpend (runTheorem8DiscreteOccurrences k hk I history) =
      (runTheorem8DiscreteOccurrences k hk I history).revenue := by
  rw [runTheorem8DiscreteOccurrences_eq_tradeoffRun]
  exact runTradeoffOccurrences_totalSpend_eq_revenue
    (theorem8DiscreteSlabTradeoff k hk) I history

/-- Any selected generic-tradeoff scan winner is affordable. -/
theorem tradeoffScan_winner_feasible
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (psi : ℝ → ℝ) (I : PaperInstance Advertiser Query)
    (S : OccurrenceState Advertiser Query) (q : Query) (a : Advertiser)
    (hchoice : (tradeoffScan psi I S q).winner = some a) :
    occurrenceCanAssign I S q a := by
  classical
  have hspec :=
    (finiteMaxScan_winner_spec
      (occurrenceCanAssign I S q) (occurrenceTradeoffScore psi I S q)
      (Finset.univ : Finset Advertiser).toList).2 a hchoice
  exact hspec.2.1

/-- A generic tradeoff step preserves every advertiser's budget bound. -/
theorem tradeoffStep_preserves_budget_feasible
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (psi : ℝ → ℝ) (I : PaperInstance Advertiser Query)
    (S : OccurrenceState Advertiser Query) (q : Query)
    (hstate : occurrenceStateBudgetFeasible I S) :
    occurrenceStateBudgetFeasible I (tradeoffStep psi I S q) := by
  apply applyScanDecision_preserves_budget_feasible I S q
    (tradeoffScan psi I S q) hstate
  intro a hchoice
  exact tradeoffScan_winner_feasible psi I S q a hchoice

/-- A generic tradeoff step preserves nonnegative spend under nonnegative bids. -/
theorem tradeoffStep_preserves_nonnegative_spend
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (psi : ℝ → ℝ) (I : PaperInstance Advertiser Query)
    (S : OccurrenceState Advertiser Query) (q : Query)
    (hstate : occurrenceStateNonnegativeSpend S)
    (hbid : I.NonnegativeBids) :
    occurrenceStateNonnegativeSpend (tradeoffStep psi I S q) := by
  exact applyScanDecision_preserves_nonnegative_spend
    I S q (tradeoffScan psi I S q) hstate hbid

/-- The actual generic-tradeoff execution never violates a budget. -/
theorem runTradeoffOccurrences_budget_feasible
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (psi : ℝ → ℝ) (I : PaperInstance Advertiser Query)
    (history : List Query) (hbudget : I.NonnegativeBudgets) :
    occurrenceStateBudgetFeasible I (runTradeoffOccurrences psi I history) := by
  unfold runTradeoffOccurrences
  apply runOccurrencesFrom_preserves_budget_feasible I (tradeoffStep psi I)
  · intro S q hstate
    exact tradeoffStep_preserves_budget_feasible psi I S q hstate
  · exact initialOccurrenceState_budget_feasible I hbudget

/-- The actual generic-tradeoff execution has nonnegative spend throughout. -/
theorem runTradeoffOccurrences_nonnegative_spend
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (psi : ℝ → ℝ) (I : PaperInstance Advertiser Query)
    (history : List Query) (hbid : I.NonnegativeBids) :
    occurrenceStateNonnegativeSpend (runTradeoffOccurrences psi I history) := by
  unfold runTradeoffOccurrences
  apply runOccurrencesFrom_preserves_nonnegative_spend (tradeoffStep psi I)
  · intro S q hstate
    exact tradeoffStep_preserves_nonnegative_spend psi I S q hstate hbid
  · exact initialOccurrenceState_nonnegative_spend

/-- The source-faithful finite Theorem 8 execution never violates a budget. -/
theorem runTheorem8DiscreteOccurrences_budget_feasible
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (k : ℕ) (hk : 0 < k) (I : PaperInstance Advertiser Query)
    (history : List Query) (hbudget : I.NonnegativeBudgets) :
    occurrenceStateBudgetFeasible I
      (runTheorem8DiscreteOccurrences k hk I history) := by
  rw [runTheorem8DiscreteOccurrences_eq_tradeoffRun]
  exact runTradeoffOccurrences_budget_feasible
    (theorem8DiscreteSlabTradeoff k hk) I history hbudget

/-- The source-faithful finite Theorem 8 execution has nonnegative spend. -/
theorem runTheorem8DiscreteOccurrences_nonnegative_spend
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (k : ℕ) (hk : 0 < k) (I : PaperInstance Advertiser Query)
    (history : List Query) (hbid : I.NonnegativeBids) :
    occurrenceStateNonnegativeSpend
      (runTheorem8DiscreteOccurrences k hk I history) := by
  rw [runTheorem8DiscreteOccurrences_eq_tradeoffRun]
  exact runTradeoffOccurrences_nonnegative_spend
    (theorem8DiscreteSlabTradeoff k hk) I history hbid

/-- The continuous scan's winner is feasible and score-maximal among all advertisers. -/
theorem balanceScan_winner_is_balance_choice
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (S : OccurrenceState Advertiser Query) (q : Query) (a : Advertiser)
    (hchoice : (balanceScan I S q).winner = some a) :
    occurrenceCanAssign I S q a ∧
      ∀ b, occurrenceCanAssign I S q b →
        occurrenceBalanceScore I S q b ≤ occurrenceBalanceScore I S q a := by
  classical
  have hspec :=
    (finiteMaxScan_winner_spec
      (occurrenceCanAssign I S q) (occurrenceBalanceScore I S q)
      (Finset.univ : Finset Advertiser).toList).2 a hchoice
  exact ⟨hspec.2.1, fun b hb => hspec.2.2 b (by simp) hb⟩

/-- The discrete finite scan realizes its stated feasible `psi_k` argmax rule. -/
theorem discreteBalanceScan_winner_is_discrete_choice
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (k : ℕ) (hk : 0 < k)
    (I : PaperInstance Advertiser Query)
    (S : OccurrenceState Advertiser Query) (q : Query) (a : Advertiser)
    (hchoice : (discreteBalanceScan k hk I S q).winner = some a) :
    occurrenceDiscreteBalanceChoice k hk I S q a := by
  classical
  have hspec :=
    (finiteMaxScan_winner_spec
      (occurrenceCanAssign I S q) (occurrenceDiscreteScore k hk I S q)
      (Finset.univ : Finset Advertiser).toList).2 a hchoice
  exact ⟨hspec.2.1, fun b hb => hspec.2.2 b (by simp) hb⟩

/-- The geometric finite scan realizes the source-faithful Theorem 8 argmax. -/
theorem theorem8DiscreteScan_winner_is_choice
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (k : ℕ) (hk : 0 < k)
    (I : PaperInstance Advertiser Query)
    (S : OccurrenceState Advertiser Query) (q : Query) (a : Advertiser)
    (hchoice : (theorem8DiscreteScan k hk I S q).winner = some a) :
    occurrenceTheorem8DiscreteChoice k hk I S q a := by
  classical
  have hspec :=
    (finiteMaxScan_winner_spec
      (occurrenceCanAssign I S q)
      (occurrenceTheorem8DiscreteScore k hk I S q)
      (Finset.univ : Finset Advertiser).toList).2 a hchoice
  exact ⟨hspec.2.1, fun b hb => hspec.2.2 b (by simp) hb⟩

/--
The split-payment potential of a complete occurrence state, at arbitrary
finite slab weights.  This is the state-level version of the Section 6
split-payment accounting.
-/
noncomputable def theorem8StateSlabPotential
    {Advertiser Query : Type*} [Fintype Advertiser]
    (k : ℕ) (I : PaperInstance Advertiser Query) (psi : Fin k → ℝ)
    (S : OccurrenceState Advertiser Query) : ℝ :=
  ∑ a : Advertiser, theorem8SlabPotential k (I.budget a) psi (S.spent a)

/--
One actual finite Theorem 8 scan charges at most its increase in
split-payment potential, plus one `1 / k` share of the winning bid.  Thus a
payment may cross a slab boundary, without imposing a no-straddling condition
on the source runner.
-/
theorem theorem8DiscreteScan_weighted_charge_le_potential_increment
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (k : ℕ) (hk : 0 < k) (I : PaperInstance Advertiser Query)
    (S : OccurrenceState Advertiser Query) (q : Query)
    (hnonneg : occurrenceStateNonnegativeSpend S)
    (hfeasible : occurrenceStateBudgetFeasible I S) (hbudget : I.PositiveBudgets)
    (hbid : I.NonnegativeBids)
    (hsmall : ∀ a q, I.bid a q ≤ I.budget a / (k : ℝ))
    (winner : Advertiser)
    (hwin : (theorem8DiscreteScan k hk I S q).winner = some winner) :
    I.bid winner q * theorem8DiscreteTradeoff k
        (activeBudgetSlab k hk (S.spent winner) (I.budget winner)) ≤
      theorem8StateSlabPotential k I (theorem8DiscreteTradeoff k)
        (applyScanDecision I S q (theorem8DiscreteScan k hk I S q)) -
        theorem8StateSlabPotential k I (theorem8DiscreteTradeoff k) S +
          I.bid winner q / (k : ℝ) := by
  classical
  let scan := theorem8DiscreteScan k hk I S q
  let S' := applyScanDecision I S q scan
  let i := activeBudgetSlab k hk (S.spent winner) (I.budget winner)
  let p := I.bid winner q
  have hchoice : scan.winner = some winner := hwin
  have hcan : occurrenceCanAssign I S q winner :=
    (theorem8DiscreteScan_winner_is_choice k hk I S q winner hwin).1
  have hbounds := activeBudgetSlab_bounds hk (S.spent winner) (I.budget winner)
    (hnonneg winner) (hbudget winner) (hfeasible winner)
  have hscalar := theorem8SlabPotential_increment_le_start_weight
    (I.budget winner) (S.spent winner) (I.bid winner q)
    (theorem8DiscreteTradeoff k)
    (activeBudgetSlab k hk (S.spent winner) (I.budget winner))
    (hbudget winner).le hbounds.1 hbounds.2 (hbid winner q)
    (hsmall winner q) hcan
    (fun j hj => theorem8DiscreteTradeoff_drop_to_succ_le_one_div j hj)
  have hstatePotential :
      theorem8StateSlabPotential k I (theorem8DiscreteTradeoff k) S' =
        theorem8StateSlabPotential k I (theorem8DiscreteTradeoff k) S -
          theorem8SlabPotential k (I.budget winner) (theorem8DiscreteTradeoff k)
            (S.spent winner) +
          theorem8SlabPotential k (I.budget winner) (theorem8DiscreteTradeoff k)
            (S.spent winner + I.bid winner q) := by
    unfold theorem8StateSlabPotential
    dsimp [S', scan]
    simp only [applyScanDecision]
    rw [hwin]
    calc
      (∑ a : Advertiser,
          theorem8SlabPotential k (I.budget a) (theorem8DiscreteTradeoff k)
            (if a = winner then S.spent a + I.bid winner q else S.spent a)) =
          ∑ a : Advertiser,
            (theorem8SlabPotential k (I.budget a) (theorem8DiscreteTradeoff k)
              (S.spent a) +
              if a = winner then
                theorem8SlabPotential k (I.budget winner) (theorem8DiscreteTradeoff k)
                  (S.spent winner + I.bid winner q) -
                  theorem8SlabPotential k (I.budget winner) (theorem8DiscreteTradeoff k)
                    (S.spent winner)
              else 0) := by
            apply Finset.sum_congr rfl
            intro a _
            by_cases ha : a = winner
            · subst a
              simp
            · simp [ha]
      _ = (∑ a : Advertiser,
            theorem8SlabPotential k (I.budget a) (theorem8DiscreteTradeoff k)
              (S.spent a)) +
          (theorem8SlabPotential k (I.budget winner) (theorem8DiscreteTradeoff k)
              (S.spent winner + I.bid winner q) -
            theorem8SlabPotential k (I.budget winner) (theorem8DiscreteTradeoff k)
              (S.spent winner)) := by
            rw [Finset.sum_add_distrib]
            simp
      _ = _ := by ring
  calc
    I.bid winner q * theorem8DiscreteTradeoff k
        (activeBudgetSlab k hk (S.spent winner) (I.budget winner)) ≤
        theorem8SlabPotential k (I.budget winner) (theorem8DiscreteTradeoff k)
            (S.spent winner + I.bid winner q) -
          theorem8SlabPotential k (I.budget winner) (theorem8DiscreteTradeoff k)
            (S.spent winner) + I.bid winner q / (k : ℝ) := hscalar
    _ = theorem8StateSlabPotential k I (theorem8DiscreteTradeoff k)
          (applyScanDecision I S q (theorem8DiscreteScan k hk I S q)) -
        theorem8StateSlabPotential k I (theorem8DiscreteTradeoff k) S +
          I.bid winner q / (k : ℝ) := by
          rw [hstatePotential]
          ring

/-- The actual runner state before an occurrence, from an arbitrary initial state. -/
noncomputable def theorem8StateBeforeFrom
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (k : ℕ) (hk : 0 < k) (I : PaperInstance Advertiser Query)
    (S : OccurrenceState Advertiser Query)
    (history : List Query) (t : Fin history.length) :
    OccurrenceState Advertiser Query :=
  runOccurrencesFrom (theorem8DiscreteStep k hk I) S (history.take t.val)

/-- The split-payment potential of zero spend is zero. -/
theorem theorem8SlabPotential_zero
    {k : ℕ} (budget : ℝ) (psi : Fin k → ℝ) (hbudget : 0 ≤ budget) :
    theorem8SlabPotential k budget psi 0 = 0 := by
  unfold theorem8SlabPotential
  apply Finset.sum_eq_zero
  intro i _
  rw [theorem8SlabSpent_eq_zero_of_le_lower budget 0 i hbudget]
  · ring
  · unfold theorem8SlabLower
    exact div_nonneg (mul_nonneg hbudget (Nat.cast_nonneg _))
      (by exact_mod_cast (Nat.zero_le k))

/-- The empty runner state has zero split-payment potential. -/
theorem theorem8StateSlabPotential_initial_zero
    {Advertiser Query : Type*} [Fintype Advertiser]
    (k : ℕ) (I : PaperInstance Advertiser Query) (psi : Fin k → ℝ)
    (hbudget : I.NonnegativeBudgets) :
    theorem8StateSlabPotential k I psi initialOccurrenceState = 0 := by
  unfold theorem8StateSlabPotential
  apply Finset.sum_eq_zero
  intro a _
  simpa [initialOccurrenceState] using
    theorem8SlabPotential_zero (I.budget a) psi (hbudget a)

/-- The Theorem 8 weighted charge at one occurrence of a run from state `S`. -/
noncomputable def theorem8AlgWeightedRevenueAtFrom
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (k : ℕ) (hk : 0 < k) (I : PaperInstance Advertiser Query)
    (S : OccurrenceState Advertiser Query)
    (history : List Query) (t : Fin history.length) : ℝ :=
  match (theorem8DiscreteScan k hk I
      (theorem8StateBeforeFrom k hk I S history t) (history.get t)).winner with
  | none => 0
  | some a => I.bid a (history.get t) * theorem8DiscreteTradeoff k
    (activeBudgetSlab k hk ((theorem8StateBeforeFrom k hk I S history t).spent a)
      (I.budget a))

/-- Removing the first arrival shifts every later pre-occurrence state by one step. -/
theorem theorem8StateBeforeFrom_succ
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (k : ℕ) (hk : 0 < k) (I : PaperInstance Advertiser Query)
    (S : OccurrenceState Advertiser Query) (q : Query) (history : List Query)
    (t : Fin history.length) :
    theorem8StateBeforeFrom k hk I S (q :: history) t.succ =
      theorem8StateBeforeFrom k hk I (theorem8DiscreteStep k hk I S q) history t := by
  unfold theorem8StateBeforeFrom
  simp [runOccurrencesFrom]

/-- The weighted charge after the first arrival is the charge of the tail run. -/
theorem theorem8AlgWeightedRevenueAtFrom_succ
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (k : ℕ) (hk : 0 < k) (I : PaperInstance Advertiser Query)
    (S : OccurrenceState Advertiser Query) (q : Query) (history : List Query)
    (t : Fin history.length) :
    theorem8AlgWeightedRevenueAtFrom k hk I S (q :: history) t.succ =
      theorem8AlgWeightedRevenueAtFrom k hk I
        (theorem8DiscreteStep k hk I S q) history t := by
  unfold theorem8AlgWeightedRevenueAtFrom
  rw [theorem8StateBeforeFrom_succ]
  rfl

/-- The initial charge of a nonempty run is its first scan's weighted charge. -/
theorem theorem8AlgWeightedRevenueAtFrom_zero
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (k : ℕ) (hk : 0 < k) (I : PaperInstance Advertiser Query)
    (S : OccurrenceState Advertiser Query) (q : Query) (history : List Query) :
    theorem8AlgWeightedRevenueAtFrom k hk I S (q :: history) 0 =
      match (theorem8DiscreteScan k hk I S q).winner with
      | none => 0
      | some a => I.bid a q * theorem8DiscreteTradeoff k
        (activeBudgetSlab k hk (S.spent a) (I.budget a)) := by
  rfl

/--
A Theorem 8 step's weighted charge is bounded by its split-potential increase
and the step's revenue divided by the number of slabs.
-/
theorem theorem8DiscreteStep_weighted_charge_le_potential_increment
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (k : ℕ) (hk : 0 < k) (I : PaperInstance Advertiser Query)
    (S : OccurrenceState Advertiser Query) (q : Query)
    (hnonneg : occurrenceStateNonnegativeSpend S)
    (hfeasible : occurrenceStateBudgetFeasible I S) (hbudget : I.PositiveBudgets)
    (hbid : I.NonnegativeBids)
    (hsmall : ∀ a q, I.bid a q ≤ I.budget a / (k : ℝ)) :
    (match (theorem8DiscreteScan k hk I S q).winner with
    | none => 0
    | some a => I.bid a q * theorem8DiscreteTradeoff k
      (activeBudgetSlab k hk (S.spent a) (I.budget a))) ≤
      theorem8StateSlabPotential k I (theorem8DiscreteTradeoff k)
        (theorem8DiscreteStep k hk I S q) -
        theorem8StateSlabPotential k I (theorem8DiscreteTradeoff k) S +
          ((theorem8DiscreteStep k hk I S q).revenue - S.revenue) / (k : ℝ) := by
  cases hwin : (theorem8DiscreteScan k hk I S q).winner with
  | none =>
      have hpotential :
          theorem8StateSlabPotential k I (theorem8DiscreteTradeoff k)
            (theorem8DiscreteStep k hk I S q) =
            theorem8StateSlabPotential k I (theorem8DiscreteTradeoff k) S := by
        unfold theorem8StateSlabPotential theorem8DiscreteStep
        simp [applyScanDecision, hwin]
      rw [hpotential]
      simp [theorem8DiscreteStep, applyScanDecision, hwin]
  | some winner =>
      have hpoint := theorem8DiscreteScan_weighted_charge_le_potential_increment
        k hk I S q hnonneg hfeasible hbudget hbid hsmall winner hwin
      simpa [theorem8DiscreteStep, applyScanDecision, hwin] using hpoint

/--
The weighted charges of any finite Theorem 8 run telescope into split-payment
potential, with the total realized revenue divided by the number of slabs as
the finite crossing error.
-/
theorem theorem8_sum_weighted_revenue_from_le_potential
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (k : ℕ) (hk : 0 < k) (I : PaperInstance Advertiser Query)
    (history : List Query) (S : OccurrenceState Advertiser Query)
    (hnonneg : occurrenceStateNonnegativeSpend S)
    (hfeasible : occurrenceStateBudgetFeasible I S) (hbudget : I.PositiveBudgets)
    (hbid : I.NonnegativeBids)
    (hsmall : ∀ a q, I.bid a q ≤ I.budget a / (k : ℝ)) :
    (∑ t : Fin history.length,
      theorem8AlgWeightedRevenueAtFrom k hk I S history t) ≤
      theorem8StateSlabPotential k I (theorem8DiscreteTradeoff k)
        (runOccurrencesFrom (theorem8DiscreteStep k hk I) S history) -
        theorem8StateSlabPotential k I (theorem8DiscreteTradeoff k) S +
          ((runOccurrencesFrom (theorem8DiscreteStep k hk I) S history).revenue -
            S.revenue) / (k : ℝ) := by
  induction history generalizing S hnonneg hfeasible with
  | nil => simp [runOccurrencesFrom]
  | cons q history ih =>
      let S' := theorem8DiscreteStep k hk I S q
      have hstep := theorem8DiscreteStep_weighted_charge_le_potential_increment
        k hk I S q hnonneg hfeasible hbudget hbid hsmall
      have hnonneg' : occurrenceStateNonnegativeSpend S' := by
        simpa [S', theorem8DiscreteStep_eq_tradeoffStep] using
          tradeoffStep_preserves_nonnegative_spend
            (theorem8DiscreteSlabTradeoff k hk) I S q hnonneg hbid
      have hfeasible' : occurrenceStateBudgetFeasible I S' := by
        simpa [S', theorem8DiscreteStep_eq_tradeoffStep] using
          tradeoffStep_preserves_budget_feasible
            (theorem8DiscreteSlabTradeoff k hk) I S q hfeasible
      have htail := ih S' hnonneg' hfeasible'
      simp only [List.length_cons]
      rw [Fin.sum_univ_succ]
      simp only [theorem8AlgWeightedRevenueAtFrom_zero,
        theorem8AlgWeightedRevenueAtFrom_succ]
      rw [show (runOccurrencesFrom (theorem8DiscreteStep k hk I) S (q :: history)) =
        runOccurrencesFrom (theorem8DiscreteStep k hk I) S' history by
          rfl]
      dsimp [S'] at htail ⊢
      ring_nf at hstep htail ⊢
      linarith

/--
The finite Theorem 8 maximization rule gives the Lemma 6 tradeoff comparison
when the OPT bidder is affordable and its final class is taken to be the
runner's final *active* slab.  The latter convention is deliberately explicit:
the source's right-closed final-type convention differs at exact endpoints.
-/
theorem theorem8DiscreteScan_tradeoff_bound_of_activeFinalSlab
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (k : ℕ) (hk : 0 < k) (I : PaperInstance Advertiser Query)
    (S : OccurrenceState Advertiser Query) (q : Query)
    (algWinner optOwner : Advertiser)
    (finalActiveSlab : Advertiser → Fin k)
    (hbid : I.NonnegativeBids)
    (hchoice : (theorem8DiscreteScan k hk I S q).winner = some algWinner)
    (hoptFeasible : occurrenceCanAssign I S q optOwner)
    (hcurrent :
      activeBudgetSlab k hk (S.spent optOwner) (I.budget optOwner) ≤
        finalActiveSlab optOwner) :
    I.bid optOwner q * theorem8DiscreteTradeoff k (finalActiveSlab optOwner) ≤
      I.bid algWinner q * theorem8DiscreteTradeoff k
        (activeBudgetSlab k hk (S.spent algWinner) (I.budget algWinner)) := by
  have hmax := (theorem8DiscreteScan_winner_is_choice
    k hk I S q algWinner hchoice).2 optOwner hoptFeasible
  have hweight :
      theorem8DiscreteTradeoff k (finalActiveSlab optOwner) ≤
        theorem8DiscreteTradeoff k
          (activeBudgetSlab k hk (S.spent optOwner) (I.budget optOwner)) :=
    theorem8DiscreteTradeoff_antitone k hcurrent
  have hoptScore :
      I.bid optOwner q * theorem8DiscreteTradeoff k (finalActiveSlab optOwner) ≤
        occurrenceTheorem8DiscreteScore k hk I S q optOwner := by
    simpa [occurrenceTheorem8DiscreteScore] using
      mul_le_mul_of_nonneg_left hweight (hbid optOwner q)
  calc
    I.bid optOwner q * theorem8DiscreteTradeoff k (finalActiveSlab optOwner) ≤
        occurrenceTheorem8DiscreteScore k hk I S q optOwner := hoptScore
    _ ≤ occurrenceTheorem8DiscreteScore k hk I S q algWinner := hmax
    _ = I.bid algWinner q * theorem8DiscreteTradeoff k
        (activeBudgetSlab k hk (S.spent algWinner) (I.budget algWinner)) := rfl

/--
With a common positive bid, a discrete-score maximizer has the earliest active
slab among feasible advertisers, which is the BALANCE rule.  Strict decrease
is the precise tie convention needed by the source's phrase "monotonically
decreasing."
-/
theorem equal_bid_discrete_winner_has_earliest_slab
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (k : ℕ) (hk : 0 < k)
    (I : PaperInstance Advertiser Query)
    (S : OccurrenceState Advertiser Query) (q : Query) (a : Advertiser)
    {commonBid : ℝ} (hcommon : ∀ b, I.bid b q = commonBid)
    (hcommon_pos : 0 < commonBid)
    (hchoice : (discreteBalanceScan k hk I S q).winner = some a) :
    occurrenceCanAssign I S q a ∧
      ∀ b, occurrenceCanAssign I S q b →
        activeBudgetSlab k hk (S.spent a) (I.budget a) ≤
          activeBudgetSlab k hk (S.spent b) (I.budget b) := by
  classical
  have hspec :=
    (finiteMaxScan_winner_spec
      (occurrenceCanAssign I S q) (occurrenceDiscreteScore k hk I S q)
      (Finset.univ : Finset Advertiser).toList).2 a hchoice
  refine ⟨hspec.2.1, ?_⟩
  intro b hb
  by_contra hnot
  have hlt :
      activeBudgetSlab k hk (S.spent b) (I.budget b) <
        activeBudgetSlab k hk (S.spent a) (I.budget a) :=
    lt_of_not_ge hnot
  have hpsi := discreteTradeoff_strictAnti k hlt
  have hscaled :
      commonBid * discreteTradeoff k
          (activeBudgetSlab k hk (S.spent a) (I.budget a)) <
        commonBid * discreteTradeoff k
          (activeBudgetSlab k hk (S.spent b) (I.budget b)) :=
    mul_lt_mul_of_pos_left hpsi hcommon_pos
  have hmax := hspec.2.2 b (by simp) hb
  unfold occurrenceDiscreteScore at hmax
  rw [hcommon a, hcommon b] at hmax
  exact (not_lt_of_ge hmax) hscaled

/-- Each actual Balance scan performs exactly one feasibility test per advertiser. -/
theorem balanceScan_candidateTests
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (S : OccurrenceState Advertiser Query) (q : Query) :
    (balanceScan I S q).candidateTests = Fintype.card Advertiser := by
  classical
  unfold balanceScan
  rw [finiteMaxScan_candidateTests]
  simp

/-- Each actual Balance scan performs at most one comparison per advertiser. -/
theorem balanceScan_scoreComparisons_le
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (S : OccurrenceState Advertiser Query) (q : Query) :
    (balanceScan I S q).scoreComparisons ≤ Fintype.card Advertiser := by
  classical
  unfold balanceScan
  simpa using
    finiteMaxScan_scoreComparisons_le
      (occurrenceCanAssign I S q) (occurrenceBalanceScore I S q)
      (Finset.univ : Finset Advertiser).toList

/-- Exact candidate-test count for a complete occurrence-indexed run. -/
theorem runBalanceOccurrences_candidateTests
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query) (history : List Query) :
    (runBalanceOccurrences I history).candidateTests =
      history.length * Fintype.card Advertiser := by
  classical
  unfold runBalanceOccurrences
  have hgeneral :
      ∀ (S : OccurrenceState Advertiser Query),
        (runOccurrencesFrom (balanceStep I) S history).candidateTests =
          S.candidateTests + history.length * Fintype.card Advertiser := by
    induction history with
    | nil => intro S; simp [runOccurrencesFrom]
    | cons q qs ih =>
        intro S
        rw [runOccurrencesFrom, ih]
        simp [balanceStep, applyScanDecision, balanceScan_candidateTests]
        simp only [List.length_cons, Nat.succ_mul, one_mul]
        omega
  simpa [initialOccurrenceState] using hgeneral initialOccurrenceState

/-- Comparison bound for the same actual occurrence-indexed run. -/
theorem runBalanceOccurrences_scoreComparisons_le
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query) (history : List Query) :
    (runBalanceOccurrences I history).scoreComparisons ≤
      history.length * Fintype.card Advertiser := by
  classical
  unfold runBalanceOccurrences
  have hgeneral :
      ∀ (S : OccurrenceState Advertiser Query),
        (runOccurrencesFrom (balanceStep I) S history).scoreComparisons ≤
          S.scoreComparisons + history.length * Fintype.card Advertiser := by
    induction history with
    | nil => intro S; simp [runOccurrencesFrom]
    | cons q qs ih =>
        intro S
        calc
          (runOccurrencesFrom (balanceStep I) S (q :: qs)).scoreComparisons =
              (runOccurrencesFrom (balanceStep I) (balanceStep I S q) qs).scoreComparisons :=
                rfl
          _ ≤ (balanceStep I S q).scoreComparisons +
              qs.length * Fintype.card Advertiser := ih (balanceStep I S q)
          _ ≤ S.scoreComparisons +
              (q :: qs).length * Fintype.card Advertiser := by
                have hscan := balanceScan_scoreComparisons_le I S q
                simp only [balanceStep, applyScanDecision, List.length_cons,
                  Nat.succ_mul, one_mul]
                omega
  simpa [initialOccurrenceState] using hgeneral initialOccurrenceState

/-! ## Occurrence revenue and the distinct-identifier bridge -/

/-- Revenue contributed by one query occurrence under an occurrence assignment. -/
noncomputable def occurrenceRevenueAt
    (I : PaperInstance Advertiser Query) (history : List Query)
    (A : Fin history.length → Option Advertiser) (t : Fin history.length) : ℝ :=
  match A t with
  | none => 0
  | some a => I.bid a (history.get t)

/-- Total revenue of an assignment whose domain is occurrences, not query words. -/
noncomputable def occurrenceRevenue
    (I : PaperInstance Advertiser Query) (history : List Query)
    (A : Fin history.length → Option Advertiser) : ℝ :=
  ∑ t : Fin history.length, occurrenceRevenueAt I history A t

/-- Spend charged to one advertiser by an occurrence-indexed assignment. -/
noncomputable def occurrenceSpend
    [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query) (history : List Query)
    (A : Fin history.length → Option Advertiser) (a : Advertiser) : ℝ :=
  ∑ t : Fin history.length,
    match A t with
    | none => 0
    | some owner => if owner = a then I.bid a (history.get t) else 0

/--
Under the temporary unit-budget and exhaustive-offline-allocation assumptions
of Sections 2--5, the occurrence-indexed offline optimum is exactly the number
of advertisers.  Thus the source normalization is an exact benchmark identity,
not a replacement objective.
-/
theorem occurrenceIndexed_offlineOptimumValue_eq_card_of_unit_exhaustive
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query) (history : List Query)
    (opt : Fin history.length → Option Advertiser)
    (hbudget : I.PositiveBudgets) (hunit : EqualUnitBudgets I)
    (hoptFeasible : ∀ a, occurrenceSpend I history opt a ≤ I.budget a)
    (hexhaust : ∀ a, occurrenceSpend I history opt a = 1) :
    (occurrenceIndexedInstance I history).offlineOptimumValue
      (fun a => (hbudget a).le) = (Fintype.card Advertiser : ℝ) := by
  let J := occurrenceIndexedInstance I history
  have hJbudget : J.NonnegativeBudgets := by
    intro a
    exact (hbudget a).le
  have hfeasible : J.Feasible opt := by
    intro a
    exact hoptFeasible a
  have hlower := AdWordsInstance.revenue_le_offlineOptimumValue J hJbudget opt hfeasible
  have hupper := AdWordsInstance.offlineOptimumValue_le_totalBudget J hJbudget
  have hrev : J.revenue opt = (Fintype.card Advertiser : ℝ) := by
    rw [AdWordsInstance.revenue_eq_sum_spend]
    change (∑ a : Advertiser, occurrenceSpend I history opt a) = _
    simp_rw [hexhaust]
    simp
  have htotal : (∑ a : Advertiser, J.budget a) = (Fintype.card Advertiser : ℝ) := by
    simp_rw [show ∀ a, J.budget a = 1 by
      intro a
      exact hunit a]
    simp
  rw [hrev] at hlower
  rw [htotal] at hupper
  linarith

/-- A source-model allocation is total when every arriving occurrence receives an owner. -/
def occurrenceAssignmentIsTotal
    (history : List Query) (A : Fin history.length → Option Advertiser) : Prop :=
  ∀ t, ∃ a, A t = some a

/--
The Section 2 feasibility model for a chronological allocation: every arrival
is assigned and no advertiser is charged above its budget.  The separate
online runner may expose an unassigned occurrence when its feasibility scan has
no candidate; connecting that execution to this total source model is a later
theorem obligation, not a definitionally hidden convention.
-/
def occurrenceAssignmentFeasible
    [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query) (history : List Query)
    (A : Fin history.length → Option Advertiser) : Prop :=
  occurrenceAssignmentIsTotal history A ∧
    ∀ a, occurrenceSpend I history A a ≤ I.budget a

/--
When query identifiers are genuinely distinct and cover the finite query type,
the old identifier-indexed revenue is the corresponding chronological list sum.
No such bridge is asserted for histories with repeated words.
-/
theorem identifierRevenue_eq_history_sum_of_nodup_cover
    {Advertiser Query : Type*} [Fintype Query]
    [DecidableEq Query]
    (I : PaperInstance Advertiser Query)
    (A : PaperAssignment Advertiser Query)
    (history : List Query) (hnodup : history.Nodup)
    (hcover : AdWordsInstance.historyFinset history = Finset.univ) :
    paperRevenue I A =
      (history.map fun q =>
        match A q with
        | none => 0
        | some a => I.bid a q).sum := by
  exact AdWordsInstance.sum_univ_eq_list_sum_of_historyFinset_eq_univ
    history hnodup hcover (fun q =>
      match A q with
      | none => 0
      | some a => I.bid a q)

/-! ## Sections 4--6: explicit source accounting objects -/

/--
Section 4/5 final-type relation: type `i+1` means final spend fraction in
`(i/k,(i+1)/k]`, with zero spend assigned to the first type by convention.
-/
def IsFinalType (k : ℕ) (spentFraction : ℝ) (i : Fin k) : Prop :=
  (spentFraction = 0 ∧ i.val = 0) ∨
    ((i.val : ℝ) / (k : ℝ) < spentFraction ∧
      spentFraction ≤ (((i.val + 1 : ℕ) : ℝ) / (k : ℝ)))

/--
A right-closed source final type and the runner's floor-based active slab can
differ by at most one.  Equality at a right endpoint is exactly the possible
one-slab discrepancy.
-/
theorem activeSlab_val_le_finalType_val_add_one
    {k : ℕ} (hk : 0 < k) (spentFraction : ℝ) (i : Fin k)
    (htype : IsFinalType k spentFraction i) :
    (activeSlab k hk spentFraction).val ≤ i.val + 1 := by
  rcases htype with ⟨hzero, hi⟩ | ⟨_, hupper⟩
  · subst spentFraction
    simp [activeSlab]
  · have hkReal : (k : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hk)
    have hmul : (k : ℝ) * spentFraction ≤ (i.val + 1 : ℕ) := by
      calc
        (k : ℝ) * spentFraction ≤
            (k : ℝ) * (((i.val + 1 : ℕ) : ℝ) / (k : ℝ)) :=
          mul_le_mul_of_nonneg_left hupper (Nat.cast_nonneg k)
        _ = (i.val + 1 : ℕ) := by field_simp
    have hmax : max 0 ((k : ℝ) * spentFraction) ≤ (i.val + 1 : ℕ) :=
      max_le (Nat.cast_nonneg _) hmul
    change min (Nat.floor (max 0 ((k : ℝ) * spentFraction))) (k - 1) ≤
      i.val + 1
    exact (Nat.min_le_left _ _).trans (Nat.floor_le_of_le hmax)

/--
If the active slab is strictly later than a right-closed final type, then the
final spent fraction is exactly that type's upper endpoint.  This isolates the
only endpoint case omitted by the source's pointwise Lemma 6 wording.
-/
theorem spentFraction_eq_finalType_upper_of_finalType_lt_activeSlab
    {k : ℕ} (hk : 0 < k) (spentFraction : ℝ) (i : Fin k)
    (htype : IsFinalType k spentFraction i)
    (hlater : i.val < (activeSlab k hk spentFraction).val) :
    spentFraction = ((i.val + 1 : ℕ) : ℝ) / (k : ℝ) := by
  rcases htype with ⟨hzero, hi⟩ | ⟨htypeLower, hupper⟩
  · subst spentFraction
    simp [activeSlab] at hlater
  have hactiveUpper := activeSlab_val_le_finalType_val_add_one
    hk spentFraction i (Or.inr ⟨htypeLower, hupper⟩)
  have hfloorLower : i.val + 1 ≤
      Nat.floor (max 0 ((k : ℝ) * spentFraction)) := by
    have hleActive : i.val + 1 ≤ (activeSlab k hk spentFraction).val := by
      omega
    change i.val + 1 ≤
      min (Nat.floor (max 0 ((k : ℝ) * spentFraction))) (k - 1) at hleActive
    exact hleActive.trans (Nat.min_le_left _ _)
  have hargNonneg : 0 ≤ max 0 ((k : ℝ) * spentFraction) := le_max_left _ _
  have hspentNonneg : 0 ≤ spentFraction := by
    have htypeBase : 0 ≤ (i.val : ℝ) / (k : ℝ) := by positivity
    exact htypeBase.trans htypeLower.le
  have hproductNonneg : 0 ≤ (k : ℝ) * spentFraction :=
    mul_nonneg (Nat.cast_nonneg k) hspentNonneg
  have hlower : ((i.val + 1 : ℕ) : ℝ) ≤ (k : ℝ) * spentFraction := by
    calc
      ((i.val + 1 : ℕ) : ℝ) ≤
          (Nat.floor (max 0 ((k : ℝ) * spentFraction)) : ℝ) := by
        exact_mod_cast hfloorLower
      _ ≤ max 0 ((k : ℝ) * spentFraction) := Nat.floor_le hargNonneg
      _ = (k : ℝ) * spentFraction := by
        exact max_eq_right hproductNonneg
  have hkReal : 0 < (k : ℝ) := by exact_mod_cast hk
  apply (eq_div_iff hkReal.ne').2
  have hupperMul : spentFraction * (k : ℝ) ≤ ((i.val + 1 : ℕ) : ℝ) := by
    calc
      spentFraction * (k : ℝ) ≤
          (((i.val + 1 : ℕ) : ℝ) / (k : ℝ)) * (k : ℝ) :=
        mul_le_mul_of_nonneg_right hupper hkReal.le
      _ = ((i.val + 1 : ℕ) : ℝ) := by field_simp
  nlinarith [hlower]

/--
In an actual finite Theorem 8 suffix run, an intermediate active slab can be
later than the source's right-closed final type only for a bidder that finishes
exactly at that final type's upper endpoint.
-/
theorem theorem8_finalType_endpoint_of_currentSlab_later
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (k : ℕ) (hk : 0 < k) (I : PaperInstance Advertiser Query)
    (history : List Query) (S : OccurrenceState Advertiser Query)
    (hbid : I.NonnegativeBids) (hbudget : I.PositiveBudgets)
    (a : Advertiser) (finalType : Fin k)
    (hfinalType : IsFinalType k
      ((runOccurrencesFrom (theorem8DiscreteStep k hk I) S history).spent a /
        I.budget a) finalType)
    (hlater : finalType.val <
      (activeBudgetSlab k hk (S.spent a) (I.budget a)).val) :
    (runOccurrencesFrom (theorem8DiscreteStep k hk I) S history).spent a /
        I.budget a = ((finalType.val + 1 : ℕ) : ℝ) / (k : ℝ) := by
  apply spentFraction_eq_finalType_upper_of_finalType_lt_activeSlab
    hk _ finalType hfinalType
  exact lt_of_lt_of_le hlater <|
    runTheorem8DiscreteOccurrencesFrom_currentSlab_le_finalActiveSlab
      k hk I history S hbid hbudget a

/--
At one actual finite Theorem 8 decision, the source right-closed final-type
weight is bounded by the selected algorithm score plus at most `bid/k`.  The
only possible loss is the one-slab endpoint discrepancy isolated above.
-/
theorem theorem8DiscreteScan_tradeoff_bound_of_finalType_with_one_slab_error
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (k : ℕ) (hk : 0 < k) (I : PaperInstance Advertiser Query)
    (S : OccurrenceState Advertiser Query) (q : Query)
    (algWinner optOwner : Advertiser) (finalSpend : Advertiser → ℝ)
    (finalType : Advertiser → Fin k)
    (hbid : I.NonnegativeBids) (hbudget : I.PositiveBudgets)
    (hchoice : (theorem8DiscreteScan k hk I S q).winner = some algWinner)
    (hoptFeasible : occurrenceCanAssign I S q optOwner)
    (hstateLeFinal : S.spent optOwner ≤ finalSpend optOwner)
    (hfinalType : IsFinalType k
      (finalSpend optOwner / I.budget optOwner) (finalType optOwner)) :
    I.bid optOwner q * theorem8DiscreteTradeoff k (finalType optOwner) ≤
      I.bid algWinner q * theorem8DiscreteTradeoff k
        (activeBudgetSlab k hk (S.spent algWinner) (I.budget algWinner)) +
        I.bid optOwner q / (k : ℝ) := by
  let current := activeBudgetSlab k hk (S.spent optOwner) (I.budget optOwner)
  have hcurrentFinal : current ≤
      activeBudgetSlab k hk (finalSpend optOwner) (I.budget optOwner) := by
    exact activeBudgetSlab_monotone_spent k hk (I.budget optOwner)
      (hbudget optOwner) hstateLeFinal
  have hfinalActive :
      (activeBudgetSlab k hk (finalSpend optOwner) (I.budget optOwner)).val ≤
        (finalType optOwner).val + 1 :=
    activeSlab_val_le_finalType_val_add_one hk
      (finalSpend optOwner / I.budget optOwner) (finalType optOwner) hfinalType
  have hcurrentUpper : current.val ≤ (finalType optOwner).val + 1 :=
    (show current.val ≤
      (activeBudgetSlab k hk (finalSpend optOwner) (I.budget optOwner)).val
      from hcurrentFinal).trans hfinalActive
  have hmax := (theorem8DiscreteScan_winner_is_choice
    k hk I S q algWinner hchoice).2 optOwner hoptFeasible
  change I.bid optOwner q * theorem8DiscreteTradeoff k (finalType optOwner) ≤
    I.bid algWinner q * theorem8DiscreteTradeoff k
      (activeBudgetSlab k hk (S.spent algWinner) (I.budget algWinner)) +
      I.bid optOwner q / (k : ℝ)
  by_cases hnoLater : current.val ≤ (finalType optOwner).val
  · have hweight : theorem8DiscreteTradeoff k (finalType optOwner) ≤
        theorem8DiscreteTradeoff k current :=
      theorem8DiscreteTradeoff_antitone k hnoLater
    have hcompare : I.bid optOwner q * theorem8DiscreteTradeoff k (finalType optOwner) ≤
        occurrenceTheorem8DiscreteScore k hk I S q optOwner := by
      simpa [occurrenceTheorem8DiscreteScore, current] using
        mul_le_mul_of_nonneg_left hweight (hbid optOwner q)
    have herror : 0 ≤ I.bid optOwner q / (k : ℝ) :=
      div_nonneg (hbid optOwner q) (by exact_mod_cast (Nat.zero_le k))
    calc
      I.bid optOwner q * theorem8DiscreteTradeoff k (finalType optOwner) ≤
          occurrenceTheorem8DiscreteScore k hk I S q optOwner := hcompare
      _ ≤ occurrenceTheorem8DiscreteScore k hk I S q algWinner := hmax
      _ ≤ occurrenceTheorem8DiscreteScore k hk I S q algWinner +
          I.bid optOwner q / (k : ℝ) := le_add_of_nonneg_right herror
      _ = _ := rfl
  · have hlater : (finalType optOwner).val < current.val := lt_of_not_ge hnoLater
    have hcurrentEqVal : current.val = (finalType optOwner).val + 1 := by omega
    have hnext : (finalType optOwner).val + 1 < k := by
      rw [← hcurrentEqVal]
      exact current.isLt
    let next : Fin k := ⟨(finalType optOwner).val + 1, hnext⟩
    have hcurrentEq : current = next := Fin.ext hcurrentEqVal
    have hgap := theorem8DiscreteTradeoff_drop_to_succ_le_one_div
      (finalType optOwner) hnext
    have hscaled := mul_le_mul_of_nonneg_left hgap (hbid optOwner q)
    have hcompare : I.bid optOwner q * theorem8DiscreteTradeoff k (finalType optOwner) ≤
        occurrenceTheorem8DiscreteScore k hk I S q optOwner +
          I.bid optOwner q / (k : ℝ) := by
      rw [show occurrenceTheorem8DiscreteScore k hk I S q optOwner =
          I.bid optOwner q * theorem8DiscreteTradeoff k current by rfl,
        hcurrentEq]
      calc
        I.bid optOwner q * theorem8DiscreteTradeoff k (finalType optOwner) ≤
            I.bid optOwner q * theorem8DiscreteTradeoff k next +
              I.bid optOwner q * (1 / (k : ℝ)) := by
          nlinarith [hscaled]
        _ = I.bid optOwner q * theorem8DiscreteTradeoff k next +
              I.bid optOwner q / (k : ℝ) := by ring
    calc
      I.bid optOwner q * theorem8DiscreteTradeoff k (finalType optOwner) ≤
          occurrenceTheorem8DiscreteScore k hk I S q optOwner +
            I.bid optOwner q / (k : ℝ) := hcompare
      _ ≤ occurrenceTheorem8DiscreteScore k hk I S q algWinner +
          I.bid optOwner q / (k : ℝ) := by linarith [hmax]
      _ = _ := rfl

/-- OPT revenue at an occurrence whose owner is in a designated endpoint class. -/
noncomputable def endpointOptRevenueAt
    {Advertiser Query : Type*}
    (I : PaperInstance Advertiser Query) (history : List Query)
    (opt : Fin history.length → Option Advertiser)
    (endpoint : Advertiser → Prop) [DecidablePred endpoint]
    (t : Fin history.length) : ℝ :=
  match opt t with
  | none => 0
  | some a => if endpoint a then I.bid a (history.get t) else 0

/--
The one-slab endpoint charge for one OPT-owned occurrence.  It is nonzero only
when the source final type is strictly earlier than the runner's current slab.
-/
noncomputable def endpointRoundingErrorAt
    {Advertiser Query : Type*}
    (k : ℕ) (I : PaperInstance Advertiser Query) (history : List Query)
    (opt : Fin history.length → Option Advertiser)
    (finalType : Advertiser → Fin k)
    (currentSlab : Fin history.length → Advertiser → Fin k)
    (t : Fin history.length) : ℝ :=
  match opt t with
  | none => 0
  | some a =>
      if (finalType a).val < (currentSlab t a).val then
        I.bid a (history.get t) / (k : ℝ)
      else 0

/-- Endpoint-filtered occurrence revenue is exactly the corresponding sum of OPT spends. -/
theorem sum_endpointOptRevenueAt_eq_endpoint_spend
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query) (history : List Query)
    (opt : Fin history.length → Option Advertiser)
    (endpoint : Advertiser → Prop) [DecidablePred endpoint] :
    ∑ t : Fin history.length, endpointOptRevenueAt I history opt endpoint t =
      ∑ a : Advertiser, if endpoint a then occurrenceSpend I history opt a else 0 := by
  classical
  calc
    ∑ t : Fin history.length, endpointOptRevenueAt I history opt endpoint t =
        ∑ t : Fin history.length, ∑ a : Advertiser,
          if endpoint a then
            match opt t with
            | none => 0
            | some owner => if owner = a then I.bid a (history.get t) else 0
          else 0 := by
      apply Finset.sum_congr rfl
      intro t _
      cases hopt : opt t with
      | none => simp [endpointOptRevenueAt, hopt]
      | some owner =>
          by_cases hend : endpoint owner
          · simp only [endpointOptRevenueAt, hopt, if_pos hend]
            symm
            have hsum := Fintype.sum_eq_single owner
              (f := fun a : Advertiser =>
                if endpoint a then
                  if owner = a then I.bid a (history.get t) else 0
                else 0)
              (fun a hne => by
                have howner : owner ≠ a := Ne.symm hne
                simp [howner])
            simpa [hend] using hsum
          · simp only [endpointOptRevenueAt, hopt, if_neg hend]
            symm
            apply Fintype.sum_eq_zero
            intro a
            by_cases howner : owner = a
            · subst a
              simp [hend]
            · simp [howner]
    _ = ∑ a : Advertiser, ∑ t : Fin history.length,
          if endpoint a then
            match opt t with
            | none => 0
            | some owner => if owner = a then I.bid a (history.get t) else 0
          else 0 := Finset.sum_comm
    _ = ∑ a : Advertiser, if endpoint a then occurrenceSpend I history opt a else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases hend : endpoint a
      · simp [hend, occurrenceSpend]
      · simp [hend]

/--
An endpoint rounding charge is bounded by its endpoint-filtered OPT revenue
divided by the number of slabs.
-/
theorem endpointRoundingErrorAt_le_endpointOptRevenueAt_div
    {Advertiser Query : Type*} {k : ℕ}
    (I : PaperInstance Advertiser Query) (history : List Query)
    (opt : Fin history.length → Option Advertiser)
    (finalType : Advertiser → Fin k)
    (currentSlab : Fin history.length → Advertiser → Fin k)
    (endpoint : Advertiser → Prop) [DecidablePred endpoint]
    (hbid : I.NonnegativeBids)
    (hbad : ∀ t a, opt t = some a →
      (finalType a).val < (currentSlab t a).val → endpoint a)
    (t : Fin history.length) :
    endpointRoundingErrorAt k I history opt finalType currentSlab t ≤
      endpointOptRevenueAt I history opt endpoint t / (k : ℝ) := by
  classical
  cases hopt : opt t with
  | none => simp [endpointRoundingErrorAt, endpointOptRevenueAt, hopt]
  | some a =>
      by_cases hlater : (finalType a).val < (currentSlab t a).val
      · have hend := hbad t a hopt hlater
        simp [endpointRoundingErrorAt, endpointOptRevenueAt, hopt,
          hlater, hend]
      · simp only [endpointRoundingErrorAt, hopt, if_neg hlater]
        by_cases hend : endpoint a
        · simpa [endpointOptRevenueAt, hopt, hend] using
            (div_nonneg (hbid a (history.get t))
              (by exact_mod_cast (Nat.zero_le k)))
        · simp [endpointOptRevenueAt, hopt, hend]

/-- The total endpoint rounding charge is at most endpoint OPT spend divided by `k`. -/
theorem sum_endpointRoundingErrorAt_le_endpoint_spend_div
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    {k : ℕ} (hk : 0 < k)
    (I : PaperInstance Advertiser Query) (history : List Query)
    (opt : Fin history.length → Option Advertiser)
    (finalType : Advertiser → Fin k)
    (currentSlab : Fin history.length → Advertiser → Fin k)
    (endpoint : Advertiser → Prop) [DecidablePred endpoint]
    (hbid : I.NonnegativeBids)
    (hbad : ∀ t a, opt t = some a →
      (finalType a).val < (currentSlab t a).val → endpoint a) :
    ∑ t : Fin history.length,
      endpointRoundingErrorAt k I history opt finalType currentSlab t ≤
      (∑ a : Advertiser, if endpoint a then occurrenceSpend I history opt a else 0) /
        (k : ℝ) := by
  calc
    ∑ t : Fin history.length,
        endpointRoundingErrorAt k I history opt finalType currentSlab t ≤
        ∑ t : Fin history.length,
          endpointOptRevenueAt I history opt endpoint t / (k : ℝ) := by
      exact Finset.sum_le_sum fun t _ =>
        endpointRoundingErrorAt_le_endpointOptRevenueAt_div
          I history opt finalType currentSlab endpoint hbid hbad t
    _ = (∑ t : Fin history.length,
          endpointOptRevenueAt I history opt endpoint t) / (k : ℝ) := by
      rw [Finset.sum_div]
    _ = _ := by
      rw [sum_endpointOptRevenueAt_eq_endpoint_spend]

/-- Endpoint-filtered OPT spend never exceeds total advertiser budget. -/
theorem endpoint_spend_le_total_budget
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query) (history : List Query)
    (opt : Fin history.length → Option Advertiser)
    (endpoint : Advertiser → Prop) [DecidablePred endpoint]
    (hbudget : I.PositiveBudgets)
    (hoptFeasible : ∀ a, occurrenceSpend I history opt a ≤ I.budget a) :
    (∑ a : Advertiser, if endpoint a then occurrenceSpend I history opt a else 0) ≤
      ∑ a : Advertiser, I.budget a := by
  refine Finset.sum_le_sum fun a _ => ?_
  by_cases hend : endpoint a
  · simpa [hend] using hoptFeasible a
  · simp [hend, (hbudget a).le]

/--
The complete endpoint correction is bounded by total budget divided by `k`.
This is the source's aggregate rounding scale; it does not grow with the
number of query occurrences.
-/
theorem sum_endpointRoundingErrorAt_le_total_budget_div
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    {k : ℕ} (hk : 0 < k)
    (I : PaperInstance Advertiser Query) (history : List Query)
    (opt : Fin history.length → Option Advertiser)
    (finalType : Advertiser → Fin k)
    (currentSlab : Fin history.length → Advertiser → Fin k)
    (endpoint : Advertiser → Prop) [DecidablePred endpoint]
    (hbid : I.NonnegativeBids) (hbudget : I.PositiveBudgets)
    (hbad : ∀ t a, opt t = some a →
      (finalType a).val < (currentSlab t a).val → endpoint a)
    (hoptFeasible : ∀ a, occurrenceSpend I history opt a ≤ I.budget a) :
    ∑ t : Fin history.length,
      endpointRoundingErrorAt k I history opt finalType currentSlab t ≤
      (∑ a : Advertiser, I.budget a) / (k : ℝ) := by
  have hspend := sum_endpointRoundingErrorAt_le_endpoint_spend_div
    hk I history opt finalType currentSlab endpoint hbid hbad
  have hbudgetSum := endpoint_spend_le_total_budget
    I history opt endpoint hbudget hoptFeasible
  exact hspend.trans <|
    div_le_div_of_nonneg_right hbudgetSum (by exact_mod_cast (Nat.zero_le k))

/-- A bidder is an endpoint bidder when its source final type ends exactly at its upper slab boundary. -/
def theorem8FinalTypeEndpoint
    {Advertiser Query : Type*} (k : ℕ)
    (I : PaperInstance Advertiser Query) (finalSpend : Advertiser → ℝ)
    (finalType : Advertiser → Fin k) (a : Advertiser) : Prop :=
  finalSpend a / I.budget a = ((finalType a).val + 1 : ℕ) / (k : ℝ)

/--
For the actual Theorem 8 runner, a source final type can be earlier than the
pre-occurrence active slab only for an endpoint bidder.
-/
theorem theorem8CurrentSlabAt_later_implies_finalTypeEndpoint
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (k : ℕ) (hk : 0 < k) (I : PaperInstance Advertiser Query)
    (history : List Query) (t : Fin history.length)
    (hbid : I.NonnegativeBids) (hbudget : I.PositiveBudgets)
    (finalType : Advertiser → Fin k)
    (hfinalType : ∀ a, IsFinalType k
      ((runTheorem8DiscreteOccurrences k hk I history).spent a / I.budget a)
      (finalType a))
    (a : Advertiser)
    (hlater : (finalType a).val <
      (theorem8CurrentSlabAt k hk I history t a).val) :
    theorem8FinalTypeEndpoint k I
      (runTheorem8DiscreteOccurrences k hk I history).spent finalType a := by
  unfold theorem8FinalTypeEndpoint
  apply spentFraction_eq_finalType_upper_of_finalType_lt_activeSlab
    hk _ (finalType a) (hfinalType a)
  exact lt_of_lt_of_le hlater <|
    theorem8CurrentSlabAt_le_finalActiveSlab
      k hk I history t hbid hbudget a

/--
The aggregate right-endpoint correction of the actual Theorem 8 run is at
most total advertiser budget divided by `k`, independently of history length.
-/
theorem theorem8_sum_endpointRoundingErrorAt_le_total_budget_div
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (k : ℕ) (hk : 0 < k) (I : PaperInstance Advertiser Query)
    (history : List Query) (opt : Fin history.length → Option Advertiser)
    (hbid : I.NonnegativeBids) (hbudget : I.PositiveBudgets)
    (finalType : Advertiser → Fin k)
    (hfinalType : ∀ a, IsFinalType k
      ((runTheorem8DiscreteOccurrences k hk I history).spent a / I.budget a)
      (finalType a))
    (hoptFeasible : ∀ a, occurrenceSpend I history opt a ≤ I.budget a) :
    ∑ t : Fin history.length,
      endpointRoundingErrorAt k I history opt finalType
        (theorem8CurrentSlabAt k hk I history) t ≤
      (∑ a : Advertiser, I.budget a) / (k : ℝ) := by
  classical
  apply sum_endpointRoundingErrorAt_le_total_budget_div
    hk I history opt finalType (theorem8CurrentSlabAt k hk I history)
    (theorem8FinalTypeEndpoint k I
      (runTheorem8DiscreteOccurrences k hk I history).spent finalType)
    hbid hbudget
  · intro t a _ hlater
    exact theorem8CurrentSlabAt_later_implies_finalTypeEndpoint
      k hk I history t hbid hbudget finalType hfinalType a hlater
  · exact hoptFeasible

/-- Every source right-closed final type lies below its stated upper endpoint. -/
theorem finalType_fraction_le_upper
    {k : ℕ} (hk : 0 < k) (spentFraction : ℝ) (i : Fin k)
    (htype : IsFinalType k spentFraction i) :
    spentFraction ≤ ((i.val + 1 : ℕ) : ℝ) / (k : ℝ) := by
  rcases htype with ⟨hzero, hi⟩ | ⟨_, hupper⟩
  · subst spentFraction
    have hkReal : 0 < (k : ℝ) := by exact_mod_cast hk
    exact div_nonneg (Nat.cast_nonneg _) hkReal.le
  · exact hupper

/--
Under the source small-bid scale `bid ≤ budget/k`, an OPT owner in a
preterminal final type is affordable at its actual Theorem 8 arrival state.
This supplies the scan-feasibility premise used in the Lemma 6 comparison.
-/
theorem theorem8StateBefore_canAssign_of_preterminal_finalType
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (k : ℕ) (hk : 0 < k) (I : PaperInstance Advertiser Query)
    (history : List Query) (t : Fin history.length)
    (hbid : I.NonnegativeBids) (hbudget : I.PositiveBudgets)
    (hsmall : ∀ a q, I.bid a q ≤ I.budget a / (k : ℝ))
    (finalType : Advertiser → Fin k)
    (hfinalType : ∀ a, IsFinalType k
      ((runTheorem8DiscreteOccurrences k hk I history).spent a / I.budget a)
      (finalType a))
    (a : Advertiser)
    (hpreterminal : (finalType a).val + 1 < k) :
    occurrenceCanAssign I (theorem8StateBefore k hk I history t)
      (history.get t) a := by
  have hkReal : 0 < (k : ℝ) := by exact_mod_cast hk
  have hstate := theorem8StateBefore_spent_le_final
    k hk I history t hbid a
  have hfrac := finalType_fraction_le_upper hk
    ((runTheorem8DiscreteOccurrences k hk I history).spent a / I.budget a)
    (finalType a) (hfinalType a)
  have hfinal : (runTheorem8DiscreteOccurrences k hk I history).spent a ≤
      I.budget a * (((finalType a).val + 1 : ℕ) : ℝ) / (k : ℝ) := by
    have hmul := (div_le_iff₀ (hbudget a)).mp hfrac
    calc
      (runTheorem8DiscreteOccurrences k hk I history).spent a ≤
          (((finalType a).val + 1 : ℕ) : ℝ) / (k : ℝ) * I.budget a := hmul
      _ = I.budget a * (((finalType a).val + 1 : ℕ) : ℝ) / (k : ℝ) := by ring
  have hindex :
      (((finalType a).val + 1 : ℕ) : ℝ) / (k : ℝ) + 1 / (k : ℝ) ≤ 1 := by
    rw [← add_div]
    apply (div_le_one₀ hkReal).2
    exact_mod_cast (show (finalType a).val + 1 + 1 ≤ k by omega)
  have hscaled :
      I.budget a * (((finalType a).val + 1 : ℕ) : ℝ) / (k : ℝ) +
        I.budget a / (k : ℝ) ≤ I.budget a := by
    calc
      I.budget a * (((finalType a).val + 1 : ℕ) : ℝ) / (k : ℝ) +
          I.budget a / (k : ℝ) =
          I.budget a *
            ((((finalType a).val + 1 : ℕ) : ℝ) / (k : ℝ) + 1 / (k : ℝ)) := by ring
      _ ≤ I.budget a * 1 := mul_le_mul_of_nonneg_left hindex (hbudget a).le
      _ = I.budget a := by ring
  unfold occurrenceCanAssign
  calc
    (theorem8StateBefore k hk I history t).spent a + I.bid a (history.get t) ≤
        (runTheorem8DiscreteOccurrences k hk I history).spent a +
          I.bid a (history.get t) := by linarith [hstate]
    _ ≤ I.budget a * (((finalType a).val + 1 : ℕ) : ℝ) / (k : ℝ) +
          I.budget a / (k : ℝ) :=
      add_le_add hfinal (hsmall a (history.get t))
    _ ≤ I.budget a := hscaled

/-- Actual Theorem 8 scan winner at one chronological occurrence. -/
noncomputable def theorem8WinnerAt
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (k : ℕ) (hk : 0 < k) (I : PaperInstance Advertiser Query)
    (history : List Query) (t : Fin history.length) : Option Advertiser :=
  (theorem8DiscreteScan k hk I
    (theorem8StateBefore k hk I history t) (history.get t)).winner

/-- The online weighted revenue recorded at one chronological Theorem 8 scan. -/
noncomputable def theorem8AlgWeightedRevenueAt
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (k : ℕ) (hk : 0 < k) (I : PaperInstance Advertiser Query)
    (history : List Query) (t : Fin history.length) : ℝ :=
  match theorem8WinnerAt k hk I history t with
  | none => 0
  | some a => I.bid a (history.get t) *
      theorem8DiscreteTradeoff k (theorem8CurrentSlabAt k hk I history t a)

/-- Starting the generalized weighted-charge accounting from the empty state recovers the source chronology. -/
theorem theorem8AlgWeightedRevenueAtFrom_initial_eq
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (k : ℕ) (hk : 0 < k) (I : PaperInstance Advertiser Query)
    (history : List Query) (t : Fin history.length) :
    theorem8AlgWeightedRevenueAtFrom k hk I initialOccurrenceState history t =
      theorem8AlgWeightedRevenueAt k hk I history t := by
  rfl

/--
The weighted payments of the source Theorem 8 run are at most its terminal
split-payment potential plus realized revenue divided by the number of slabs.
-/
theorem theorem8_sum_weighted_revenue_le_potential
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (k : ℕ) (hk : 0 < k) (I : PaperInstance Advertiser Query)
    (history : List Query) (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (hsmall : ∀ a q, I.bid a q ≤ I.budget a / (k : ℝ)) :
    (∑ t : Fin history.length,
      theorem8AlgWeightedRevenueAt k hk I history t) ≤
      theorem8StateSlabPotential k I (theorem8DiscreteTradeoff k)
        (runTheorem8DiscreteOccurrences k hk I history) +
        (runTheorem8DiscreteOccurrences k hk I history).revenue / (k : ℝ) := by
  have hmain := theorem8_sum_weighted_revenue_from_le_potential
    k hk I history initialOccurrenceState
    initialOccurrenceState_nonnegative_spend
    (initialOccurrenceState_budget_feasible I (fun a => (hbudget a).le))
    hbudget hbid hsmall
  have hzero := theorem8StateSlabPotential_initial_zero
    k I (theorem8DiscreteTradeoff k) (fun a => (hbudget a).le)
  calc
    (∑ t : Fin history.length,
        theorem8AlgWeightedRevenueAt k hk I history t) =
        ∑ t : Fin history.length,
          theorem8AlgWeightedRevenueAtFrom k hk I initialOccurrenceState history t := by
            apply Finset.sum_congr rfl
            intro t _
            exact (theorem8AlgWeightedRevenueAtFrom_initial_eq k hk I history t).symm
    _ ≤ theorem8StateSlabPotential k I (theorem8DiscreteTradeoff k)
          (runOccurrencesFrom (theorem8DiscreteStep k hk I) initialOccurrenceState history) -
        theorem8StateSlabPotential k I (theorem8DiscreteTradeoff k)
          initialOccurrenceState +
          ((runOccurrencesFrom (theorem8DiscreteStep k hk I)
            initialOccurrenceState history).revenue - initialOccurrenceState.revenue) /
            (k : ℝ) := hmain
    _ = theorem8StateSlabPotential k I (theorem8DiscreteTradeoff k)
          (runTheorem8DiscreteOccurrences k hk I history) +
          (runTheorem8DiscreteOccurrences k hk I history).revenue / (k : ℝ) := by
          rw [hzero]
          simp [runTheorem8DiscreteOccurrences, initialOccurrenceState]

/-- OPT's source-final-type weighted revenue at one chronological occurrence. -/
noncomputable def theorem8OptWeightedRevenueAt
    {Advertiser Query : Type*}
    (k : ℕ) (I : PaperInstance Advertiser Query) (history : List Query)
    (opt : Fin history.length → Option Advertiser)
    (finalType : Advertiser → Fin k) (t : Fin history.length) : ℝ :=
  match opt t with
  | none => 0
  | some a => I.bid a (history.get t) * theorem8DiscreteTradeoff k (finalType a)

/-- The terminal Theorem 8 type has zero geometric tradeoff weight. -/
theorem theorem8DiscreteTradeoff_terminal
    {k : ℕ} (i : Fin k) (hterminal : i.val + 1 = k) :
    theorem8DiscreteTradeoff k i = 0 := by
  unfold theorem8DiscreteTradeoff
  rw [show k - (i.val + 1) = 0 by omega]
  norm_num

/-- Every finite Theorem 8 tradeoff weight is nonnegative. -/
theorem theorem8DiscreteTradeoff_nonnegative
    {k : ℕ} (i : Fin k) : 0 ≤ theorem8DiscreteTradeoff k i := by
  have hk : 0 < (k : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt i.isLt)
  have hkone : (1 : ℝ) ≤ k := by exact_mod_cast (Nat.zero_lt_of_lt i.isLt)
  have hbase : 0 ≤ 1 - 1 / (k : ℝ) := by
    rw [one_div]
    exact sub_nonneg.mpr ((inv_le_one₀ hk).2 hkone)
  have hbaseOne : 1 - 1 / (k : ℝ) ≤ 1 := by
    have : 0 ≤ 1 / (k : ℝ) := by positivity
    linarith
  have hpow : (1 - 1 / (k : ℝ)) ^ (k - (i.val + 1)) ≤ 1 :=
    pow_le_one₀ hbase hbaseOne
  unfold theorem8DiscreteTradeoff
  linarith

/-- One scan's weighted algorithm revenue is nonnegative under nonnegative bids. -/
theorem theorem8AlgWeightedRevenueAt_nonnegative
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (k : ℕ) (hk : 0 < k) (I : PaperInstance Advertiser Query)
    (history : List Query) (t : Fin history.length) (hbid : I.NonnegativeBids) :
    0 ≤ theorem8AlgWeightedRevenueAt k hk I history t := by
  unfold theorem8AlgWeightedRevenueAt theorem8WinnerAt
  split <;> simp
  exact mul_nonneg (hbid _ _) (theorem8DiscreteTradeoff_nonnegative _)

/--
Actual-run Lemma 6 with the source's right-endpoint correction.  A preterminal
OPT owner is feasible under the source small-bid scale; terminal owners have
zero source weight.
-/
theorem theorem8_per_occurrence_tradeoff_with_endpoint_error
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (k : ℕ) (hk : 0 < k) (I : PaperInstance Advertiser Query)
    (history : List Query) (t : Fin history.length)
    (opt : Fin history.length → Option Advertiser)
    (hbid : I.NonnegativeBids) (hbudget : I.PositiveBudgets)
    (hsmall : ∀ a q, I.bid a q ≤ I.budget a / (k : ℝ))
    (finalType : Advertiser → Fin k)
    (hfinalType : ∀ a, IsFinalType k
      ((runTheorem8DiscreteOccurrences k hk I history).spent a / I.budget a)
      (finalType a)) :
    theorem8OptWeightedRevenueAt k I history opt finalType t ≤
      theorem8AlgWeightedRevenueAt k hk I history t +
        endpointRoundingErrorAt k I history opt finalType
          (theorem8CurrentSlabAt k hk I history) t := by
  classical
  cases hopt : opt t with
  | none =>
      simp [theorem8OptWeightedRevenueAt, endpointRoundingErrorAt, hopt]
      exact theorem8AlgWeightedRevenueAt_nonnegative k hk I history t hbid
  | some owner =>
      by_cases hpreterminal : (finalType owner).val + 1 < k
      · have hfeasible := theorem8StateBefore_canAssign_of_preterminal_finalType
          k hk I history t hbid hbudget hsmall finalType hfinalType owner hpreterminal
        cases hwinner : theorem8WinnerAt k hk I history t with
        | none =>
            have hscan : (theorem8DiscreteScan k hk I
                (theorem8StateBefore k hk I history t) (history.get t)).winner = none :=
              hwinner
            have hnone :=
              (finiteMaxScan_winner_spec
                (occurrenceCanAssign I (theorem8StateBefore k hk I history t)
                  (history.get t))
                (occurrenceTheorem8DiscreteScore k hk I
                  (theorem8StateBefore k hk I history t) (history.get t))
                (Finset.univ : Finset Advertiser).toList).1.mp hscan
            exact False.elim (hnone owner (by simp) hfeasible)
        | some winner =>
            change (theorem8DiscreteScan k hk I
              (theorem8StateBefore k hk I history t) (history.get t)).winner =
              some winner at hwinner
            have hchoice : (theorem8DiscreteScan k hk I
                (theorem8StateBefore k hk I history t) (history.get t)).winner = some winner :=
              hwinner
            have hstate := theorem8StateBefore_spent_le_final
              k hk I history t hbid owner
            by_cases hlater : (finalType owner).val <
                (theorem8CurrentSlabAt k hk I history t owner).val
            · have hpoint := theorem8DiscreteScan_tradeoff_bound_of_finalType_with_one_slab_error
                k hk I (theorem8StateBefore k hk I history t) (history.get t)
                winner owner (runTheorem8DiscreteOccurrences k hk I history).spent
                finalType hbid hbudget hchoice hfeasible hstate (hfinalType owner)
              have hlaterFin : finalType owner <
                  theorem8CurrentSlabAt k hk I history t owner := hlater
              simp only [theorem8OptWeightedRevenueAt, hopt,
                theorem8AlgWeightedRevenueAt, theorem8WinnerAt,
                endpointRoundingErrorAt]
              change I.bid owner (history.get t) *
                  theorem8DiscreteTradeoff k (finalType owner) ≤
                (match (theorem8DiscreteScan k hk I
                    (theorem8StateBefore k hk I history t) (history.get t)).winner with
                  | none => 0
                  | some a => I.bid a (history.get t) * theorem8DiscreteTradeoff k
                    (theorem8CurrentSlabAt k hk I history t a)) +
                  if finalType owner < theorem8CurrentSlabAt k hk I history t owner then
                    I.bid owner (history.get t) / (k : ℝ)
                  else 0
              rw [hwinner]
              simp only [if_pos hlaterFin]
              exact hpoint
            · have hnoLater : theorem8CurrentSlabAt k hk I history t owner ≤
                finalType owner := by
                  exact Nat.le_of_not_lt hlater
              have hmax := (theorem8DiscreteScan_winner_is_choice
                k hk I (theorem8StateBefore k hk I history t) (history.get t)
                winner hchoice).2 owner hfeasible
              have hweight : theorem8DiscreteTradeoff k (finalType owner) ≤
                  theorem8DiscreteTradeoff k
                    (theorem8CurrentSlabAt k hk I history t owner) :=
                theorem8DiscreteTradeoff_antitone k hnoLater
              have hcompare : I.bid owner (history.get t) *
                  theorem8DiscreteTradeoff k (finalType owner) ≤
                  occurrenceTheorem8DiscreteScore k hk I
                    (theorem8StateBefore k hk I history t) (history.get t) owner := by
                simpa [occurrenceTheorem8DiscreteScore, theorem8CurrentSlabAt,
                  theorem8StateBefore] using
                  mul_le_mul_of_nonneg_left hweight (hbid owner (history.get t))
              have hpoint : I.bid owner (history.get t) *
                  theorem8DiscreteTradeoff k (finalType owner) ≤
                  I.bid winner (history.get t) * theorem8DiscreteTradeoff k
                    (theorem8CurrentSlabAt k hk I history t winner) := by
                calc
                  I.bid owner (history.get t) * theorem8DiscreteTradeoff k
                      (finalType owner) ≤
                      occurrenceTheorem8DiscreteScore k hk I
                        (theorem8StateBefore k hk I history t) (history.get t) owner := hcompare
                  _ ≤ occurrenceTheorem8DiscreteScore k hk I
                        (theorem8StateBefore k hk I history t) (history.get t) winner := hmax
                  _ = _ := by rfl
              simp only [theorem8OptWeightedRevenueAt, hopt,
                theorem8AlgWeightedRevenueAt, theorem8WinnerAt,
                endpointRoundingErrorAt]
              change I.bid owner (history.get t) *
                  theorem8DiscreteTradeoff k (finalType owner) ≤
                (match (theorem8DiscreteScan k hk I
                    (theorem8StateBefore k hk I history t) (history.get t)).winner with
                  | none => 0
                  | some a => I.bid a (history.get t) * theorem8DiscreteTradeoff k
                    (theorem8CurrentSlabAt k hk I history t a)) +
                  if finalType owner < theorem8CurrentSlabAt k hk I history t owner then
                    I.bid owner (history.get t) / (k : ℝ)
                  else 0
              have hnotLaterFin : ¬ finalType owner <
                  theorem8CurrentSlabAt k hk I history t owner :=
                not_lt_of_ge hnoLater
              rw [hwinner]
              simp only [if_neg hnotLaterFin, add_zero]
              exact hpoint
      · have hterminal : (finalType owner).val + 1 = k := by
          have := (finalType owner).isLt
          omega
        have hzero := theorem8DiscreteTradeoff_terminal (finalType owner) hterminal
        have herr_nonneg : 0 ≤ endpointRoundingErrorAt k I history opt finalType
            (theorem8CurrentSlabAt k hk I history) t := by
          simp only [endpointRoundingErrorAt, hopt]
          split_ifs with h
          · exact div_nonneg (hbid owner (history.get t))
              (by exact_mod_cast (Nat.zero_le k))
          · exact le_rfl
        have halg_nonneg := theorem8AlgWeightedRevenueAt_nonnegative
          k hk I history t hbid
        simp [theorem8OptWeightedRevenueAt, hopt, hzero]
        linarith

/--
Summing the actual-run Lemma 6 bridge costs at most one total-budget slab.
The bound is independent of the number of arrival occurrences.
-/
theorem theorem8_sum_tradeoff_with_endpoint_error
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (k : ℕ) (hk : 0 < k) (I : PaperInstance Advertiser Query)
    (history : List Query) (opt : Fin history.length → Option Advertiser)
    (hbid : I.NonnegativeBids) (hbudget : I.PositiveBudgets)
    (hsmall : ∀ a q, I.bid a q ≤ I.budget a / (k : ℝ))
    (finalType : Advertiser → Fin k)
    (hfinalType : ∀ a, IsFinalType k
      ((runTheorem8DiscreteOccurrences k hk I history).spent a / I.budget a)
      (finalType a))
    (hoptFeasible : ∀ a, occurrenceSpend I history opt a ≤ I.budget a) :
    (∑ t : Fin history.length,
      theorem8OptWeightedRevenueAt k I history opt finalType t) ≤
      (∑ t : Fin history.length,
        theorem8AlgWeightedRevenueAt k hk I history t) +
        (∑ a : Advertiser, I.budget a) / (k : ℝ) := by
  calc
    (∑ t : Fin history.length,
        theorem8OptWeightedRevenueAt k I history opt finalType t) ≤
        ∑ t : Fin history.length,
          (theorem8AlgWeightedRevenueAt k hk I history t +
            endpointRoundingErrorAt k I history opt finalType
              (theorem8CurrentSlabAt k hk I history) t) := by
          exact Finset.sum_le_sum fun t _ =>
            theorem8_per_occurrence_tradeoff_with_endpoint_error
              k hk I history t opt hbid hbudget hsmall finalType hfinalType
    _ = (∑ t : Fin history.length,
          theorem8AlgWeightedRevenueAt k hk I history t) +
        ∑ t : Fin history.length,
          endpointRoundingErrorAt k I history opt finalType
            (theorem8CurrentSlabAt k hk I history) t := Finset.sum_add_distrib
    _ ≤ (∑ t : Fin history.length,
          theorem8AlgWeightedRevenueAt k hk I history t) +
        (∑ a : Advertiser, I.budget a) / (k : ℝ) := by
          exact add_le_add_right
            (theorem8_sum_endpointRoundingErrorAt_le_total_budget_div
              k hk I history opt hbid hbudget finalType hfinalType hoptFeasible) _

/-- Every spent fraction in the feasible unit interval has a source final type. -/
theorem exists_finalType
    (k : ℕ) (hk : 0 < k) (x : ℝ) (hxnonneg : 0 ≤ x) (hxle : x ≤ 1) :
    ∃ i : Fin k, IsFinalType k x i := by
  by_cases hxzero : x = 0
  · refine ⟨⟨0, hk⟩, Or.inl ?_⟩
    simp [hxzero]
  · have hxpos : 0 < x := lt_of_le_of_ne hxnonneg (Ne.symm hxzero)
    have hkReal : 0 < (k : ℝ) := by exact_mod_cast hk
    let c : ℤ := ⌈(k : ℝ) * x⌉
    have hcpos : 0 < c := by
      rw [show c = ⌈(k : ℝ) * x⌉ by rfl, Int.ceil_pos]
      exact mul_pos hkReal hxpos
    have hcle : c ≤ (k : ℤ) := by
      rw [show c = ⌈(k : ℝ) * x⌉ by rfl, Int.ceil_le]
      norm_cast
      simpa [mul_comm] using mul_le_of_le_one_left hkReal.le hxle
    let n : ℕ := c.toNat
    have hnc : (n : ℤ) = c := by
      simp [n, Int.toNat_of_nonneg hcpos.le]
    have hnpos : 0 < n := by
      have : (0 : ℤ) < (n : ℤ) := by simpa [hnc] using hcpos
      exact_mod_cast this
    have hncReal : (n : ℝ) = (c : ℝ) := by
      exact_mod_cast hnc
    have hnle : n ≤ k := by
      have : (n : ℤ) ≤ (k : ℤ) := by simpa [hnc] using hcle
      exact_mod_cast this
    let i : Fin k := ⟨n - 1, by omega⟩
    refine ⟨i, Or.inr ?_⟩
    constructor
    · have hltZ : ((n - 1 : ℕ) : ℤ) < c := by
        rw [← hnc]
        omega
      have hlt : ((n - 1 : ℕ) : ℝ) < (k : ℝ) * x := by
        rw [← Int.cast_natCast]
        exact (Int.lt_ceil).mp (by simpa [c] using hltZ)
      have : ((n - 1 : ℕ) : ℝ) / (k : ℝ) < x :=
        (div_lt_iff₀ hkReal).2 (by simpa [mul_comm] using hlt)
      simpa [i] using this
    · have hleInt : (k : ℝ) * x ≤ (c : ℝ) := Int.le_ceil _
      have hle : (k : ℝ) * x ≤ (n : ℝ) := by linarith
      have : x ≤ (n : ℝ) / (k : ℝ) :=
        (le_div_iff₀ hkReal).2 (by simpa [mul_comm] using hle)
      simpa [i, Nat.sub_add_cancel (Nat.succ_le_iff.2 hnpos)] using this

/-- The completed finite Theorem 8 run induces a final type for each bidder. -/
theorem runTheorem8DiscreteOccurrences_has_final_types
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (k : ℕ) (hk : 0 < k) (I : PaperInstance Advertiser Query)
    (history : List Query) (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets) :
    ∃ finalType : Advertiser → Fin k, ∀ a,
      IsFinalType k
        ((runTheorem8DiscreteOccurrences k hk I history).spent a / I.budget a)
        (finalType a) := by
  have hnonneg := runTheorem8DiscreteOccurrences_nonnegative_spend
    k hk I history hbid
  have hfeasible := runTheorem8DiscreteOccurrences_budget_feasible
    k hk I history (fun a => (hbudget a).le)
  choose finalType hfinalType using fun a =>
    exists_finalType k hk
      ((runTheorem8DiscreteOccurrences k hk I history).spent a / I.budget a)
      (div_nonneg (hnonneg a) (hbudget a).le)
      ((div_le_one₀ (hbudget a)).2 (hfeasible a))
  exact ⟨finalType, hfinalType⟩

/-- Section 4's number `x_i` of bidders in final type `i+1`. -/
noncomputable def section4TypeCount
    {Advertiser : Type*} [Fintype Advertiser]
    (k : ℕ) (finalSpentFraction : Advertiser → ℝ) (i : Fin k) : ℝ :=
  ∑ a : Advertiser, if IsFinalType k (finalSpentFraction a) i then 1 else 0

/-- The idealized Section 4 slab-spend formula after the stated rounding simplification. -/
noncomputable def section4IdealizedSlabSpend
    {k : ℕ} (N : ℝ) (x : Fin k → ℝ) (i : Fin k) : ℝ :=
  N / (k : ℝ) -
    (∑ j ∈ Finset.Iio i, x j) / (k : ℝ)

/-- Section 4's displayed formula for `beta_i`. -/
theorem section4IdealizedSlabSpend_formula
    {k : ℕ} (N : ℝ) (x : Fin k → ℝ) (i : Fin k) :
    section4IdealizedSlabSpend N x i =
      N / (k : ℝ) - (∑ j ∈ Finset.Iio i, x j) / (k : ℝ) := by
  rfl

/--
The aggregate `N/k` discretization bound from the explicit per-bidder rounding
premise used in Section 4's informal small-bid argument.
-/
theorem section4_discretization_error_le_N_div_k
    {Advertiser : Type*} [Fintype Advertiser]
    {k : ℕ} (hk : 0 < k) (error : Advertiser → ℝ)
    (herror_nonneg : ∀ a, 0 ≤ error a)
    (herror : ∀ a, error a ≤ 1 / (k : ℝ)) :
    ∑ a : Advertiser, error a ≤
      (Fintype.card Advertiser : ℝ) / (k : ℝ) := by
  calc
    ∑ a : Advertiser, error a ≤
        ∑ _a : Advertiser, (1 / (k : ℝ)) :=
      Finset.sum_le_sum fun a _ => herror a
    _ = (Fintype.card Advertiser : ℝ) / (k : ℝ) := by
      simp [div_eq_mul_inv]

/-- Section 4's revenue-to-factor-LP bridge, separated from the LP optimum proof. -/
theorem section4_balance_revenue_factor_lp_bridge
    {k : ℕ} (N BAL Φ : ℝ)
    (hBAL : N - BAL ≤ Φ + N / (k : ℝ)) :
    N - Φ - N / (k : ℝ) ≤ BAL := by
  linarith

/-- Section 5's type-count vector `alpha`. -/
noncomputable abbrev section5AlphaTypeCount
    {Advertiser : Type*} [Fintype Advertiser]
    (k : ℕ) (finalSpentFraction : Advertiser → ℝ) : Fin k → ℝ :=
  section4TypeCount k finalSpentFraction

/--
The vector `a` used by Section 5's factor-revealing LP has the first `k - 1`
type counts: the terminal type is not an LP variable.  Writing `k = m + 1`
makes that source convention total, including the degenerate `m = 0` case.
-/
noncomputable def section5PreterminalAlphaTypeCount
    {Advertiser : Type*} [Fintype Advertiser]
    (m : ℕ) (finalSpentFraction : Advertiser → ℝ) : Fin m → ℝ :=
  fun i => section5AlphaTypeCount (m + 1) finalSpentFraction i.castSucc

/-- Each realized Section 5 preterminal type count is nonnegative. -/
theorem section5PreterminalAlphaTypeCount_nonnegative
    {Advertiser : Type*} [Fintype Advertiser]
    (m : ℕ) (finalSpentFraction : Advertiser → ℝ) (i : Fin m) :
    0 ≤ section5PreterminalAlphaTypeCount m finalSpentFraction i := by
  unfold section5PreterminalAlphaTypeCount section5AlphaTypeCount section4TypeCount
  apply Finset.sum_nonneg
  intro a _
  split_ifs <;> norm_num

/--
The preterminal type-count vector induced by a chosen source final-type
classifier.  Keeping the classifier explicit is useful at right endpoints:
the runner fixes one deterministic, right-closed type for each bidder.
-/
noncomputable def theorem8PreterminalAlphaFromFinalTypes
    {Advertiser : Type*} [Fintype Advertiser]
    (m : ℕ) (finalType : Advertiser → Fin (m + 1)) : Fin m → ℝ :=
  fun i => ∑ a : Advertiser, if finalType a = i.castSucc then 1 else 0

/--
Prefix type counts are precisely the number of bidders whose chosen final
type lies strictly before that prefix boundary.
-/
theorem theorem8PreterminalAlphaFromFinalTypes_prefix
    {Advertiser : Type*} [Fintype Advertiser]
    (m : ℕ) (finalType : Advertiser → Fin (m + 1)) (i : Fin m) :
    (∑ j ∈ Finset.Iio i,
      theorem8PreterminalAlphaFromFinalTypes m finalType j) =
      ∑ a : Advertiser, if finalType a < i.castSucc then 1 else 0 := by
  classical
  unfold theorem8PreterminalAlphaFromFinalTypes
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : finalType a < i.castSucc
  · let j : Fin m := ⟨(finalType a).val, lt_trans ha i.isLt⟩
    have hjmem : j ∈ Finset.Iio i := by
      simp only [Finset.mem_Iio]
      change j.val < i.val
      exact ha
    have hj : finalType a = j.castSucc := by
      apply Fin.ext
      rfl
    have hterm :
        (fun x : Fin m => if finalType a = x.castSucc then (1 : ℝ) else 0) =
          fun x => if x = j then 1 else 0 := by
      funext x
      by_cases hx : x = j
      · subst x
        simp [hj]
      · have hne : finalType a ≠ x.castSucc := by
          intro h
          apply hx
          apply Fin.ext
          simpa [j] using congrArg Fin.val h.symm
        simp [hx, hne]
    rw [hterm, Finset.sum_ite_eq']
    simp [hjmem, ha]
  · have hzero : ∀ j ∈ Finset.Iio i,
        (if finalType a = j.castSucc then (1 : ℝ) else 0) = 0 := by
      intro j hj
      have hjlt : j < i := by simpa using (Finset.mem_Iio.mp hj)
      have hcast : j.castSucc < i.castSucc := by
        exact hjlt
      by_cases heq : finalType a = j.castSucc
      · exfalso
        apply ha
        simpa [heq] using hcast
      · simp [heq]
    rw [Finset.sum_eq_zero hzero]
    simp [ha]

/--
The finite event ledger underlying Section 4's stated idealization.  Each
event is one OPT-assigned query; `payment` is its common interested-bid value.
The local score comparison is the BALANCE choice rule on that event.  The last
field is the exact-type/no-straddling accounting convention explicitly adopted
by the source immediately after Lemma 1: an advertiser whose final type has
not ended before a slab contributes one slab width there, and no other
advertiser contributes.
-/
structure Section4IdealizedBalanceExecution
    (m : ℕ) (Advertiser Event : Type*)
    [Fintype Advertiser] [Fintype Event] where
  payment : Event → ℝ
  optOwner : Event → Advertiser
  finalType : Advertiser → Fin (m + 1)
  optCurrentSlab : Event → Fin (m + 1)
  balanceSlab : Event → Fin (m + 1)
  psi : Fin (m + 1) → ℝ
  optCurrent_le_final : ∀ event,
    optCurrentSlab event ≤ finalType (optOwner event)
  balance_choice : ∀ event,
    payment event * psi (optCurrentSlab event) ≤
      payment event * psi (balanceSlab event)
  payment_nonneg : ∀ event, 0 ≤ payment event
  psi_strictAnti : StrictAnti psi
  opt_exhausts_unit_budget : ∀ advertiser,
    (∑ event : Event,
      if optOwner event = advertiser then payment event else 0) = 1
  slab_payment_eq_width_of_final_type : ∀ slab,
    (∑ event : Event,
      if balanceSlab event = slab then payment event else 0) =
      ∑ advertiser : Advertiser,
        if slab ≤ finalType advertiser then 1 / ((m + 1 : ℕ) : ℝ) else 0

namespace Section4IdealizedBalanceExecution

/-- The Section 4 preterminal type-count vector induced by the idealized run. -/
noncomputable abbrev typeCount
    {m : ℕ} {Advertiser Event : Type*} [Fintype Advertiser] [Fintype Event]
    (E : Section4IdealizedBalanceExecution m Advertiser Event) : Fin m → ℝ :=
  theorem8PreterminalAlphaFromFinalTypes m E.finalType

/--
Lemma 1 at one event of the idealized Section 4 BALANCE ledger.  The result is
the order relation between the BALANCE slab and the OPT owner's final type.
-/
theorem balanceSlab_le_finalType
    {m : ℕ} {Advertiser Event : Type*} [Fintype Advertiser] [Fintype Event]
    (E : Section4IdealizedBalanceExecution m Advertiser Event) (event : Event)
    (hpayment : 0 < E.payment event) :
    E.balanceSlab event ≤ E.finalType (E.optOwner event) := by
  exact MSVV07SourceLemmas.lemma1_balance_pays_no_later_slab
    E.psi (E.optCurrent_le_final event) (E.balance_choice event) rfl
      hpayment E.psi_strictAnti

/-- Total OPT payment whose owner's final type lies in the Section 4 prefix. -/
noncomputable def optPrefixPayment
    {m : ℕ} {Advertiser Event : Type*} [Fintype Advertiser] [Fintype Event]
    (E : Section4IdealizedBalanceExecution m Advertiser Event) (i : Fin m) : ℝ :=
  ∑ event : Event,
    if E.finalType (E.optOwner event) ≤ i.castSucc then E.payment event else 0

/-- Total BALANCE payment made from the same Section 4 slab prefix. -/
noncomputable def balancePrefixPayment
    {m : ℕ} {Advertiser Event : Type*} [Fintype Advertiser] [Fintype Event]
    (E : Section4IdealizedBalanceExecution m Advertiser Event) (i : Fin m) : ℝ :=
  ∑ event : Event,
    if E.balanceSlab event ≤ i.castSucc then E.payment event else 0

/--
The actual OPT event ledger, under the source's exhausted-unit-budget
normalization, has exactly the final-type mass recorded by the Section 4
prefix of `x`.
-/
theorem typeCount_prefix_eq_optPrefixPayment
    {m : ℕ} {Advertiser Event : Type*} [Fintype Advertiser] [Fintype Event]
    (E : Section4IdealizedBalanceExecution m Advertiser Event) (i : Fin m) :
    (∑ j ∈ MSVV07SourceLemmas.paperRoutePrefix i, E.typeCount j) =
      E.optPrefixPayment i := by
  classical
  unfold typeCount optPrefixPayment theorem8PreterminalAlphaFromFinalTypes
  calc
    (∑ j ∈ MSVV07SourceLemmas.paperRoutePrefix i,
        ∑ a : Advertiser, if E.finalType a = j.castSucc then 1 else 0) =
        ∑ a : Advertiser,
          if E.finalType a ≤ i.castSucc then 1 else 0 := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro a _
            by_cases ha : E.finalType a ≤ i.castSucc
            · let j : Fin m := ⟨(E.finalType a).val, lt_of_le_of_lt ha i.isLt⟩
              have hjmem : j ∈ MSVV07SourceLemmas.paperRoutePrefix i := by
                rw [MSVV07SourceLemmas.paperRoutePrefix_eq_Iic]
                simp only [Finset.mem_Iic]
                change j.val ≤ i.val
                exact ha
              have hj : E.finalType a = j.castSucc := by
                apply Fin.ext
                rfl
              have hterm :
                  (fun x : Fin m =>
                    if E.finalType a = x.castSucc then (1 : ℝ) else 0) =
                    fun x => if x = j then 1 else 0 := by
                      funext x
                      by_cases hx : x = j
                      · subst x
                        simp [hj]
                      · have hne : E.finalType a ≠ x.castSucc := by
                          intro h
                          apply hx
                          apply Fin.ext
                          simpa [j] using congrArg Fin.val h.symm
                        simp [hx, hne]
              rw [hterm, Finset.sum_ite_eq']
              simp [hjmem, ha]
            · have hzero : ∀ j ∈ MSVV07SourceLemmas.paperRoutePrefix i,
                  (if E.finalType a = j.castSucc then (1 : ℝ) else 0) = 0 := by
                    intro j hj
                    have hjle : j ≤ i := by
                      rw [MSVV07SourceLemmas.paperRoutePrefix_eq_Iic] at hj
                      exact Finset.mem_Iic.mp hj
                    have hcast : j.castSucc ≤ i.castSucc := by
                      exact hjle
                    by_cases heq : E.finalType a = j.castSucc
                    · exfalso
                      apply ha
                      simpa [heq] using hcast
                    · simp [heq]
              rw [Finset.sum_eq_zero hzero]
              simp [ha]
    _ = ∑ a : Advertiser,
          if E.finalType a ≤ i.castSucc then
            ∑ event : Event,
              if E.optOwner event = a then E.payment event else 0
          else 0 := by
            apply Finset.sum_congr rfl
            intro a _
            rw [E.opt_exhausts_unit_budget a]
    _ = ∑ event : Event, ∑ a : Advertiser,
          if E.finalType a ≤ i.castSucc then
            if E.optOwner event = a then E.payment event else 0
          else 0 := by
            calc
              (∑ a : Advertiser,
                if E.finalType a ≤ i.castSucc then
                  ∑ event : Event,
                    if E.optOwner event = a then E.payment event else 0
                else 0) =
                ∑ a : Advertiser, ∑ event : Event,
                  if E.finalType a ≤ i.castSucc then
                    if E.optOwner event = a then E.payment event else 0
                  else 0 := by
                    apply Finset.sum_congr rfl
                    intro a _
                    by_cases htype : E.finalType a ≤ i.castSucc
                    · simp [htype]
                    · simp [htype]
              _ = _ := Finset.sum_comm
    _ = ∑ event : Event,
          if E.finalType (E.optOwner event) ≤ i.castSucc then E.payment event else 0 := by
            apply Finset.sum_congr rfl
            intro event _
            by_cases htype : E.finalType (E.optOwner event) ≤ i.castSucc
            · rw [if_pos htype]
              have hsum := Fintype.sum_eq_single (E.optOwner event)
                (f := fun a : Advertiser =>
                  if E.finalType a ≤ i.castSucc then
                    if E.optOwner event = a then E.payment event else 0
                  else 0)
                (fun a hne => by
                  have howner : E.optOwner event ≠ a := Ne.symm hne
                  simp [howner])
              simpa [htype] using hsum
            · rw [if_neg htype]
              have hsum :
                  (∑ a : Advertiser,
                    if E.finalType a ≤ i.castSucc then
                      if E.optOwner event = a then E.payment event else 0
                    else 0) = 0 := by
                      apply Fintype.sum_eq_zero
                      intro a
                      by_cases howner : E.optOwner event = a
                      · subst a
                        simp [htype]
                      · simp [howner]
              exact hsum

end Section4IdealizedBalanceExecution

/--
Under the Section 2 unit-budget normalization, the final-type budget mass at
a preterminal slab is exactly the paper's idealized Section 4 beta value.
-/
theorem theorem8_finalType_unit_budget_mass_eq_ideal_beta
    {Advertiser : Type*} [Fintype Advertiser]
    (m : ℕ) (finalType : Advertiser → Fin (m + 1)) (i : Fin m) :
    (∑ a : Advertiser,
      if i.castSucc ≤ finalType a then 1 / ((m + 1 : ℕ) : ℝ) else 0) =
      MSVV07SourceLemmas.paperRouteIdealBeta (Fintype.card Advertiser : ℝ)
        (theorem8PreterminalAlphaFromFinalTypes m finalType) i := by
  classical
  have hpref :
      (∑ j ∈ Finset.Iio i,
        theorem8PreterminalAlphaFromFinalTypes m finalType j) =
        ∑ a : Advertiser, if finalType a < i.castSucc then 1 else 0 := by
    exact theorem8PreterminalAlphaFromFinalTypes_prefix m finalType i
  unfold MSVV07SourceLemmas.paperRouteIdealBeta
  rw [hpref]
  calc
    (∑ a : Advertiser,
        if i.castSucc ≤ finalType a then 1 / ((m + 1 : ℕ) : ℝ) else 0) =
        ∑ a : Advertiser,
          (1 - (if finalType a < i.castSucc then 1 else 0)) /
            ((m + 1 : ℕ) : ℝ) := by
          apply Finset.sum_congr rfl
          intro a _
          by_cases htype : i.castSucc ≤ finalType a
          · have hnot : ¬ finalType a < i.castSucc := not_lt_of_ge htype
            simp [htype, hnot]
          · have hbefore : finalType a < i.castSucc := lt_of_not_ge htype
            simp [htype, hbefore]
    _ = ∑ a : Advertiser,
          (1 / ((m + 1 : ℕ) : ℝ) -
            (if finalType a < i.castSucc then 1 else 0) /
              ((m + 1 : ℕ) : ℝ)) := by
          apply Finset.sum_congr rfl
          intro a _
          ring
    _ = (∑ _a : Advertiser, (1 : ℝ)) / ((m + 1 : ℕ) : ℝ) -
          (∑ a : Advertiser,
            if finalType a < i.castSucc then 1 else 0) /
            ((m + 1 : ℕ) : ℝ) := by
          rw [Finset.sum_sub_distrib, Finset.sum_div, Finset.sum_div]
    _ = _ := by
      simp [div_eq_mul_inv]

namespace Section4IdealizedBalanceExecution

/--
Lemma 1 aggregated over a Section 4 prefix: every OPT payment in that prefix
is also a BALANCE payment in the same prefix.
-/
theorem optPrefixPayment_le_balancePrefixPayment
    {m : ℕ} {Advertiser Event : Type*} [Fintype Advertiser] [Fintype Event]
    (E : Section4IdealizedBalanceExecution m Advertiser Event) (i : Fin m) :
    E.optPrefixPayment i ≤ E.balancePrefixPayment i := by
  unfold optPrefixPayment balancePrefixPayment
  apply Finset.sum_le_sum
  intro event _
  by_cases htype : E.finalType (E.optOwner event) ≤ i.castSucc
  · by_cases hpayment : 0 < E.payment event
    · have hslab : E.balanceSlab event ≤ i.castSucc :=
        (E.balanceSlab_le_finalType event hpayment).trans htype
      simp [htype, hslab]
    · have hzero : E.payment event = 0 :=
        le_antisymm (le_of_not_gt hpayment) (E.payment_nonneg event)
      simp [hzero]
  · by_cases hslab : E.balanceSlab event ≤ i.castSucc
    · exact (by simp [htype, hslab, E.payment_nonneg event])
    · simp [htype, hslab]

/--
The exact-type/no-straddling convention turns the actual BALANCE event ledger
into the source's ideal beta total on every Section 4 prefix.
-/
theorem balancePrefixPayment_eq_idealBeta_prefix
    {m : ℕ} {Advertiser Event : Type*} [Fintype Advertiser] [Fintype Event]
    (E : Section4IdealizedBalanceExecution m Advertiser Event) (i : Fin m) :
    E.balancePrefixPayment i =
      ∑ j ∈ MSVV07SourceLemmas.paperRoutePrefix i,
        MSVV07SourceLemmas.paperRouteIdealBeta (Fintype.card Advertiser : ℝ)
          E.typeCount j := by
  classical
  unfold balancePrefixPayment
  calc
    (∑ event : Event,
        if E.balanceSlab event ≤ i.castSucc then E.payment event else 0) =
        ∑ j ∈ MSVV07SourceLemmas.paperRoutePrefix i,
          ∑ event : Event,
            if E.balanceSlab event = j.castSucc then E.payment event else 0 := by
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro event _
              by_cases hslab : E.balanceSlab event ≤ i.castSucc
              · let j : Fin m := ⟨(E.balanceSlab event).val,
                    lt_of_le_of_lt hslab i.isLt⟩
                have hjmem : j ∈ MSVV07SourceLemmas.paperRoutePrefix i := by
                  rw [MSVV07SourceLemmas.paperRoutePrefix_eq_Iic]
                  simp only [Finset.mem_Iic]
                  change j.val ≤ i.val
                  exact hslab
                have hj : E.balanceSlab event = j.castSucc := by
                  apply Fin.ext
                  rfl
                have hterm :
                    (fun x : Fin m =>
                      if E.balanceSlab event = x.castSucc then E.payment event else 0) =
                      fun x => if x = j then E.payment event else 0 := by
                        funext x
                        by_cases hx : x = j
                        · subst x
                          simp [hj]
                        · have hne : E.balanceSlab event ≠ x.castSucc := by
                            intro h
                            apply hx
                            apply Fin.ext
                            simpa [j] using congrArg Fin.val h.symm
                          simp [hx, hne]
                rw [hterm, Finset.sum_ite_eq']
                simp [hjmem, hslab]
              · have hzero : ∀ j ∈ MSVV07SourceLemmas.paperRoutePrefix i,
                    (if E.balanceSlab event = j.castSucc then E.payment event else 0) = 0 := by
                      intro j hj
                      have hjle : j ≤ i := by
                        rw [MSVV07SourceLemmas.paperRoutePrefix_eq_Iic] at hj
                        exact Finset.mem_Iic.mp hj
                      have hcast : j.castSucc ≤ i.castSucc := by
                        exact hjle
                      by_cases heq : E.balanceSlab event = j.castSucc
                      · exfalso
                        apply hslab
                        simpa [heq] using hcast
                      · simp [heq]
                rw [Finset.sum_eq_zero hzero]
                simp [hslab]
    _ = ∑ j ∈ MSVV07SourceLemmas.paperRoutePrefix i,
          ∑ a : Advertiser,
            if j.castSucc ≤ E.finalType a then 1 / ((m + 1 : ℕ) : ℝ) else 0 := by
              apply Finset.sum_congr rfl
              intro j _
              rw [E.slab_payment_eq_width_of_final_type j.castSucc]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      simpa [typeCount] using
        (theorem8_finalType_unit_budget_mass_eq_ideal_beta
          (Advertiser := Advertiser) m E.finalType j)

/--
The source's Lemma-1 prefix accounting, derived from the idealized execution
rather than accepted as a caller certificate.
-/
theorem prefix_accounting
    {m : ℕ} {Advertiser Event : Type*} [Fintype Advertiser] [Fintype Event]
    (E : Section4IdealizedBalanceExecution m Advertiser Event) (i : Fin m) :
    (∑ j ∈ MSVV07SourceLemmas.paperRoutePrefix i, E.typeCount j) ≤
      ∑ j ∈ MSVV07SourceLemmas.paperRoutePrefix i,
        MSVV07SourceLemmas.paperRouteIdealBeta (Fintype.card Advertiser : ℝ)
          E.typeCount j := by
  calc
    (∑ j ∈ MSVV07SourceLemmas.paperRoutePrefix i, E.typeCount j) =
        E.optPrefixPayment i := E.typeCount_prefix_eq_optPrefixPayment i
    _ ≤ E.balancePrefixPayment i := E.optPrefixPayment_le_balancePrefixPayment i
    _ = _ := E.balancePrefixPayment_eq_idealBeta_prefix i

/--
Section 4 Lemma 2 for the source's finite idealized BALANCE execution.  Its
LP row follows from the local BALANCE choice rule, the exhausted-OPT
normalization, and the source's exact-type/no-straddling convention.
-/
theorem factor_revealing_lp_constraint
    {m : ℕ} {Advertiser Event : Type*} [Fintype Advertiser] [Fintype Event]
    (E : Section4IdealizedBalanceExecution m Advertiser Event) (i : Fin m) :
    MSVV07SourceLemmas.paperRouteLPRow E.typeCount i ≤
      MSVV07SourceLemmas.paperRouteRhs (Fintype.card Advertiser : ℝ) i := by
  exact MSVV07SourceLemmas.lemma2_factor_revealing_lp_constraint
    (Fintype.card Advertiser : ℝ) E.typeCount
    (MSVV07SourceLemmas.paperRouteIdealBeta (Fintype.card Advertiser : ℝ)
      E.typeCount) i
    (E.prefix_accounting i)
    (MSVV07SourceLemmas.paperRouteIdealBeta_prefix
      (Fintype.card Advertiser : ℝ) E.typeCount i)

end Section4IdealizedBalanceExecution

/-- Every source final type lies at or above its lower slab endpoint. -/
theorem finalType_fraction_lower_endpoint_le
    {k : ℕ} (_hk : 0 < k) (spentFraction : ℝ) (i : Fin k)
    (htype : IsFinalType k spentFraction i) :
    (i.val : ℝ) / (k : ℝ) ≤ spentFraction := by
  rcases htype with ⟨hzero, hindex⟩ | ⟨hlower, _⟩
  · subst spentFraction
    have hval : i.val = 0 := hindex
    simp [hval]
  · exact hlower.le

/--
For one unit-budget bidder, its unspent budget is at most the source
preterminal objective contribution of its final type plus one slab width.  The
terminal type contributes only that final slab width.
-/
theorem finalType_unit_unspent_le_preterminal_objective_add_slab
    {Advertiser Query : Type*} [Fintype Advertiser]
    (m : ℕ) (I : PaperInstance Advertiser Query) (hunit : EqualUnitBudgets I)
    (finalSpend : Advertiser → ℝ) (finalType : Advertiser → Fin (m + 1))
    (hfinalType : ∀ a, IsFinalType (m + 1)
      (finalSpend a / I.budget a) (finalType a)) (a : Advertiser) :
    1 - finalSpend a ≤
      (∑ i : Fin m, MSVV07SourceLemmas.paperRoutePrimalObjectiveCoeff i *
        (if finalType a = i.castSucc then 1 else 0)) +
        1 / ((m + 1 : ℕ) : ℝ) := by
  have hlower := finalType_fraction_lower_endpoint_le (Nat.zero_lt_succ m)
    (finalSpend a / I.budget a) (finalType a) (hfinalType a)
  rw [hunit a] at hlower
  simp only [div_one] at hlower
  have hpoint : ∀ ft : Fin (m + 1),
      (ft.val : ℝ) / ((m + 1 : ℕ) : ℝ) ≤ finalSpend a →
      1 - finalSpend a ≤
        (∑ i : Fin m, MSVV07SourceLemmas.paperRoutePrimalObjectiveCoeff i *
          (if ft = i.castSucc then 1 else 0)) +
          1 / ((m + 1 : ℕ) : ℝ) := by
    intro ft
    refine Fin.lastCases (motive := fun ft =>
      (ft.val : ℝ) / ((m + 1 : ℕ) : ℝ) ≤ finalSpend a →
        1 - finalSpend a ≤
          (∑ i : Fin m, MSVV07SourceLemmas.paperRoutePrimalObjectiveCoeff i *
            (if ft = i.castSucc then 1 else 0)) +
            1 / ((m + 1 : ℕ) : ℝ)) ?_ (fun j => ?_) ft
    · intro hft
      have hbase : 1 - finalSpend a ≤
          1 - ((Fin.last m).val : ℝ) / ((m + 1 : ℕ) : ℝ) := by
        linarith
      have hsum :
          (∑ i : Fin m, MSVV07SourceLemmas.paperRoutePrimalObjectiveCoeff i *
            (if Fin.last m = i.castSucc then 1 else 0)) = 0 := by
          apply Finset.sum_eq_zero
          intro i _
          have hne : Fin.last m ≠ i.castSucc := by
            intro h
            have hval := congrArg Fin.val h
            simp only [Fin.val_last, Fin.val_castSucc] at hval
            omega
          simp [hne]
      rw [hsum]
      calc
        1 - finalSpend a ≤ 1 - ((Fin.last m).val : ℝ) / ((m + 1 : ℕ) : ℝ) := hbase
        _ = 1 / ((m + 1 : ℕ) : ℝ) := by
          simp only [Fin.val_last]
          have hne : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
          push_cast
          field_simp
          ring
        _ ≤ 0 + 1 / ((m + 1 : ℕ) : ℝ) := by norm_num
    · intro hft
      have hbase : 1 - finalSpend a ≤
          1 - (j.val : ℝ) / ((m + 1 : ℕ) : ℝ) := by
        have hft' : (j.val : ℝ) / ((m + 1 : ℕ) : ℝ) ≤ finalSpend a := by
          simpa only [Fin.val_castSucc] using hft
        linarith
      have hsum :
          (∑ i : Fin m, MSVV07SourceLemmas.paperRoutePrimalObjectiveCoeff i *
            (if j.castSucc = i.castSucc then 1 else 0)) =
              MSVV07SourceLemmas.paperRoutePrimalObjectiveCoeff j := by
          rw [Fintype.sum_eq_single j]
          · simp
          · intro i hne
            have hcast : j.castSucc ≠ i.castSucc := by
              intro h
              apply hne
              exact Fin.castSucc_injective m h.symm
            simp [hcast]
      rw [hsum]
      calc
        1 - finalSpend a ≤ 1 - (j.val : ℝ) / ((m + 1 : ℕ) : ℝ) := hbase
        _ = MSVV07SourceLemmas.paperRoutePrimalObjectiveCoeff j +
            1 / ((m + 1 : ℕ) : ℝ) := by
            unfold MSVV07SourceLemmas.paperRoutePrimalObjectiveCoeff
            have hjle : j.val ≤ m := Nat.le_of_lt j.isLt
            rw [Nat.cast_sub hjle]
            have hne : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
            push_cast
            field_simp
            ring
  exact hpoint (finalType a) hlower

/--
The whole unit-budget Theorem 8 run leaves at most its preterminal source-LP
objective plus one aggregate slab width unspent.
-/
theorem theorem8_unspent_le_preterminal_objective_with_error
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (m : ℕ) (I : PaperInstance Advertiser Query) (history : List Query)
    (hunit : EqualUnitBudgets I)
    (finalType : Advertiser → Fin (m + 1))
    (hfinalType : ∀ a, IsFinalType (m + 1)
      ((runTheorem8DiscreteOccurrences (m + 1) (Nat.zero_lt_succ m) I history).spent a /
        I.budget a) (finalType a)) :
    (Fintype.card Advertiser : ℝ) -
      (runTheorem8DiscreteOccurrences (m + 1) (Nat.zero_lt_succ m) I history).revenue ≤
      MSVV07SourceLemmas.paperRoutePrimalObjective
        (theorem8PreterminalAlphaFromFinalTypes m finalType) +
        (Fintype.card Advertiser : ℝ) / ((m + 1 : ℕ) : ℝ) := by
  let finalSpend :=
    (runTheorem8DiscreteOccurrences (m + 1) (Nat.zero_lt_succ m) I history).spent
  have hpoint : ∀ a : Advertiser,
      1 - finalSpend a ≤
        (∑ i : Fin m, MSVV07SourceLemmas.paperRoutePrimalObjectiveCoeff i *
          (if finalType a = i.castSucc then 1 else 0)) +
          1 / ((m + 1 : ℕ) : ℝ) := by
    intro a
    exact finalType_unit_unspent_le_preterminal_objective_add_slab
      m I hunit finalSpend finalType hfinalType a
  have hrevenue := runTheorem8DiscreteOccurrences_totalSpend_eq_revenue
    (m + 1) (Nat.zero_lt_succ m) I history
  change (Fintype.card Advertiser : ℝ) -
      (runTheorem8DiscreteOccurrences (m + 1) (Nat.zero_lt_succ m) I history).revenue ≤ _
  rw [← hrevenue]
  unfold occurrenceStateTotalSpend
  calc
    (Fintype.card Advertiser : ℝ) - ∑ a : Advertiser, finalSpend a =
        ∑ a : Advertiser, (1 - finalSpend a) := by
          rw [Finset.sum_sub_distrib]
          simp
    _ ≤ ∑ a : Advertiser,
        ((∑ i : Fin m, MSVV07SourceLemmas.paperRoutePrimalObjectiveCoeff i *
          (if finalType a = i.castSucc then 1 else 0)) +
          1 / ((m + 1 : ℕ) : ℝ)) := by
          apply Finset.sum_le_sum
          intro a _
          exact hpoint a
    _ = (∑ i : Fin m, MSVV07SourceLemmas.paperRoutePrimalObjectiveCoeff i *
        theorem8PreterminalAlphaFromFinalTypes m finalType i) +
        (Fintype.card Advertiser : ℝ) / ((m + 1 : ℕ) : ℝ) := by
          rw [Finset.sum_add_distrib]
          congr 1
          · unfold theorem8PreterminalAlphaFromFinalTypes
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
          · simp [div_eq_mul_inv]
    _ = _ := by rfl

/-- The final spent-budget fraction produced by a Section 5 tradeoff run. -/
noncomputable def section5TradeoffRunSpentFraction
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (psi : ℝ → ℝ) (I : PaperInstance Advertiser Query) (history : List Query) :
    Advertiser → ℝ :=
  fun a => (runTradeoffOccurrences psi I history).spent a / I.budget a

/--
Section 5's `k-1`-coordinate type-count vector for the actual run on an
instance with tradeoff `psi` (with `k = m + 1`).
-/
noncomputable def section5PreterminalAlphaTypeCountOfTradeoffRun
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (m : ℕ) (psi : ℝ → ℝ) (I : PaperInstance Advertiser Query)
    (history : List Query) : Fin m → ℝ :=
  section5PreterminalAlphaTypeCount m
    (section5TradeoffRunSpentFraction psi I history)

/-- Actual-run Section 5 type counts are nonnegative. -/
theorem section5PreterminalAlphaTypeCountOfTradeoffRun_nonnegative
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (m : ℕ) (psi : ℝ → ℝ) (I : PaperInstance Advertiser Query)
    (history : List Query) (i : Fin m) :
    0 ≤ section5PreterminalAlphaTypeCountOfTradeoffRun m psi I history i := by
  exact section5PreterminalAlphaTypeCount_nonnegative m
    (section5TradeoffRunSpentFraction psi I history) i

/-- Section 5's idealized slab-spend vector `beta`. -/
noncomputable abbrev section5IdealizedBeta
    {k : ℕ} (N : ℝ) (alpha : Fin k → ℝ) : Fin k → ℝ :=
  section4IdealizedSlabSpend N alpha

/-- Section 5's prefix perturbation `Delta_i = sum_{j <= i}(alpha_j-beta_j)`. -/
noncomputable def section5Delta
    {k : ℕ} (alpha beta : Fin k → ℝ) (i : Fin k) : ℝ :=
  ∑ j ∈ Finset.Iic i, (alpha j - beta j)

/-- `ALG(q)` for one recorded occurrence decision. -/
noncomputable def section5AlgQueryRevenue
    (I : PaperInstance Advertiser Query)
    (d : OccurrenceDecision Advertiser Query) : ℝ :=
  match d.winner with
  | none => 0
  | some a => I.bid a d.query

/-- `OPT(q)` for occurrence `t`, so repeated query words remain distinct. -/
noncomputable def section5OptQueryRevenue
    (I : PaperInstance Advertiser Query) (history : List Query)
    (opt : Fin history.length → Option Advertiser) (t : Fin history.length) : ℝ :=
  occurrenceRevenueAt I history opt t

/-- OPT revenue over the fiber of occurrences whose owner has final type `i`. -/
noncomputable def section5OptTypeFiberRevenue
    (I : PaperInstance Advertiser Query) (history : List Query)
    (opt : Fin history.length → Option Advertiser)
    (finalType : Advertiser → Fin k) (i : Fin k) : ℝ :=
  ∑ t : Fin history.length,
    match opt t with
    | none => 0
    | some a => if finalType a = i then I.bid a (history.get t) else 0

/-- Query type induced by OPT's owner and the online run's final bidder type classifier. -/
def section5QueryType
    (optOwner : Option Advertiser) (finalType : Advertiser → Fin k) : Option (Fin k) :=
  optOwner.map finalType

/-- Slab from which the online algorithm paid for a recorded occurrence. -/
noncomputable def section5QuerySlab
    (k : ℕ) (hk : 0 < k) (I : PaperInstance Advertiser Query)
    (d : OccurrenceDecision Advertiser Query) : Option (Fin k) :=
  d.winner.map fun a => activeBudgetSlab k hk (d.spentBefore a) (I.budget a)

/-- ALG revenue over the fiber of recorded occurrences paid from slab `i`. -/
noncomputable def section5AlgSlabFiberRevenue
    (k : ℕ) (hk : 0 < k) (I : PaperInstance Advertiser Query)
    (decisions : List (OccurrenceDecision Advertiser Query)) (i : Fin k) : ℝ :=
  (decisions.map fun d =>
    if section5QuerySlab k hk I d = some i then
      section5AlgQueryRevenue I d
    else 0).sum

/--
Under the Section 2--5 unit-budget exhaustive-OPT assumption, OPT revenue over
a final-type fiber equals the number of bidders in that fiber.
-/
theorem section5_opt_type_fiber_revenue_eq_type_count
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    {k : ℕ} (I : PaperInstance Advertiser Query) (history : List Query)
    (opt : Fin history.length → Option Advertiser)
    (finalType : Advertiser → Fin k)
    (hexhaust : ∀ a, occurrenceSpend I history opt a = 1)
    (i : Fin k) :
    section5OptTypeFiberRevenue I history opt finalType i =
      ∑ a : Advertiser, if finalType a = i then 1 else 0 := by
  classical
  calc
    section5OptTypeFiberRevenue I history opt finalType i =
        ∑ t : Fin history.length, ∑ a : Advertiser,
          if finalType a = i then
            match opt t with
            | none => 0
            | some owner => if owner = a then I.bid a (history.get t) else 0
          else 0 := by
            unfold section5OptTypeFiberRevenue
            apply Finset.sum_congr rfl
            intro t _
            cases hopt : opt t with
            | none => simp [hopt]
            | some owner =>
                by_cases htype : finalType owner = i
                · simp only [hopt]
                  rw [if_pos htype]
                  symm
                  have hsum := Fintype.sum_eq_single owner
                    (f := fun b : Advertiser =>
                      if finalType b = i then
                        if owner = b then I.bid b (history.get t) else 0
                      else 0)
                    (fun b hne => by
                      have howner : owner ≠ b := Ne.symm hne
                      simp [howner])
                  simpa [htype] using hsum
                · simp only [hopt]
                  rw [if_neg htype]
                  symm
                  apply Fintype.sum_eq_zero
                  intro b
                  by_cases howner : owner = b
                  · subst b
                    simp [htype]
                  · simp [howner]
    _ = ∑ a : Advertiser, ∑ t : Fin history.length,
          if finalType a = i then
            match opt t with
            | none => 0
            | some owner => if owner = a then I.bid a (history.get t) else 0
          else 0 := Finset.sum_comm
    _ = ∑ a : Advertiser,
          if finalType a = i then occurrenceSpend I history opt a else 0 := by
            apply Finset.sum_congr rfl
            intro a _
            by_cases htype : finalType a = i
            · simp [htype, occurrenceSpend]
            · simp [htype]
    _ = ∑ a : Advertiser, if finalType a = i then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro a _
          rw [hexhaust a]

/--
Summing Theorem 8's OPT weights by occurrences is the same as summing by the
final-type fibers used in the source accounting.
-/
theorem theorem8_sum_optWeightedRevenue_eq_type_fibers
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    {k : ℕ} (I : PaperInstance Advertiser Query) (history : List Query)
    (opt : Fin history.length → Option Advertiser)
    (finalType : Advertiser → Fin k) :
    (∑ t : Fin history.length,
      theorem8OptWeightedRevenueAt k I history opt finalType t) =
      ∑ i : Fin k, theorem8DiscreteTradeoff k i *
        section5OptTypeFiberRevenue I history opt finalType i := by
  classical
  unfold theorem8OptWeightedRevenueAt section5OptTypeFiberRevenue
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  cases hopt : opt t with
  | none => simp
  | some a =>
    simp only [hopt]
    have hsum := Fintype.sum_eq_single (finalType a)
      (f := fun i : Fin k =>
        theorem8DiscreteTradeoff k i *
          (if finalType a = i then I.bid a (history.get t) else 0))
      (fun i hne => by
        have htype : finalType a ≠ i := Ne.symm hne
        simp [htype])
    calc
      I.bid a (history.get t) * theorem8DiscreteTradeoff k (finalType a) =
          theorem8DiscreteTradeoff k (finalType a) * I.bid a (history.get t) := by ring
      _ = ∑ i : Fin k, theorem8DiscreteTradeoff k i *
          (if finalType a = i then I.bid a (history.get t) else 0) := by
            symm
            simpa using hsum

/--
With unit budgets and an exhausting OPT assignment, the runner's weighted OPT
sum is exactly the source factor-LP objective applied to its preterminal final
type-count vector.  The terminal type vanishes because its tradeoff weight is
zero.
-/
theorem theorem8_sum_optWeightedRevenue_eq_preterminal_alpha
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (m : ℕ) (I : PaperInstance Advertiser Query) (history : List Query)
    (opt : Fin history.length → Option Advertiser)
    (finalType : Advertiser → Fin (m + 1))
    (hexhaust : ∀ a, occurrenceSpend I history opt a = 1) :
    (∑ t : Fin history.length,
      theorem8OptWeightedRevenueAt (m + 1) I history opt finalType t) =
      ∑ i : Fin m, MSVV07SourceLemmas.paperRoutePsiCandidate i *
        theorem8PreterminalAlphaFromFinalTypes m finalType i := by
  rw [theorem8_sum_optWeightedRevenue_eq_type_fibers]
  rw [Fin.sum_univ_castSucc]
  have hterminal : theorem8DiscreteTradeoff (m + 1) (Fin.last m) = 0 := by
    apply theorem8DiscreteTradeoff_terminal
    simp
  rw [hterminal]
  simp only [zero_mul, add_zero]
  apply Finset.sum_congr rfl
  intro i _
  rw [theorem8DiscreteTradeoff_castSucc_eq_paperRoutePsiCandidate]
  rw [section5_opt_type_fiber_revenue_eq_type_count I history opt finalType hexhaust]
  rfl

/-- Section 6's current type is the one-indexed active budget slab. -/
noncomputable abbrev section6CurrentType
    (k : ℕ) (hk : 0 < k) (spent budget : ℝ) : Fin k :=
  activeBudgetSlab k hk spent budget

/-- Lower endpoint of bidder `a`'s budget slab `i`. -/
noncomputable def section6SlabLower
    (k : ℕ) (I : PaperInstance Advertiser Query)
    (i : Fin k) (a : Advertiser) : ℝ :=
  I.budget a * (i.val : ℝ) / (k : ℝ)

/-- Upper endpoint of bidder `a`'s budget slab `i`. -/
noncomputable def section6SlabUpper
    (k : ℕ) (I : PaperInstance Advertiser Query)
    (i : Fin k) (a : Advertiser) : ℝ :=
  I.budget a * ((i.val + 1 : ℕ) : ℝ) / (k : ℝ)

/--
`beta_i^j`: the amount of bidder `a`'s final spend lying in budget interval
`[i B_a/k, (i+1) B_a/k]`.  The difference of clipped cumulative spends splits
a payment that crosses a slab boundary instead of assigning the whole payment
to its starting slab.
-/
noncomputable def section6BidderSlabSpend
    (k : ℕ) (I : PaperInstance Advertiser Query)
    (finalSpend : Advertiser → ℝ)
    (i : Fin k) (a : Advertiser) : ℝ :=
  min (finalSpend a) (section6SlabUpper k I i a) -
    min (finalSpend a) (section6SlabLower k I i a)

/-- `beta_i`: aggregate split payment from slab `i` across all bidders. -/
noncomputable def section6AggregateSlabSpend
    {Advertiser Query : Type*} [Fintype Advertiser]
    (k : ℕ) (I : PaperInstance Advertiser Query)
    (finalSpend : Advertiser → ℝ) (i : Fin k) : ℝ :=
  ∑ a : Advertiser, section6BidderSlabSpend k I finalSpend i a

/--
The split-payment slabs telescope to a bidder's final spend.  This is exact:
it does not require a no-straddling convention for individual arrivals.
-/
theorem sum_section6BidderSlabSpend_eq_finalSpend
    {Advertiser Query : Type*} {k : ℕ} (hk : 0 < k)
    (I : PaperInstance Advertiser Query) (finalSpend : Advertiser → ℝ)
    (hfinal_nonneg : ∀ a, 0 ≤ finalSpend a)
    (hfinal_feasible : ∀ a, finalSpend a ≤ I.budget a)
    (a : Advertiser) :
    ∑ i : Fin k, section6BidderSlabSpend k I finalSpend i a = finalSpend a := by
  let f : ℕ → ℝ := fun i =>
    min (finalSpend a) (I.budget a * (i : ℝ) / (k : ℝ))
  have hterm : ∀ i : Fin k,
      section6BidderSlabSpend k I finalSpend i a = f (i.val + 1) - f i.val := by
    intro i
    simp only [section6BidderSlabSpend, section6SlabUpper, section6SlabLower, f]
  have hkReal : (k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hk)
  have hfzero : f 0 = 0 := by
    simp only [f, Nat.cast_zero, mul_zero, zero_div]
    exact min_eq_right (hfinal_nonneg a)
  have hfk : f k = finalSpend a := by
    unfold f
    rw [show I.budget a * (k : ℝ) / (k : ℝ) = I.budget a by
      field_simp]
    exact min_eq_left (hfinal_feasible a)
  calc
    ∑ i : Fin k, section6BidderSlabSpend k I finalSpend i a =
        ∑ i : Fin k, (f (i.val + 1) - f i.val) := by
          apply Finset.sum_congr rfl
          intro i _
          exact hterm i
    _ = ∑ i ∈ Finset.range k, (f (i + 1) - f i) :=
      Fin.sum_univ_eq_sum_range (fun i => f (i + 1) - f i) k
    _ = f k - f 0 := Finset.sum_range_sub f k
    _ = finalSpend a := by rw [hfk, hfzero, sub_zero]

/-- The aggregate Section 6 split payments equal the total final spend. -/
theorem sum_section6AggregateSlabSpend_eq_total_finalSpend
    {Advertiser Query : Type*} [Fintype Advertiser] {k : ℕ} (hk : 0 < k)
    (I : PaperInstance Advertiser Query) (finalSpend : Advertiser → ℝ)
    (hfinal_nonneg : ∀ a, 0 ≤ finalSpend a)
    (hfinal_feasible : ∀ a, finalSpend a ≤ I.budget a) :
    ∑ i : Fin k, section6AggregateSlabSpend k I finalSpend i =
      ∑ a : Advertiser, finalSpend a := by
  unfold section6AggregateSlabSpend
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  exact sum_section6BidderSlabSpend_eq_finalSpend
    hk I finalSpend hfinal_nonneg hfinal_feasible a

/-- `alpha_i`: OPT revenue from occurrences assigned to bidders of final type `i`. -/
noncomputable def section6OptRevenueByFinalType
    {Advertiser Query : Type*}
    (I : PaperInstance Advertiser Query) (history : List Query)
    (opt : Fin history.length → Option Advertiser)
    (finalType : Advertiser → Fin k) (i : Fin k) : ℝ :=
  ∑ t : Fin history.length,
    match opt t with
    | none => 0
    | some a =>
        if finalType a = i then I.bid a (history.get t) else 0

/-- Section 6's `alpha`, the sum of the `alpha_i` values. -/
noncomputable def section6OptRevenueTotalByType
    {Advertiser Query : Type*} [Fintype (Fin k)]
    (I : PaperInstance Advertiser Query) (history : List Query)
    (opt : Fin history.length → Option Advertiser)
    (finalType : Advertiser → Fin k) : ℝ :=
  ∑ i : Fin k, section6OptRevenueByFinalType I history opt finalType i

/-- The type fibers partition the occurrence-indexed OPT revenue. -/
theorem section6_alpha_total_eq_occurrenceRevenue
    {Advertiser Query : Type*} {k : ℕ}
    (I : PaperInstance Advertiser Query) (history : List Query)
    (opt : Fin history.length → Option Advertiser)
    (finalType : Advertiser → Fin k) :
    section6OptRevenueTotalByType I history opt finalType =
      occurrenceRevenue I history opt := by
  classical
  unfold section6OptRevenueTotalByType section6OptRevenueByFinalType
    occurrenceRevenue occurrenceRevenueAt
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  cases hopt : opt t with
  | none => simp [hopt]
  | some a => simp [hopt]

/-- Each positive-budget slab's lower endpoint is at most its upper endpoint. -/
theorem section6SlabLower_le_upper
    {k : ℕ} (I : PaperInstance Advertiser Query)
    (hbudget : I.PositiveBudgets) (i : Fin k) (a : Advertiser) :
    section6SlabLower k I i a ≤ section6SlabUpper k I i a := by
  unfold section6SlabLower section6SlabUpper
  have hkNat : 0 < k := Nat.zero_lt_of_lt i.isLt
  have hk : 0 < (k : ℝ) := by exact_mod_cast hkNat
  apply (div_le_div_iff_of_pos_right hk).2
  exact mul_le_mul_of_nonneg_left (by norm_num) (hbudget a).le

/-- Split-payment slab spend is nonnegative. -/
theorem section6BidderSlabSpend_nonnegative
    {k : ℕ} (I : PaperInstance Advertiser Query)
    (hbudget : I.PositiveBudgets) (finalSpend : Advertiser → ℝ)
    (i : Fin k) (a : Advertiser) :
    0 ≤ section6BidderSlabSpend k I finalSpend i a := by
  unfold section6BidderSlabSpend
  exact sub_nonneg.mpr
    (min_le_min_left _ (section6SlabLower_le_upper I hbudget i a))

/--
Any bidder contributes at most one slab width to a fixed split-payment slab.
Unlike the source's no-straddling simplification, this is exact even when a
single payment crosses a slab boundary.
-/
theorem section6BidderSlabSpend_le_budget_div
    {Advertiser Query : Type*} {k : ℕ} (hk : 0 < k)
    (I : PaperInstance Advertiser Query) (hbudget : I.PositiveBudgets)
    (finalSpend : Advertiser → ℝ) (i : Fin k) (a : Advertiser) :
    section6BidderSlabSpend k I finalSpend i a ≤ I.budget a / (k : ℝ) := by
  have hlowerUpper := section6SlabLower_le_upper I hbudget i a
  by_cases hfinal : finalSpend a ≤ section6SlabLower k I i a
  · have hupper : finalSpend a ≤ section6SlabUpper k I i a :=
      hfinal.trans hlowerUpper
    unfold section6BidderSlabSpend
    rw [min_eq_left hupper, min_eq_left hfinal]
    simpa using div_nonneg (hbudget a).le (Nat.cast_nonneg k)
  · have hlower : section6SlabLower k I i a ≤ finalSpend a := le_of_not_ge hfinal
    unfold section6BidderSlabSpend
    rw [min_eq_right hlower]
    calc
      min (finalSpend a) (section6SlabUpper k I i a) -
          section6SlabLower k I i a ≤
          section6SlabUpper k I i a - section6SlabLower k I i a :=
        sub_le_sub_right (min_le_right _ _) _
      _ = I.budget a / (k : ℝ) := by
        have hkReal : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
        unfold section6SlabUpper section6SlabLower
        push_cast
        field_simp
        ring

/--
A slab strictly after a bidder's source final type receives no split payment.
Together with the one-slab upper bound, this recovers the paper's idealized
slab accounting without assigning a boundary-crossing payment wholesale to
either adjacent slab.
-/
theorem section6BidderSlabSpend_eq_zero_of_finalType_lt
    {Advertiser Query : Type*} {k : ℕ} (hk : 0 < k)
    (I : PaperInstance Advertiser Query) (hbudget : I.PositiveBudgets)
    (finalSpend : Advertiser → ℝ) (finalType : Advertiser → Fin k)
    (hfinalType : ∀ a,
      IsFinalType k (finalSpend a / I.budget a) (finalType a))
    (i : Fin k) (a : Advertiser) (hbefore : finalType a < i) :
    section6BidderSlabSpend k I finalSpend i a = 0 := by
  have hkReal : 0 < (k : ℝ) := by exact_mod_cast hk
  have hfrac := finalType_fraction_le_upper hk
    (finalSpend a / I.budget a) (finalType a) (hfinalType a)
  have hfinal : finalSpend a ≤
      I.budget a * (((finalType a).val + 1 : ℕ) : ℝ) / (k : ℝ) := by
    have hmul := (div_le_iff₀ (hbudget a)).mp hfrac
    calc
      finalSpend a ≤ (((finalType a).val + 1 : ℕ) : ℝ) / (k : ℝ) * I.budget a := hmul
      _ = I.budget a * (((finalType a).val + 1 : ℕ) : ℝ) / (k : ℝ) := by ring
  have hindex : (finalType a).val + 1 ≤ i.val := by
    exact Nat.succ_le_iff.mpr hbefore
  have hcap :
      I.budget a * (((finalType a).val + 1 : ℕ) : ℝ) / (k : ℝ) ≤
        section6SlabLower k I i a := by
    unfold section6SlabLower
    apply (div_le_div_iff_of_pos_right hkReal).2
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hindex) (hbudget a).le
  have hlower : finalSpend a ≤ section6SlabLower k I i a := hfinal.trans hcap
  have hupper : finalSpend a ≤ section6SlabUpper k I i a :=
    hlower.trans (section6SlabLower_le_upper I hbudget i a)
  unfold section6BidderSlabSpend
  rw [min_eq_left hupper, min_eq_left hlower, sub_self]

/--
The actual split-payment mass in a slab is bounded by the mass of bidders
whose final type has not ended before that slab.  This is the exact bridge
from the runner's payments to the paper's idealized Section 4 slab vector.
-/
theorem section6AggregateSlabSpend_le_finalType_budget_mass
    {Advertiser Query : Type*} [Fintype Advertiser]
    {k : ℕ} (hk : 0 < k)
    (I : PaperInstance Advertiser Query) (hbudget : I.PositiveBudgets)
    (finalSpend : Advertiser → ℝ) (finalType : Advertiser → Fin k)
    (hfinalType : ∀ a,
      IsFinalType k (finalSpend a / I.budget a) (finalType a))
    (i : Fin k) :
    section6AggregateSlabSpend k I finalSpend i ≤
      ∑ a : Advertiser,
        if i ≤ finalType a then I.budget a / (k : ℝ) else 0 := by
  unfold section6AggregateSlabSpend
  apply Finset.sum_le_sum
  intro a _
  by_cases htype : i ≤ finalType a
  · simpa [htype] using
      section6BidderSlabSpend_le_budget_div hk I hbudget finalSpend i a
  · have hbefore : finalType a < i := lt_of_not_ge htype
    rw [section6BidderSlabSpend_eq_zero_of_finalType_lt
      hk I hbudget finalSpend finalType hfinalType i a hbefore]
    simp [htype]

/--
For the paper's Section 2 unit-budget normalization, the actual runner's
split-payment slab spend is at most the idealized Section 4 beta vector
determined by its final types.  Thus no per-query rounding convention enters
the source LP bridge.
-/
theorem theorem8_actual_slabSpend_le_idealBeta
    {Advertiser Query : Type*} [Fintype Advertiser]
    (m : ℕ) (I : PaperInstance Advertiser Query) (hbudget : I.PositiveBudgets)
    (hunit : EqualUnitBudgets I) (finalSpend : Advertiser → ℝ)
    (finalType : Advertiser → Fin (m + 1))
    (hfinalType : ∀ a,
      IsFinalType (m + 1) (finalSpend a / I.budget a) (finalType a))
    (i : Fin m) :
    section6AggregateSlabSpend (m + 1) I finalSpend i.castSucc ≤
      MSVV07SourceLemmas.paperRouteIdealBeta (Fintype.card Advertiser : ℝ)
        (theorem8PreterminalAlphaFromFinalTypes m finalType) i := by
  have hmass := section6AggregateSlabSpend_le_finalType_budget_mass
    (Nat.zero_lt_succ m) I hbudget finalSpend finalType hfinalType i.castSucc
  calc
    section6AggregateSlabSpend (m + 1) I finalSpend i.castSucc ≤
        ∑ a : Advertiser,
          if i.castSucc ≤ finalType a then I.budget a / ((m + 1 : ℕ) : ℝ) else 0 := hmass
    _ = ∑ a : Advertiser,
          if i.castSucc ≤ finalType a then 1 / ((m + 1 : ℕ) : ℝ) else 0 := by
          apply Finset.sum_congr rfl
          intro a _
          rw [hunit a]
    _ = _ := theorem8_finalType_unit_budget_mass_eq_ideal_beta m finalType i

/--
If bidder `a` finishes in a type strictly after slab `i`, final-type semantics
force the whole interval `i` to have been spent.
-/
theorem section6BidderSlabSpend_eq_budget_div_of_lt_finalType
    {k : ℕ} (hk : 0 < k) (I : PaperInstance Advertiser Query)
    (hbudget : I.PositiveBudgets) (finalSpend : Advertiser → ℝ)
    (finalType : Advertiser → Fin k)
    (hfinalType : ∀ a,
      IsFinalType k (finalSpend a / I.budget a) (finalType a))
    (i : Fin k) (a : Advertiser) (hi : i < finalType a) :
    section6BidderSlabSpend k I finalSpend i a =
      I.budget a / (k : ℝ) := by
  have hkReal : 0 < (k : ℝ) := by exact_mod_cast hk
  have htypeLower :
      ((finalType a).val : ℝ) / (k : ℝ) <
        finalSpend a / I.budget a := by
    rcases hfinalType a with hzero | hinterval
    · exact False.elim (by omega)
    · exact hinterval.1
  have hindexNat : i.val + 1 ≤ (finalType a).val := by omega
  have hindexReal :
      ((i.val + 1 : ℕ) : ℝ) ≤ ((finalType a).val : ℝ) := by
    exact_mod_cast hindexNat
  have hindexFrac :
      ((i.val + 1 : ℕ) : ℝ) / (k : ℝ) ≤
        ((finalType a).val : ℝ) / (k : ℝ) :=
    (div_le_div_iff_of_pos_right hkReal).2 hindexReal
  have hupperFrac :
      ((i.val + 1 : ℕ) : ℝ) / (k : ℝ) <
        finalSpend a / I.budget a :=
    hindexFrac.trans_lt htypeLower
  have hupper :
      section6SlabUpper k I i a < finalSpend a := by
    have hmul := (lt_div_iff₀ (hbudget a)).mp hupperFrac
    calc
      section6SlabUpper k I i a =
          ((i.val + 1 : ℕ) : ℝ) / (k : ℝ) * I.budget a := by
            unfold section6SlabUpper
            ring
      _ < finalSpend a := hmul
  have hlower :
      section6SlabLower k I i a ≤ finalSpend a :=
    (section6SlabLower_le_upper I hbudget i a).trans hupper.le
  unfold section6BidderSlabSpend
  rw [min_eq_right hupper.le, min_eq_right hlower]
  unfold section6SlabUpper section6SlabLower
  push_cast
  ring

/-- Regroup one OPT final-type fiber as advertiser-wise occurrence spend. -/
theorem section6OptRevenueByFinalType_eq_sum_occurrenceSpend
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    {k : ℕ} (I : PaperInstance Advertiser Query) (history : List Query)
    (opt : Fin history.length → Option Advertiser)
    (finalType : Advertiser → Fin k) (i : Fin k) :
    section6OptRevenueByFinalType I history opt finalType i =
      ∑ a : Advertiser,
        if finalType a = i then occurrenceSpend I history opt a else 0 := by
  classical
  calc
    section6OptRevenueByFinalType I history opt finalType i =
        ∑ t : Fin history.length, ∑ a : Advertiser,
          if finalType a = i then
            match opt t with
            | none => 0
            | some owner => if owner = a then I.bid a (history.get t) else 0
          else 0 := by
            unfold section6OptRevenueByFinalType
            apply Finset.sum_congr rfl
            intro t _
            cases hopt : opt t with
            | none => simp
            | some owner =>
                by_cases htype : finalType owner = i
                · simp only
                  rw [if_pos htype]
                  symm
                  have hsum := Fintype.sum_eq_single owner
                    (f := fun b : Advertiser =>
                      if finalType b = i then
                        if owner = b then I.bid b (history.get t) else 0
                      else 0)
                    (fun b hne => by
                      have howner : owner ≠ b := Ne.symm hne
                      simp [howner])
                  simpa [htype] using hsum
                · simp only
                  rw [if_neg htype]
                  symm
                  apply Fintype.sum_eq_zero
                  intro b
                  by_cases howner : owner = b
                  · subst b
                    simp [htype]
                  · simp [howner]
    _ = ∑ a : Advertiser, ∑ t : Fin history.length,
          if finalType a = i then
            match opt t with
            | none => 0
            | some owner => if owner = a then I.bid a (history.get t) else 0
          else 0 := Finset.sum_comm
    _ = ∑ a : Advertiser,
          if finalType a = i then occurrenceSpend I history opt a else 0 := by
            apply Finset.sum_congr rfl
            intro a _
            by_cases htype : finalType a = i
            · simp only [if_pos htype, occurrenceSpend]
            · simp [htype]

/-- The OPT revenue after type `i` is exactly the spend of later-type owners. -/
theorem section6OptRevenueTail_eq_sum_later_spend
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    {k : ℕ} (I : PaperInstance Advertiser Query) (history : List Query)
    (opt : Fin history.length → Option Advertiser)
    (finalType : Advertiser → Fin k) (i : Fin k) :
    section6OptRevenueTotalByType I history opt finalType -
        ∑ j ∈ Finset.Iic i,
          section6OptRevenueByFinalType I history opt finalType j =
      ∑ a : Advertiser,
        if i < finalType a then occurrenceSpend I history opt a else 0 := by
  classical
  unfold section6OptRevenueTotalByType
  rw [show
    (∑ j : Fin k,
        section6OptRevenueByFinalType I history opt finalType j) -
          ∑ j ∈ Finset.Iic i,
            section6OptRevenueByFinalType I history opt finalType j =
        ∑ j ∈ Finset.Ioi i,
          section6OptRevenueByFinalType I history opt finalType j by
      exact (by
        have hdiff := Finset.sum_sdiff
          (s₁ := (Finset.Iic i))
          (s₂ := (Finset.univ : Finset (Fin k)))
          (f := section6OptRevenueByFinalType I history opt finalType)
          (by simp)
        rw [← hdiff, add_sub_cancel_right]
        apply Finset.sum_congr
        · ext j
          simp
        · intro j hj
          rfl)]
  simp_rw [section6OptRevenueByFinalType_eq_sum_occurrenceSpend]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : i < finalType a
  · simp [ha]
  · simp [ha]

/-- Actual advertiser-wise OPT feasibility bounds every later-type OPT tail. -/
theorem section6OptRevenueTail_le_later_budgets
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    {k : ℕ} (I : PaperInstance Advertiser Query) (history : List Query)
    (opt : Fin history.length → Option Advertiser)
    (finalType : Advertiser → Fin k)
    (hoptFeasible : ∀ a,
      occurrenceSpend I history opt a ≤ I.budget a)
    (i : Fin k) :
    section6OptRevenueTotalByType I history opt finalType -
        ∑ j ∈ Finset.Iic i,
          section6OptRevenueByFinalType I history opt finalType j ≤
      ∑ a ∈ (Finset.univ : Finset Advertiser).filter
        (fun a => i < finalType a), I.budget a := by
  rw [section6OptRevenueTail_eq_sum_later_spend]
  rw [Finset.sum_filter]
  exact Finset.sum_le_sum fun a _ => by
    by_cases ha : i < finalType a
    · simpa [ha] using hoptFeasible a
    · simp [ha]

/--
The generalized Section 6 beta inequality derived from the paper's primitive
objects: an occurrence-indexed feasible OPT assignment and final types of the
online run.  No tail-budget or full-earlier-slab fact remains as an input.
-/
theorem section6_beta_lower_bound_from_opt_feasibility_and_final_types
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    {k : ℕ} (hk : 0 < k) (I : PaperInstance Advertiser Query)
    (history : List Query)
    (opt : Fin history.length → Option Advertiser)
    (finalSpend : Advertiser → ℝ)
    (finalType : Advertiser → Fin k)
    (hbudget : I.PositiveBudgets)
    (hoptFeasible : ∀ a,
      occurrenceSpend I history opt a ≤ I.budget a)
    (hfinalType : ∀ a,
      IsFinalType k (finalSpend a / I.budget a) (finalType a)) :
    ∀ i : Fin k,
      (section6OptRevenueTotalByType I history opt finalType -
          ∑ j ∈ Finset.Iic i,
            section6OptRevenueByFinalType I history opt finalType j) /
          (k : ℝ) ≤
        section6AggregateSlabSpend k I finalSpend i := by
  intro i
  have hkReal : 0 < (k : ℝ) := by exact_mod_cast hk
  have htail :=
    section6OptRevenueTail_le_later_budgets
      I history opt finalType hoptFeasible i
  have htailDiv :
      (section6OptRevenueTotalByType I history opt finalType -
          ∑ j ∈ Finset.Iic i,
            section6OptRevenueByFinalType I history opt finalType j) /
          (k : ℝ) ≤
        (∑ a ∈ (Finset.univ : Finset Advertiser).filter
          (fun a => i < finalType a), I.budget a) / (k : ℝ) :=
    (div_le_div_iff_of_pos_right hkReal).2 htail
  calc
    (section6OptRevenueTotalByType I history opt finalType -
          ∑ j ∈ Finset.Iic i,
            section6OptRevenueByFinalType I history opt finalType j) /
          (k : ℝ) ≤
        (∑ a ∈ (Finset.univ : Finset Advertiser).filter
          (fun a => i < finalType a), I.budget a) / (k : ℝ) := htailDiv
    _ = ∑ a : Advertiser,
        if i < finalType a then I.budget a / (k : ℝ) else 0 := by
          rw [Finset.sum_div]
          simp only [Finset.sum_filter]
    _ ≤ ∑ a : Advertiser,
        section6BidderSlabSpend k I finalSpend i a := by
          exact Finset.sum_le_sum fun a _ => by
            by_cases ha : i < finalType a
            · simpa [ha] using
                (section6BidderSlabSpend_eq_budget_div_of_lt_finalType
                  hk I hbudget finalSpend finalType hfinalType i a ha).ge
            · simpa [ha] using
                section6BidderSlabSpend_nonnegative
                  I hbudget finalSpend i a
    _ = section6AggregateSlabSpend k I finalSpend i := rfl

/--
The Section 6 beta lower bounds hold for a final-type classifier derived from
the actual finite Theorem 8 execution and any feasible occurrence-indexed OPT.
-/
theorem theorem8_run_section6_beta_lower_bound
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (k : ℕ) (hk : 0 < k) (I : PaperInstance Advertiser Query)
    (history : List Query) (opt : Fin history.length → Option Advertiser)
    (hbid : I.NonnegativeBids) (hbudget : I.PositiveBudgets)
    (hoptFeasible : ∀ a, occurrenceSpend I history opt a ≤ I.budget a) :
    ∃ finalType : Advertiser → Fin k, ∀ i : Fin k,
      (section6OptRevenueTotalByType I history opt finalType -
          ∑ j ∈ Finset.Iic i,
            section6OptRevenueByFinalType I history opt finalType j) /
          (k : ℝ) ≤
        section6AggregateSlabSpend k I
          (runTheorem8DiscreteOccurrences k hk I history).spent i := by
  obtain ⟨finalType, hfinalType⟩ :=
    runTheorem8DiscreteOccurrences_has_final_types
      k hk I history hbid hbudget
  refine ⟨finalType, ?_⟩
  exact section6_beta_lower_bound_from_opt_feasibility_and_final_types
    hk I history opt (runTheorem8DiscreteOccurrences k hk I history).spent
    finalType hbudget hoptFeasible hfinalType

/--
For the finite Theorem 8 runner, the entire Section 6 split-payment vector
adds up to the runner's realized revenue.  Thus the beta accounting is an
exact decomposition of the algorithm side, including arrivals that cross slab
boundaries.
-/
theorem theorem8_run_total_slab_spend_eq_revenue
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (k : ℕ) (hk : 0 < k) (I : PaperInstance Advertiser Query)
    (history : List Query) (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets) :
    ∑ i : Fin k, section6AggregateSlabSpend k I
      (runTheorem8DiscreteOccurrences k hk I history).spent i =
      (runTheorem8DiscreteOccurrences k hk I history).revenue := by
  have hnonneg := runTheorem8DiscreteOccurrences_nonnegative_spend
    k hk I history hbid
  have hfeasible := runTheorem8DiscreteOccurrences_budget_feasible
    k hk I history (fun a => (hbudget a).le)
  calc
    ∑ i : Fin k, section6AggregateSlabSpend k I
        (runTheorem8DiscreteOccurrences k hk I history).spent i =
        ∑ a : Advertiser, (runTheorem8DiscreteOccurrences k hk I history).spent a :=
      sum_section6AggregateSlabSpend_eq_total_finalSpend
        hk I _ hnonneg hfeasible
    _ = (runTheorem8DiscreteOccurrences k hk I history).revenue :=
      runTheorem8DiscreteOccurrences_totalSpend_eq_revenue k hk I history

/-- The runner's split-payment potential is exactly the Section 6 weighted beta sum. -/
theorem theorem8StateSlabPotential_eq_section6_weighted_spend
    {Advertiser Query : Type*} [Fintype Advertiser]
    (k : ℕ) (I : PaperInstance Advertiser Query) (psi : Fin k → ℝ)
    (S : OccurrenceState Advertiser Query) :
    theorem8StateSlabPotential k I psi S =
      ∑ i : Fin k, psi i * section6AggregateSlabSpend k I S.spent i := by
  unfold theorem8StateSlabPotential theorem8SlabPotential
    section6AggregateSlabSpend section6BidderSlabSpend
    section6SlabLower section6SlabUpper theorem8SlabSpent
    theorem8SlabLower theorem8SlabUpper
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]

/-- Feasibility of the actual finite runner bounds its realized revenue by total budget. -/
theorem runTheorem8DiscreteOccurrences_revenue_le_total_budget
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (k : ℕ) (hk : 0 < k) (I : PaperInstance Advertiser Query)
    (history : List Query) (hbudget : I.PositiveBudgets) :
    (runTheorem8DiscreteOccurrences k hk I history).revenue ≤
      ∑ a : Advertiser, I.budget a := by
  rw [← runTheorem8DiscreteOccurrences_totalSpend_eq_revenue k hk I history]
  unfold occurrenceStateTotalSpend
  exact Finset.sum_le_sum fun a _ =>
    runTheorem8DiscreteOccurrences_budget_feasible k hk I history
      (fun a => (hbudget a).le) a

/--
The actual Theorem 8 runner's weighted online payments are bounded by the
Section 6 split-payment beta sum plus one total-budget slab.
-/
theorem theorem8_sum_weighted_revenue_le_section6_weighted_spend
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (k : ℕ) (hk : 0 < k) (I : PaperInstance Advertiser Query)
    (history : List Query) (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (hsmall : ∀ a q, I.bid a q ≤ I.budget a / (k : ℝ)) :
    (∑ t : Fin history.length,
      theorem8AlgWeightedRevenueAt k hk I history t) ≤
      (∑ i : Fin k, theorem8DiscreteTradeoff k i *
        section6AggregateSlabSpend k I
          (runTheorem8DiscreteOccurrences k hk I history).spent i) +
        (∑ a : Advertiser, I.budget a) / (k : ℝ) := by
  have halg := theorem8_sum_weighted_revenue_le_potential
    k hk I history hbid hbudget hsmall
  have hbudgetTotal := runTheorem8DiscreteOccurrences_revenue_le_total_budget
    k hk I history hbudget
  calc
    (∑ t : Fin history.length,
        theorem8AlgWeightedRevenueAt k hk I history t) ≤
        theorem8StateSlabPotential k I (theorem8DiscreteTradeoff k)
          (runTheorem8DiscreteOccurrences k hk I history) +
          (runTheorem8DiscreteOccurrences k hk I history).revenue / (k : ℝ) := halg
    _ = (∑ i : Fin k, theorem8DiscreteTradeoff k i *
          section6AggregateSlabSpend k I
            (runTheorem8DiscreteOccurrences k hk I history).spent i) +
          (runTheorem8DiscreteOccurrences k hk I history).revenue / (k : ℝ) := by
          rw [theorem8StateSlabPotential_eq_section6_weighted_spend]
    _ ≤ (∑ i : Fin k, theorem8DiscreteTradeoff k i *
          section6AggregateSlabSpend k I
            (runTheorem8DiscreteOccurrences k hk I history).spent i) +
          (∑ a : Advertiser, I.budget a) / (k : ℝ) := by
          apply add_le_add_right
          exact div_le_div_of_nonneg_right hbudgetTotal
            (by exact_mod_cast (Nat.zero_le k))

/--
Combining actual-run Lemma 6 with split-payment accounting yields the finite
Theorem 8 weighted relation.  One total-budget slab covers source final-type
endpoints and one covers payments crossing their active slab boundary.
-/
theorem theorem8_weighted_opt_le_section6_weighted_spend_with_error
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (k : ℕ) (hk : 0 < k) (I : PaperInstance Advertiser Query)
    (history : List Query) (opt : Fin history.length → Option Advertiser)
    (hbid : I.NonnegativeBids) (hbudget : I.PositiveBudgets)
    (hsmall : ∀ a q, I.bid a q ≤ I.budget a / (k : ℝ))
    (finalType : Advertiser → Fin k)
    (hfinalType : ∀ a, IsFinalType k
      ((runTheorem8DiscreteOccurrences k hk I history).spent a / I.budget a)
      (finalType a))
    (hoptFeasible : ∀ a, occurrenceSpend I history opt a ≤ I.budget a) :
    (∑ t : Fin history.length,
      theorem8OptWeightedRevenueAt k I history opt finalType t) ≤
      (∑ i : Fin k, theorem8DiscreteTradeoff k i *
        section6AggregateSlabSpend k I
          (runTheorem8DiscreteOccurrences k hk I history).spent i) +
        2 * ((∑ a : Advertiser, I.budget a) / (k : ℝ)) := by
  have hlemma6 := theorem8_sum_tradeoff_with_endpoint_error
    k hk I history opt hbid hbudget hsmall finalType hfinalType hoptFeasible
  have halg := theorem8_sum_weighted_revenue_le_section6_weighted_spend
    k hk I history hbid hbudget hsmall
  linarith

/--
Finite Theorem 8 source accounting under the paper's temporary unit-budget,
exhausting-OPT normalization.  The actual runner's weighted type count is at
most the idealized Section 4 beta vector plus two aggregate slab widths: one
for right endpoints and one for boundary-crossing payments.
-/
theorem theorem8_weighted_preterminal_alpha_le_idealBeta_with_error
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (m : ℕ) (I : PaperInstance Advertiser Query) (history : List Query)
    (opt : Fin history.length → Option Advertiser)
    (hbid : I.NonnegativeBids) (hbudget : I.PositiveBudgets)
    (hunit : EqualUnitBudgets I)
    (hsmall : ∀ a q, I.bid a q ≤ I.budget a / ((m + 1 : ℕ) : ℝ))
    (finalType : Advertiser → Fin (m + 1))
    (hfinalType : ∀ a, IsFinalType (m + 1)
      ((runTheorem8DiscreteOccurrences (m + 1) (Nat.zero_lt_succ m) I history).spent a /
        I.budget a) (finalType a))
    (hoptFeasible : ∀ a, occurrenceSpend I history opt a ≤ I.budget a)
    (hexhaust : ∀ a, occurrenceSpend I history opt a = 1) :
    (∑ i : Fin m, MSVV07SourceLemmas.paperRoutePsiCandidate i *
      theorem8PreterminalAlphaFromFinalTypes m finalType i) ≤
      (∑ i : Fin m, MSVV07SourceLemmas.paperRoutePsiCandidate i *
        MSVV07SourceLemmas.paperRouteIdealBeta (Fintype.card Advertiser : ℝ)
          (theorem8PreterminalAlphaFromFinalTypes m finalType) i) +
        2 * ((Fintype.card Advertiser : ℝ) / ((m + 1 : ℕ) : ℝ)) := by
  let finalSpend := (runTheorem8DiscreteOccurrences (m + 1) (Nat.zero_lt_succ m)
    I history).spent
  have hpsi_nonneg : ∀ i : Fin m, 0 ≤ MSVV07SourceLemmas.paperRoutePsiCandidate i := by
    intro i
    unfold MSVV07SourceLemmas.paperRoutePsiCandidate
      MSVV07SourceLemmas.paperRoutePsiFromDual
    apply Finset.sum_nonneg
    intro j _
    exact MSVV07SourceLemmas.paperRouteDualCandidate_nonnegative j
  have hactual :
      (∑ i : Fin (m + 1), theorem8DiscreteTradeoff (m + 1) i *
        section6AggregateSlabSpend (m + 1) I finalSpend i) ≤
        ∑ i : Fin m, MSVV07SourceLemmas.paperRoutePsiCandidate i *
          MSVV07SourceLemmas.paperRouteIdealBeta (Fintype.card Advertiser : ℝ)
            (theorem8PreterminalAlphaFromFinalTypes m finalType) i := by
    rw [Fin.sum_univ_castSucc]
    have hterminal : theorem8DiscreteTradeoff (m + 1) (Fin.last m) = 0 := by
      apply theorem8DiscreteTradeoff_terminal
      simp
    rw [hterminal]
    simp only [zero_mul, add_zero]
    apply Finset.sum_le_sum
    intro i _
    rw [theorem8DiscreteTradeoff_castSucc_eq_paperRoutePsiCandidate]
    exact mul_le_mul_of_nonneg_left
      (theorem8_actual_slabSpend_le_idealBeta m I hbudget hunit finalSpend
        finalType hfinalType i)
      (hpsi_nonneg i)
  have hrun := theorem8_weighted_opt_le_section6_weighted_spend_with_error
    (m + 1) (Nat.zero_lt_succ m) I history opt hbid hbudget hsmall finalType hfinalType
    hoptFeasible
  have hopt := theorem8_sum_optWeightedRevenue_eq_preterminal_alpha
    m I history opt finalType hexhaust
  have htotal : (∑ a : Advertiser, I.budget a) = (Fintype.card Advertiser : ℝ) := by
    calc
      (∑ a : Advertiser, I.budget a) = ∑ _a : Advertiser, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro a _
        exact hunit a
      _ = _ := by simp
  dsimp [finalSpend] at hactual
  rw [hopt] at hrun
  rw [htotal] at hrun
  exact hrun.trans (by
    simpa [add_comm] using
      add_le_add_left hactual (2 * ((Fintype.card Advertiser : ℝ) / ((m + 1 : ℕ) : ℝ))))

/--
The actual finite runner supplies a feasible point for the paper's
tradeoff-revealing LP.  The LP value is at most the exact finite
factor-revealing value plus the two runner-derived aggregate slab errors.
-/
theorem theorem8_preterminal_alpha_le_factor_value_with_error
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (m : ℕ) (I : PaperInstance Advertiser Query) (history : List Query)
    (opt : Fin history.length → Option Advertiser)
    (hbid : I.NonnegativeBids) (hbudget : I.PositiveBudgets)
    (hunit : EqualUnitBudgets I)
    (hsmall : ∀ a q, I.bid a q ≤ I.budget a / ((m + 1 : ℕ) : ℝ))
    (finalType : Advertiser → Fin (m + 1))
    (hfinalType : ∀ a, IsFinalType (m + 1)
      ((runTheorem8DiscreteOccurrences (m + 1) (Nat.zero_lt_succ m) I history).spent a /
        I.budget a) (finalType a))
    (hoptFeasible : ∀ a, occurrenceSpend I history opt a ≤ I.budget a)
    (hexhaust : ∀ a, occurrenceSpend I history opt a = 1) :
    MSVV07SourceLemmas.paperRoutePrimalObjective
      (theorem8PreterminalAlphaFromFinalTypes m finalType) ≤
      MSVV07SourceLemmas.factorRevealingLPValue m (Fintype.card Advertiser : ℝ) +
        2 * ((Fintype.card Advertiser : ℝ) / ((m + 1 : ℕ) : ℝ)) := by
  let alpha := theorem8PreterminalAlphaFromFinalTypes m finalType
  let beta := MSVV07SourceLemmas.paperRouteIdealBeta
    (Fintype.card Advertiser : ℝ) alpha
  let l := MSVV07SourceLemmas.paperRouteLPRow alpha
  have halpha : ∀ i : Fin m, 0 ≤ alpha i := by
    intro i
    unfold alpha theorem8PreterminalAlphaFromFinalTypes
    apply Finset.sum_nonneg
    intro a _
    split_ifs <;> norm_num
  have hl : ∀ i : Fin m,
      l i = MSVV07SourceLemmas.paperRouteRhs (Fintype.card Advertiser : ℝ) i +
        MSVV07SourceLemmas.paperRouteDelta alpha beta i := by
    intro i
    unfold l beta
    apply MSVV07SourceLemmas.lemma5_tradeoff_rhs_eq_base_add_delta
    exact MSVV07SourceLemmas.paperRouteIdealBeta_prefix
      (Fintype.card Advertiser : ℝ) alpha i
  have hfeasible :
      (MSVV07SourceLemmas.tradeoffRevealingLP
        MSVV07SourceLemmas.paperRoutePrimalObjectiveCoeff l).PrimalFeasible alpha := by
    constructor
    · exact halpha
    · intro i
      change (∑ j : Fin m, MSVV07SourceLemmas.paperRouteMatrixCoeff i j * alpha j) ≤ l i
      rw [MSVV07SourceLemmas.paperRouteMatrixCoeff_row_eq_lpRow]
  have hweighted := theorem8_weighted_preterminal_alpha_le_idealBeta_with_error
    m I history opt hbid hbudget hunit hsmall finalType hfinalType hoptFeasible hexhaust
  have hperturb :
      (∑ i : Fin m, MSVV07SourceLemmas.paperRoutePsiCandidate i *
        (alpha i - beta i)) ≤
        2 * ((Fintype.card Advertiser : ℝ) / ((m + 1 : ℕ) : ℝ)) := by
    change (∑ i : Fin m, MSVV07SourceLemmas.paperRoutePsiCandidate i *
        (alpha i - beta i)) ≤ _
    rw [show (∑ i : Fin m, MSVV07SourceLemmas.paperRoutePsiCandidate i *
        (alpha i - beta i)) =
        (∑ i : Fin m, MSVV07SourceLemmas.paperRoutePsiCandidate i * alpha i) -
          ∑ i : Fin m, MSVV07SourceLemmas.paperRoutePsiCandidate i * beta i by
      simp [mul_sub, Finset.sum_sub_distrib]]
    exact sub_le_iff_le_add.mpr (by simpa [alpha, beta, add_comm] using hweighted)
  have hbound := MSVV07SourceLemmas.theorem8_source_route_tradeoff_lp_upper_bound_with_error
    (Fintype.card Advertiser : ℝ) alpha beta l
      (2 * ((Fintype.card Advertiser : ℝ) / ((m + 1 : ℕ) : ℝ)))
      hl hperturb hfeasible
  simpa [MSVV07SourceLemmas.tradeoffRevealingLP,
    Optimization.StandardMaxLP.primalObjective, alpha] using hbound

/--
Finite source-faithful Theorem 8 guarantee under the paper's temporary
unit-budget and exhausting-OPT normalization.  All finite discrepancies are
visible: two slab widths from weighted query accounting and one from the
terminal unspent-budget conversion.
-/
theorem theorem8_unit_budget_finite_competitive_with_error
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (m : ℕ) (I : PaperInstance Advertiser Query) (history : List Query)
    (opt : Fin history.length → Option Advertiser)
    (hbid : I.NonnegativeBids) (hbudget : I.PositiveBudgets)
    (hunit : EqualUnitBudgets I)
    (hsmall : ∀ a q, I.bid a q ≤ I.budget a / ((m + 1 : ℕ) : ℝ))
    (hoptFeasible : ∀ a, occurrenceSpend I history opt a ≤ I.budget a)
    (hexhaust : ∀ a, occurrenceSpend I history opt a = 1) :
    paperMsvvRatio * (Fintype.card Advertiser : ℝ) ≤
      (runTheorem8DiscreteOccurrences (m + 1) (Nat.zero_lt_succ m) I history).revenue +
        3 * ((Fintype.card Advertiser : ℝ) / ((m + 1 : ℕ) : ℝ)) := by
  obtain ⟨finalType, hfinalType⟩ :=
    runTheorem8DiscreteOccurrences_has_final_types
      (m + 1) (Nat.zero_lt_succ m) I history hbid hbudget
  have hobj := theorem8_preterminal_alpha_le_factor_value_with_error
    m I history opt hbid hbudget hunit hsmall finalType hfinalType hoptFeasible hexhaust
  have hunspent := theorem8_unspent_le_preterminal_objective_with_error
    m I history hunit finalType hfinalType
  have hN : 0 ≤ (Fintype.card Advertiser : ℝ) := by positivity
  have hfactor := MSVV07SourceLemmas.factorRevealingLPValue_le_N_div_exp_one
    m (Fintype.card Advertiser : ℝ) hN
  unfold paperMsvvRatio
  rw [show (1 - 1 / Real.exp 1) * (Fintype.card Advertiser : ℝ) =
    (Fintype.card Advertiser : ℝ) -
      (Fintype.card Advertiser : ℝ) / Real.exp 1 by ring]
  linarith

/--
The same finite source Theorem 8 inequality expressed against the actual
occurrence-indexed offline optimum.  The benchmark equality uses exactly the
temporary unit-budget and exhaustive-optimum normalization stated by the
paper before its Section 6 extensions.
-/
theorem theorem8_unit_budget_finite_competitive_with_error_against_offline_optimum
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (m : ℕ) (I : PaperInstance Advertiser Query) (history : List Query)
    (opt : Fin history.length → Option Advertiser)
    (hbid : I.NonnegativeBids) (hbudget : I.PositiveBudgets)
    (hunit : EqualUnitBudgets I)
    (hsmall : ∀ a q, I.bid a q ≤ I.budget a / ((m + 1 : ℕ) : ℝ))
    (hoptFeasible : occurrenceAssignmentFeasible I history opt)
    (hexhaust : ∀ a, occurrenceSpend I history opt a = 1) :
    paperMsvvRatio *
        (occurrenceIndexedInstance I history).offlineOptimumValue
          (fun a => (hbudget a).le) ≤
      (runTheorem8DiscreteOccurrences (m + 1) (Nat.zero_lt_succ m) I history).revenue +
        3 * ((Fintype.card Advertiser : ℝ) / ((m + 1 : ℕ) : ℝ)) := by
  rw [occurrenceIndexed_offlineOptimumValue_eq_card_of_unit_exhaustive
    I history opt hbudget hunit hoptFeasible.2 hexhaust]
  exact theorem8_unit_budget_finite_competitive_with_error
    m I history opt hbid hbudget hunit hsmall hoptFeasible.2 hexhaust

/-- A fixed nonnegative aggregate constant divided by the number of slabs
eventually falls below every positive tolerance. -/
theorem constant_div_nat_succ_eventually_lt
    (C delta : ℝ) (hC : 0 ≤ C) (hdelta : 0 < delta) :
    ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
      C / ((m + 1 : ℕ) : ℝ) < delta := by
  by_cases hCzero : C = 0
  · refine ⟨0, ?_⟩
    intro m hm
    simp [hCzero, hdelta]
  have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hCzero)
  obtain ⟨M, hM⟩ := exists_nat_one_div_lt (div_pos hdelta hCpos)
  refine ⟨M, ?_⟩
  intro m hm
  have hM' : 1 / ((M + 1 : ℕ) : ℝ) < delta / C := by
    simpa [Nat.cast_add] using hM
  have hcast : ((M + 1 : ℕ) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ hm
  have hMpos : 0 < ((M + 1 : ℕ) : ℝ) := by positivity
  have hinv : 1 / ((m + 1 : ℕ) : ℝ) ≤ 1 / ((M + 1 : ℕ) : ℝ) :=
    one_div_le_one_div_of_le hMpos hcast
  have hscaled : C * (1 / ((m + 1 : ℕ) : ℝ)) < C * (delta / C) :=
    (mul_le_mul_of_nonneg_left hinv hC).trans_lt
      (mul_lt_mul_of_pos_left hM' hCpos)
  have hcancel : C * (delta / C) = delta := by
    field_simp
  rw [hcancel] at hscaled
  simpa [div_eq_mul_inv] using hscaled

/--
The source Theorem 8 limit under the temporary Sections 2--5 normalization.
For a family whose bids are at most one `(m + 1)`-st of every unit budget, the
finite accounting error is uniformly `3 |Advertiser| / (m + 1)` and therefore
vanishes without any query-count-dependent convergence premise.
-/
theorem theorem8_unit_budget_competitive_of_small_bids_limit
    {Advertiser : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (n : ℕ → ℕ)
    (I : (m : ℕ) → PaperInstance Advertiser (Fin (n m)))
    (opt : (m : ℕ) → Fin (List.finRange (n m)).length → Option Advertiser)
    (hbid : ∀ m, (I m).NonnegativeBids)
    (hbudget : ∀ m, (I m).PositiveBudgets)
    (hunit : ∀ m, EqualUnitBudgets (I m))
    (hsmall : ∀ m a q,
      (I m).bid a q ≤ (I m).budget a / ((m + 1 : ℕ) : ℝ))
    (hoptFeasible : ∀ m,
      occurrenceAssignmentFeasible (I m) (List.finRange (n m)) (opt m))
    (hexhaust : ∀ m a,
      occurrenceSpend (I m) (List.finRange (n m)) (opt m) a = 1) :
    ∀ delta : ℝ, 0 < delta →
      ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
        paperMsvvRatio *
            (occurrenceIndexedInstance (I m) (List.finRange (n m))).offlineOptimumValue
              (fun a => (hbudget m a).le) ≤
          (runTheorem8DiscreteOccurrences
            (m + 1) (Nat.zero_lt_succ m) (I m) (List.finRange (n m))).revenue + delta := by
  intro delta hdelta
  obtain ⟨M, hM⟩ := constant_div_nat_succ_eventually_lt
    (3 * (Fintype.card Advertiser : ℝ)) delta (by positivity) hdelta
  refine ⟨M, ?_⟩
  intro m hm
  have hfinite := theorem8_unit_budget_finite_competitive_with_error_against_offline_optimum
    m (I m) (List.finRange (n m)) (opt m) (hbid m) (hbudget m) (hunit m)
    (hsmall m) (hoptFeasible m) (hexhaust m)
  have herror := hM m hm
  have herror' :
      3 * ((Fintype.card Advertiser : ℝ) / ((m + 1 : ℕ) : ℝ)) < delta := by
    calc
      3 * ((Fintype.card Advertiser : ℝ) / ((m + 1 : ℕ) : ℝ)) =
          3 * (Fintype.card Advertiser : ℝ) / ((m + 1 : ℕ) : ℝ) := by ring
      _ < delta := herror
  calc
    paperMsvvRatio *
        (occurrenceIndexedInstance (I m) (List.finRange (n m))).offlineOptimumValue
          (fun a => (hbudget m a).le) ≤
        (runTheorem8DiscreteOccurrences
          (m + 1) (Nat.zero_lt_succ m) (I m) (List.finRange (n m))).revenue +
          3 * ((Fintype.card Advertiser : ℝ) / ((m + 1 : ℕ) : ℝ)) := hfinite
    _ ≤ (runTheorem8DiscreteOccurrences
          (m + 1) (Nat.zero_lt_succ m) (I m) (List.finRange (n m))).revenue + delta := by
          linarith

/--
The Section 6 weighted relation follows from the same query-fiber accounting
used in Lemma 7 when the final-slab error is zero.
-/
theorem section6_weighted_alpha_beta_of_query_accounting
    {m Query : Type*} [Fintype m] [Fintype Query]
    (psi alpha beta : m → ℝ) (opt alg : Query → ℝ)
    (queryType querySlab : Query → m)
    (htradeoff_sum :
      (∑ q : Query,
        (opt q * psi (queryType q) - alg q * psi (querySlab q))) ≤ 0)
    (hopt_accounting :
      (∑ q : Query, opt q * psi (queryType q)) =
        ∑ i : m, psi i * alpha i)
    (halg_accounting :
      (∑ q : Query, alg q * psi (querySlab q)) ≤
        ∑ i : m, psi i * beta i) :
    (∑ i : m, psi i * alpha i) ≤
      ∑ i : m, psi i * beta i := by
  have h := MSVV07SourceLemmas.lemma7_weighted_perturbation_bound
    psi alpha beta opt alg queryType querySlab 0
    htradeoff_sum hopt_accounting (by simpa using halg_accounting)
  simpa [mul_sub, Finset.sum_sub_distrib] using h

/--
Under the equal-unit-budget normalization used before Section 6's
heterogeneous-budget extension, the paper's original small-bids condition also
bounds the all-bidders next-price charge by the winner's budget fraction.
-/
theorem section6_next_highest_bid_all_small_bids_of_equal_unit_budgets
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query) {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (hunit : EqualUnitBudgets I)
    (hsmall : paperSmallBids I epsilon) :
    ∀ a q,
      Proof.section6_next_highest_bid_all I a q ≤ epsilon * I.budget a := by
  classical
  intro a q
  unfold Proof.section6_next_highest_bid_all
  let others : Finset Advertiser := (Finset.univ : Finset Advertiser).erase a
  by_cases h : others.Nonempty
  · have hsup :
        others.sup' h (fun b => I.bid b q) ≤ epsilon := by
      apply Finset.sup'_le h
      intro b hb
      simpa [hunit b] using hsmall b q
    simpa [others, h, hunit a] using max_le hepsilon hsup
  · simp [others, h, hunit a, hepsilon]

/--
The same equal-unit-budget argument applies after filtering the competing bids
to the bidders that are alive at the current query.
-/
theorem section6_next_highest_bid_alive_small_bids_of_equal_unit_budgets
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (alive : Advertiser → Query → Prop) [∀ a q, Decidable (alive a q)]
    {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (hunit : EqualUnitBudgets I)
    (hsmall : paperSmallBids I epsilon) :
    ∀ a q,
      Proof.section6_next_highest_bid_alive I alive a q ≤
        epsilon * I.budget a := by
  classical
  intro a q
  unfold Proof.section6_next_highest_bid_alive
  let others : Finset Advertiser :=
    ((Finset.univ : Finset Advertiser).erase a).filter fun b => alive b q
  by_cases h : others.Nonempty
  · have hsup :
        others.sup' h (fun b => I.bid b q) ≤ epsilon := by
      apply Finset.sup'_le h
      intro b hb
      simpa [hunit b] using hsmall b q
    simpa [others, h, hunit a] using max_le hepsilon hsup
  · simp [others, h, hunit a, hepsilon]

/-- The all-alive specialization makes the alive next-price charge equal the all-bidder charge. -/
theorem section6_all_alive_next_price_reduces_to_all_bidders
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query) (a : Advertiser) (q : Query) :
    Proof.section6_next_highest_bid_alive I (fun _ _ => True) a q =
      Proof.section6_next_highest_bid_all I a q := by
  classical
  unfold Proof.section6_next_highest_bid_alive Proof.section6_next_highest_bid_all
  simp

/-! ## Section 8: proposals as definitions, not proved guarantees -/

/-- A finite switching-distribution day: each time belongs to a regime with a fixed query PMF. -/
structure SwitchingQueryDistribution (Time Regime Query : Type*) where
  regimeAt : Time → Regime
  queryDistribution : Regime → PMF Query

/--
The fixed query distribution in force at a particular time.  Switching the
regime changes this PMF; within a regime the PMF is unchanged.
-/
noncomputable def SwitchingQueryDistribution.queryDistributionAt
    {Time Regime Query : Type*}
    (M : SwitchingQueryDistribution Time Regime Query) (time : Time) :
    PMF Query :=
  M.queryDistribution (M.regimeAt time)

/-- Paper proposal: run Balance after multiplying each advertiser's bids by its weight. -/
noncomputable def runWeightedBidProposal
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query) (weight : Advertiser → ℝ)
    (history : List Query) : OccurrenceState Advertiser Query :=
  runBalanceOccurrences (I.withAdvertiserWeights weight) history

/-- One window of the Section 8 up/down weight-adjustment heuristic. -/
noncomputable def updateWeightAfterWindow
    (step : ℝ) (weight spent fairShare : ℝ) : ℝ :=
  if spent < fairShare then weight + step
  else if fairShare < spent then max 0 (weight - step)
  else weight

/--
Repeat the Section 8 weight-adjustment heuristic after each time window.  Each
pair records the bidder's spend and fair-share target in the next window.
-/
noncomputable def updateWeightAfterWindows (step : ℝ) :
    ℝ → List (ℝ × ℝ) → ℝ
  | weight, [] => weight
  | weight, (spent, fairShare) :: windows =>
      updateWeightAfterWindows step
        (updateWeightAfterWindow step weight spent fairShare) windows

/--
The source-faithful one-window heuristic relation: underspending raises the
weight, overspending lowers it, and exact fair-share spending leaves it fixed.
The paper does not specify a step size or a zero clamp.
-/
def IsWeightAdjustment
    (weight spent fairShare nextWeight : ℝ) : Prop :=
  (spent < fairShare ∧ weight < nextWeight) ∨
    (fairShare < spent ∧ nextWeight < weight) ∨
    (spent = fairShare ∧ nextWeight = weight)

/-- Repeat the source's direction-only adjustment relation after every window. -/
def IsRepeatedWeightAdjustment : ℝ → List (ℝ × ℝ) → ℝ → Prop
  | weight, [], finalWeight => finalWeight = weight
  | weight, (spent, fairShare) :: windows, finalWeight =>
      ∃ nextWeight,
        IsWeightAdjustment weight spent fairShare nextWeight ∧
          IsRepeatedWeightAdjustment nextWeight windows finalWeight

/-- Every finite window history admits at least one source-faithful adjustment path. -/
theorem exists_repeated_weight_adjustment
    (weight : ℝ) (windows : List (ℝ × ℝ)) :
    ∃ finalWeight, IsRepeatedWeightAdjustment weight windows finalWeight := by
  induction windows generalizing weight with
  | nil =>
      exact ⟨weight, rfl⟩
  | cons window windows ih =>
      rcases window with ⟨spent, fairShare⟩
      by_cases hunder : spent < fairShare
      · obtain ⟨finalWeight, hpath⟩ := ih (weight + 1)
        exact ⟨finalWeight, weight + 1, ⟨Or.inl ⟨hunder, by linarith⟩, hpath⟩⟩
      · by_cases hover : fairShare < spent
        · obtain ⟨finalWeight, hpath⟩ := ih (weight - 1)
          exact
            ⟨finalWeight, weight - 1,
              ⟨Or.inr (Or.inl ⟨hover, by linarith⟩), hpath⟩⟩
        · have hequal : spent = fairShare := le_antisymm
            (le_of_not_gt hover) (le_of_not_gt hunder)
          obtain ⟨finalWeight, hpath⟩ := ih weight
          exact
            ⟨finalWeight, weight,
              ⟨Or.inr (Or.inr ⟨hequal, rfl⟩), hpath⟩⟩

/-- Advertiser representatives used by the replicated-RANKING proposal. -/
abbrev Representative (Advertiser : Type*) (m : ℕ) := Advertiser × Fin m

/-- Replace each advertiser by `m` equal-budget representatives with identical bids. -/
noncomputable def replicatedInstance
    (m : ℕ) (I : PaperInstance Advertiser Query) :
    PaperInstance (Representative Advertiser m) Query where
  budget r := I.budget r.1 / (m : ℝ)
  bid r q := I.bid r.1 q

/-- Generalized-RANKING score on a replicated advertiser population. -/
noncomputable def replicatedRankingScore
    (I : PaperInstance Advertiser Query)
    (rankWeight : Representative Advertiser m → ℝ)
    (r : Representative Advertiser m) (q : Query) : ℝ :=
  I.bid r.1 q * rankWeight r

/-- The actual finite maximum scan used by one replicated-RANKING decision. -/
noncomputable def replicatedRankingScan
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (m : ℕ) (I : PaperInstance Advertiser Query)
    (rankWeight : Representative Advertiser m → ℝ)
    (S : OccurrenceState (Representative Advertiser m) Query) (q : Query) :
    FiniteMaxScanResult (Representative Advertiser m) :=
  finiteMaxScan
    (occurrenceCanAssign (replicatedInstance m I) S q)
    (fun r => replicatedRankingScore I rankWeight r q)
    (Finset.univ : Finset (Representative Advertiser m)).toList

/-- One occurrence step of the replicated-RANKING proposal. -/
noncomputable def replicatedRankingStep
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (m : ℕ) (I : PaperInstance Advertiser Query)
    (rankWeight : Representative Advertiser m → ℝ)
    (S : OccurrenceState (Representative Advertiser m) Query) (q : Query) :
    OccurrenceState (Representative Advertiser m) Query :=
  applyScanDecision (replicatedInstance m I) S q
    (replicatedRankingScan m I rankWeight S q)

/--
Run the generalized RANKING proposal on every query occurrence, conditional on
the sampled rank weights.  The source's simulation and competitive-factor
discussion remains heuristic and is not asserted here.
-/
noncomputable def runReplicatedRankingProposal
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (m : ℕ) (I : PaperInstance Advertiser Query)
    (rankWeight : Representative Advertiser m → ℝ)
    (history : List Query) :
    OccurrenceState (Representative Advertiser m) Query :=
  runOccurrencesFrom (replicatedRankingStep m I rankWeight)
    initialOccurrenceState history

/-- A representative has exhausted its equal budget in a completed run. -/
def representativeBudgetExhausted
    {Advertiser Query : Type*}
    (m : ℕ) (I : PaperInstance Advertiser Query)
    (S : OccurrenceState (Representative Advertiser m) Query)
    (r : Representative Advertiser m) : Prop :=
  S.spent r = (replicatedInstance m I).budget r

/--
The Section 8 replicated-RANKING exhaustion-order heuristic, made explicit as
a predicate rather than claimed as a proved performance guarantee: within one
original bidder's representatives, exhaustion at a later rank entails
exhaustion at every earlier rank.
-/
def replicatedRankingExhaustionInRankOrder
    {Advertiser Query : Type*}
    (m : ℕ) (I : PaperInstance Advertiser Query)
    (rank : Representative Advertiser m → ℕ)
    (S : OccurrenceState (Representative Advertiser m) Query) : Prop :=
  ∀ r r', r.1 = r'.1 → rank r ≤ rank r' →
    representativeBudgetExhausted m I S r' →
      representativeBudgetExhausted m I S r

/-- Unfold the explicit Section 8 exhaustion-order heuristic. -/
theorem replicatedRankingExhaustionInRankOrder_iff
    {Advertiser Query : Type*}
    (m : ℕ) (I : PaperInstance Advertiser Query)
    (rank : Representative Advertiser m → ℕ)
    (S : OccurrenceState (Representative Advertiser m) Query) :
    replicatedRankingExhaustionInRankOrder m I rank S ↔
      ∀ r r', r.1 = r'.1 → rank r ≤ rank r' →
        representativeBudgetExhausted m I S r' →
          representativeBudgetExhausted m I S r := by
  rfl

/-- A selected representative is affordable and maximizes the rank-scaled bid. -/
theorem replicatedRankingScan_winner_spec
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (m : ℕ) (I : PaperInstance Advertiser Query)
    (rankWeight : Representative Advertiser m → ℝ)
    (S : OccurrenceState (Representative Advertiser m) Query) (q : Query)
    (r : Representative Advertiser m)
    (hchoice : (replicatedRankingScan m I rankWeight S q).winner = some r) :
    occurrenceCanAssign (replicatedInstance m I) S q r ∧
      ∀ r', occurrenceCanAssign (replicatedInstance m I) S q r' →
        replicatedRankingScore I rankWeight r' q ≤
          replicatedRankingScore I rankWeight r q := by
  classical
  have hspec :=
    (finiteMaxScan_winner_spec
      (occurrenceCanAssign (replicatedInstance m I) S q)
      (fun r => replicatedRankingScore I rankWeight r q)
      (Finset.univ : Finset (Representative Advertiser m)).toList).2 r hchoice
  exact ⟨hspec.2.1, fun r' hr' => hspec.2.2 r' (by simp) hr'⟩

/-! ## Section 7 / Theorem 9: source intermediate formulas -/

/-- The epsilon bid in a permuted hard instance, indexed by round and bidder position. -/
noncomputable def theorem9RoundBid
    (N : ℕ) (epsilon : ℝ) (permutation : Equiv.Perm (Fin N))
    (round bidder : Fin N) : ℝ :=
  if permutation bidder ∈ theorem9ActualEligibleBidders N permutation round then
    epsilon
  else 0

/-- In zero-based indexing, exactly positions `round,...,N-1` bid epsilon. -/
theorem theorem9RoundBid_formula
    (N : ℕ) (epsilon : ℝ) (permutation : Equiv.Perm (Fin N))
    (round bidder : Fin N) :
    theorem9RoundBid N epsilon permutation round bidder =
      if (round : ℕ) ≤ (bidder : ℕ) then epsilon else 0 := by
  classical
  unfold theorem9RoundBid
  simp [mem_theorem9ActualEligibleBidders]

/-- Concrete `N`-round, `m`-occurrences-per-round hard AdWords instance. -/
noncomputable def theorem9HardInstance
    (N m : ℕ) (epsilon : ℝ) (permutation : Equiv.Perm (Fin N)) :
    PaperInstance (Fin N) (Fin N × Fin m) where
  budget _ := 1
  bid bidder q :=
    if bidder ∈ theorem9ActualEligibleBidders N permutation q.1 then epsilon else 0

/-- The source offline witness assigns every occurrence of round `i` to `permutation i`. -/
def theorem9HardOfflineAssignment
    (N m : ℕ) (permutation : Equiv.Perm (Fin N)) :
    PaperAssignment (Fin N) (Fin N × Fin m) :=
  fun q => some (permutation q.1)

/-- The displayed offline witness earns `N*m*epsilon`. -/
theorem theorem9HardOfflineAssignment_revenue
    (N m : ℕ) (epsilon : ℝ) (permutation : Equiv.Perm (Fin N)) :
    paperRevenue (theorem9HardInstance N m epsilon permutation)
        (theorem9HardOfflineAssignment N m permutation) =
      (N : ℝ) * (m : ℝ) * epsilon := by
  classical
  unfold paperRevenue Proof.paperRevenue theorem9HardOfflineAssignment
    theorem9HardInstance
  simp [theorem9ActualEligibleBidders, theorem9EligibleBidders]

/-- Under the paper normalization `m*epsilon=1`, the offline witness earns `N`. -/
theorem theorem9HardOfflineAssignment_revenue_eq_N
    (N m : ℕ) (epsilon : ℝ) (permutation : Equiv.Perm (Fin N))
    (hround : (m : ℝ) * epsilon = 1) :
    paperRevenue (theorem9HardInstance N m epsilon permutation)
        (theorem9HardOfflineAssignment N m permutation) = (N : ℝ) := by
  rw [theorem9HardOfflineAssignment_revenue, mul_assoc, hround, mul_one]

/-- The paper's `q_ij`: expected fraction of round `i` allocated to position `j`. -/
noncomputable def theorem9ExpectedRoundAllocation
    (N : ℕ) (algorithm : BMatchingIntegralPrefixAlgorithm N)
    (round bidder : Fin N) : ℝ :=
  pmfExp (uniformPermutationDistribution N) fun permutation =>
    BMatchingIntegralPrefixAlgorithm.prefixAllocation algorithm
      (theorem9ObservedPrefix N permutation round)
      round (permutation bidder)

/-- A finite certificate specialized to the concrete integral prefix algorithms. -/
noncomputable def theorem9IntegralFiniteCertificate (N : ℕ) :
    BMatchingFeasibleObservedPrefixAllocationRevenueCertificate
      N (BMatchingIntegralPrefixAlgorithm N) 1 where
  normalizedRevenue := fun algorithm permutation =>
    (∑ bidder : Fin N,
      min 1
        (∑ round : Fin N,
          BMatchingIntegralPrefixAlgorithm.prefixAllocation algorithm
            (theorem9ObservedPrefix N permutation round)
            round (permutation bidder))) / (N : ℝ)
  prefixAllocation := fun algorithm obs round bidder =>
    BMatchingIntegralPrefixAlgorithm.prefixAllocation algorithm obs round bidder
  normalizedRevenue_le_cappedPrefixAllocationSpend := by
    intro algorithm permutation
    exact le_rfl
  prefixAllocation_zero_of_not_visible := by
    intro algorithm obs round bidder hnot
    exact BMatchingIntegralPrefixAlgorithm.prefixAllocation_zero_of_not_visible
      algorithm obs round bidder hnot
  prefixAllocation_sum_le_one := by
    intro algorithm obs round
    exact BMatchingIntegralPrefixAlgorithm.prefixAllocation_sum_le_one
      algorithm obs round
  revenueBound_le_ratio := by
    by_cases hN : 0 < N
    · exact theorem9NormalizedRevenueUpperBound_le_one hN
    · have hN0 : N = 0 := Nat.eq_zero_of_not_pos hN
      subst N
      norm_num [theorem9NormalizedRevenueUpperBound]

/-- The conversion chain that proves the paper's permutation-symmetry `q_ij` bound. -/
noncomputable def theorem9IntegralRoundCertificate (N : ℕ) :
    BMatchingRoundAllocationRevenueCertificate
      N (BMatchingIntegralPrefixAlgorithm N) 1 :=
  (((theorem9IntegralFiniteCertificate N).toObservedPrefixAllocationRevenueCertificate
      ).toRelabelSymmetricPointwiseAllocationRevenueCertificate
      ).toSymmetricPointwiseAllocationRevenueCertificate
      |>.toPointwiseAllocationRevenueCertificate
      |>.toRoundAllocationRevenueCertificate

/--
Theorem 9's intermediate formula:
`E_pi[q_ij] <= 1/(N-i+1)` for `j >= i`, and it is zero for `j < i`, expressed
in zero-based indices as denominator `N-i`.
-/
theorem theorem9_expected_round_allocation_bound
    (N : ℕ) (algorithm : BMatchingIntegralPrefixAlgorithm N)
    (round bidder : Fin N) :
    theorem9ExpectedRoundAllocation N algorithm round bidder ≤
      if (round : ℕ) ≤ (bidder : ℕ) then
        1 / ((N - (round : ℕ) : ℕ) : ℝ)
      else 0 := by
  change
    (theorem9IntegralRoundCertificate N).expectedRoundBidderAllocation
        algorithm round bidder ≤ _
  exact
    (theorem9IntegralRoundCertificate N).expectedRoundBidderAllocation_le
      algorithm round bidder

/-- An ineligible bidder has exactly zero expected allocation in that round. -/
theorem theorem9_expected_round_allocation_zero_of_ineligible
    (N : ℕ) (algorithm : BMatchingIntegralPrefixAlgorithm N)
    (round bidder : Fin N) (hineligible : ¬ (round : ℕ) ≤ (bidder : ℕ)) :
    theorem9ExpectedRoundAllocation N algorithm round bidder = 0 := by
  unfold theorem9ExpectedRoundAllocation
  calc
    pmfExp (uniformPermutationDistribution N)
        (fun permutation =>
          BMatchingIntegralPrefixAlgorithm.prefixAllocation algorithm
            (theorem9ObservedPrefix N permutation round)
            round (permutation bidder)) =
        pmfExp (uniformPermutationDistribution N) (fun _ => 0) := by
          apply pmfExp_congr
          intro permutation
          apply
            BMatchingIntegralPrefixAlgorithm.prefixAllocation_zero_of_not_visible
          simp [theorem9ObservedPrefix,
            theorem9ActualEligibleBidders_not_mem_of_not_eligible hineligible]
    _ = 0 := pmfExp_zero _

/-- Summing the expected round bounds gives the paper's capped bidder-spend bound. -/
theorem theorem9_expected_bidder_spend_le_harmonic_bound
    (N : ℕ) (algorithm : BMatchingIntegralPrefixAlgorithm N)
    (bidder : Fin N) :
    min 1
        (∑ round : Fin N,
          theorem9ExpectedRoundAllocation N algorithm round bidder) ≤
      theorem9BidderSpendUpperBound N bidder := by
  unfold theorem9BidderSpendUpperBound
  exact min_le_min_left 1
    (Finset.sum_le_sum fun round _ =>
      theorem9_expected_round_allocation_bound N algorithm round bidder)

/--
After averaging over the hard permutation distribution, every deterministic
integral prefix algorithm is bounded by the summed harmonic cap.
-/
theorem theorem9_expected_normalized_revenue_le_harmonic_bound
    (N : ℕ) (algorithm : BMatchingIntegralPrefixAlgorithm N) :
    pmfExp (uniformPermutationDistribution N)
        (fun permutation =>
          (theorem9IntegralRoundCertificate N).normalizedRevenue
            algorithm permutation) ≤
      theorem9NormalizedRevenueUpperBound N := by
  exact
    (theorem9IntegralRoundCertificate N).toRevenueBoundCertificate
      |>.deterministicAverage_le_revenueBound algorithm

/-- Paper-facing expansion of the capped harmonic spend bound for bidder `j`. -/
theorem theorem9_harmonic_spend_formula (N : ℕ) (bidder : Fin N) :
    theorem9BidderSpendUpperBound N bidder =
      min 1
        (∑ round : Fin N,
          if (round : ℕ) ≤ (bidder : ℕ) then
            1 / ((N - (round : ℕ) : ℕ) : ℝ)
          else 0) := by
  rfl

/-- Summing the bidder caps and dividing by OPT `N` gives the finite revenue bound. -/
theorem theorem9_harmonic_revenue_formula (N : ℕ) :
    theorem9NormalizedRevenueUpperBound N =
      (∑ bidder : Fin N, theorem9BidderSpendUpperBound N bidder) / (N : ℝ) := by
  rfl

/--
Uncapped harmonic spend accumulated before zero-based round `r` in the nested
suffix instance.
-/
noncomputable def fluidHarmonicBefore (N r : ℕ) : ℝ :=
  ∑ round ∈ Finset.range r, 1 / ((N - round : ℕ) : ℝ)

/-- Capped common spend of every bidder still eligible before round `r`. -/
noncomputable def fluidCappedSpendBefore (N r : ℕ) : ℝ :=
  min 1 (fluidHarmonicBefore N r)

/-- Equal payment assigned to each still-eligible bidder during round `r`. -/
noncomputable def fluidBalanceRoundIncrement (N r : ℕ) : ℝ :=
  fluidCappedSpendBefore N (r + 1) - fluidCappedSpendBefore N r

/-- Fluid allocation in the identity-permutation nested suffix-round family. -/
noncomputable def fluidBalanceAllocation
    (N : ℕ) (round bidder : Fin N) : ℝ :=
  if (round : ℕ) ≤ (bidder : ℕ) then
    fluidBalanceRoundIncrement N round
  else 0

/-- Spend state immediately before a round; bidders already removed retain final spend. -/
noncomputable def fluidBalanceSpentBefore
    (N : ℕ) (round bidder : Fin N) : ℝ :=
  if (round : ℕ) ≤ (bidder : ℕ) then
    fluidCappedSpendBefore N round
  else
    fluidCappedSpendBefore N ((bidder : ℕ) + 1)

/-- Final spend of one bidder in the explicit fluid execution. -/
noncomputable def fluidBalanceFinalSpend (N : ℕ) (bidder : Fin N) : ℝ :=
  fluidCappedSpendBefore N ((bidder : ℕ) + 1)

theorem fluidHarmonicBefore_succ (N r : ℕ) :
    fluidHarmonicBefore N (r + 1) =
      fluidHarmonicBefore N r + 1 / ((N - r : ℕ) : ℝ) := by
  simp [fluidHarmonicBefore, Finset.sum_range_succ]

theorem fluidHarmonicBefore_nonneg (N r : ℕ) :
    0 ≤ fluidHarmonicBefore N r := by
  unfold fluidHarmonicBefore
  exact Finset.sum_nonneg fun i _ => by positivity

theorem fluidCappedSpendBefore_nonneg (N r : ℕ) :
    0 ≤ fluidCappedSpendBefore N r := by
  exact le_min (by norm_num) (fluidHarmonicBefore_nonneg N r)

theorem fluidCappedSpendBefore_le_one (N r : ℕ) :
    fluidCappedSpendBefore N r ≤ 1 := by
  exact min_le_left _ _

theorem fluidCappedSpendBefore_mono_step (N r : ℕ) :
    fluidCappedSpendBefore N r ≤ fluidCappedSpendBefore N (r + 1) := by
  unfold fluidCappedSpendBefore
  apply min_le_min (le_refl 1)
  rw [fluidHarmonicBefore_succ]
  have hterm : 0 ≤ 1 / ((N - r : ℕ) : ℝ) := by positivity
  linarith

theorem fluidBalanceRoundIncrement_nonneg (N r : ℕ) :
    0 ≤ fluidBalanceRoundIncrement N r := by
  unfold fluidBalanceRoundIncrement
  exact sub_nonneg.mpr (fluidCappedSpendBefore_mono_step N r)

/-- Capping can only reduce the equal `1/(N-r)` uncapped round increment. -/
theorem fluidBalanceRoundIncrement_le_harmonic_step (N r : ℕ) :
    fluidBalanceRoundIncrement N r ≤ 1 / ((N - r : ℕ) : ℝ) := by
  let H := fluidHarmonicBefore N r
  let x := 1 / ((N - r : ℕ) : ℝ)
  have hx : 0 ≤ x := by
    dsimp [x]
    positivity
  have hsucc : fluidHarmonicBefore N (r + 1) = H + x := by
    simpa [H, x] using fluidHarmonicBefore_succ N r
  unfold fluidBalanceRoundIncrement fluidCappedSpendBefore
  rw [hsucc]
  change min 1 (H + x) - min 1 H ≤ x
  by_cases hH : 1 ≤ H
  · have hHx : 1 ≤ H + x := hH.trans (le_add_of_nonneg_right hx)
    rw [min_eq_left hHx, min_eq_left hH]
    linarith
  · have hHle : H ≤ 1 := le_of_not_ge hH
    by_cases hsum : H + x ≤ 1
    · rw [min_eq_right hsum, min_eq_right hHle]
      linarith
    · have hone_le : 1 ≤ H + x := le_of_not_ge hsum
      rw [min_eq_left hone_le, min_eq_right hHle]
      linarith

/-- The explicit allocation never assigns mass to a bidder outside the suffix. -/
theorem fluidBalanceAllocation_zero_of_ineligible
    (N : ℕ) (round bidder : Fin N)
    (h : ¬ (round : ℕ) ≤ (bidder : ℕ)) :
    fluidBalanceAllocation N round bidder = 0 := by
  simp [fluidBalanceAllocation, h]

/-- All active bidders have equal spend, hence each is a least-spent eligible bidder. -/
theorem fluidBalance_eligible_equal_least_spend
    (N : ℕ) (round bidder bidder' : Fin N)
    (hbidder : (round : ℕ) ≤ (bidder : ℕ))
    (hbidder' : (round : ℕ) ≤ (bidder' : ℕ)) :
    fluidBalanceSpentBefore N round bidder =
      fluidBalanceSpentBefore N round bidder' := by
  simp [fluidBalanceSpentBefore, hbidder, hbidder']

/-- Fluid allocations are nonnegative. -/
theorem fluidBalanceAllocation_nonneg
    (N : ℕ) (round bidder : Fin N) :
    0 ≤ fluidBalanceAllocation N round bidder := by
  unfold fluidBalanceAllocation
  split_ifs
  · exact fluidBalanceRoundIncrement_nonneg N round
  · exact le_rfl

/-- The eligible-cohort allocation is its cardinality times the common increment. -/
theorem fluidBalance_sum_eligible_eq_card_mul
    (N : ℕ) (round : Fin N) :
    (∑ bidder ∈ theorem9EligibleBidders N round,
      fluidBalanceAllocation N round bidder) =
      ((theorem9EligibleBidders N round).card : ℝ) *
        fluidBalanceRoundIncrement N round := by
  calc
    (∑ bidder ∈ theorem9EligibleBidders N round,
        fluidBalanceAllocation N round bidder) =
        ∑ _bidder ∈ theorem9EligibleBidders N round,
          fluidBalanceRoundIncrement N round := by
            apply Finset.sum_congr rfl
            intro bidder hbidder
            rw [fluidBalanceAllocation, if_pos
              ((mem_theorem9EligibleBidders N round bidder).mp hbidder)]
    _ = ((theorem9EligibleBidders N round).card : ℝ) *
        fluidBalanceRoundIncrement N round := by simp

/-- Each bidder's post-round spend remains within its unit budget. -/
theorem fluidBalance_budget_feasible
    (N : ℕ) (round bidder : Fin N) :
    fluidBalanceSpentBefore N round bidder +
        fluidBalanceAllocation N round bidder ≤ 1 := by
  by_cases h : (round : ℕ) ≤ (bidder : ℕ)
  · have hcap := fluidCappedSpendBefore_le_one N ((round : ℕ) + 1)
    simpa [fluidBalanceSpentBefore, fluidBalanceAllocation,
      fluidBalanceRoundIncrement, h] using hcap
  · have hcap := fluidCappedSpendBefore_le_one N ((bidder : ℕ) + 1)
    simpa [fluidBalanceSpentBefore, fluidBalanceAllocation, h] using hcap

/-- At most one unit of query mass is allocated in every round. -/
theorem fluidBalance_round_allocation_conservation
    (N : ℕ) (round : Fin N) :
    (∑ bidder ∈ theorem9EligibleBidders N round,
      fluidBalanceAllocation N round bidder) ≤ 1 := by
  have hcount : 0 < N - (round : ℕ) := Nat.sub_pos_of_lt round.isLt
  have hcountReal : 0 < ((N - (round : ℕ) : ℕ) : ℝ) := by
    exact_mod_cast hcount
  have hincrement :=
    fluidBalanceRoundIncrement_le_harmonic_step N (round : ℕ)
  calc
    (∑ bidder ∈ theorem9EligibleBidders N round,
        fluidBalanceAllocation N round bidder) =
        ((N - (round : ℕ) : ℕ) : ℝ) *
          fluidBalanceRoundIncrement N round := by
            rw [← theorem9EligibleBidders_card]
            exact fluidBalance_sum_eligible_eq_card_mul N round
    _ ≤ ((N - (round : ℕ) : ℕ) : ℝ) *
        (1 / ((N - (round : ℕ) : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hincrement hcountReal.le
    _ = 1 := by field_simp [ne_of_gt hcountReal]

/--
Every fluid round either allocates its full unit query mass or leaves every
eligible bidder exactly saturated after the round.  Thus any discard is caused
by budget exhaustion, not by an externally stipulated slack variable.
-/
theorem fluidBalance_round_full_or_all_eligible_saturated
    (N : ℕ) (round : Fin N) :
    (∑ bidder ∈ theorem9EligibleBidders N round,
      fluidBalanceAllocation N round bidder) = 1 ∨
    ∀ bidder : Fin N, bidder ∈ theorem9EligibleBidders N round →
      fluidBalanceSpentBefore N round bidder +
        fluidBalanceAllocation N round bidder = 1 := by
  have hcount : 0 < N - (round : ℕ) := Nat.sub_pos_of_lt round.isLt
  have hcountReal : 0 < ((N - (round : ℕ) : ℕ) : ℝ) := by
    exact_mod_cast hcount
  let H := fluidHarmonicBefore N (round : ℕ)
  let x := 1 / ((N - (round : ℕ) : ℕ) : ℝ)
  have hx : 0 < x := by
    dsimp [x]
    positivity
  have hsucc : fluidHarmonicBefore N ((round : ℕ) + 1) = H + x := by
    simpa [H, x] using fluidHarmonicBefore_succ N (round : ℕ)
  by_cases hfull : H + x ≤ 1
  · left
    have hH : H ≤ 1 := le_trans (le_add_of_nonneg_right hx.le) hfull
    have hincrement : fluidBalanceRoundIncrement N round = x := by
      unfold fluidBalanceRoundIncrement fluidCappedSpendBefore
      rw [hsucc]
      change min 1 (H + x) - min 1 H = x
      rw [min_eq_right hfull, min_eq_right hH]
      ring
    calc
      (∑ bidder ∈ theorem9EligibleBidders N round,
          fluidBalanceAllocation N round bidder) =
          ((N - (round : ℕ) : ℕ) : ℝ) *
            fluidBalanceRoundIncrement N round := by
              rw [← theorem9EligibleBidders_card]
              exact fluidBalance_sum_eligible_eq_card_mul N round
      _ = ((N - (round : ℕ) : ℕ) : ℝ) * x := by rw [hincrement]
      _ = 1 := by
        dsimp [x]
        field_simp [ne_of_gt hcountReal]
  · right
    have hsaturated : fluidCappedSpendBefore N ((round : ℕ) + 1) = 1 := by
      unfold fluidCappedSpendBefore
      rw [hsucc]
      exact min_eq_left (le_of_not_ge hfull)
    intro bidder hbidder
    have heligible : (round : ℕ) ≤ (bidder : ℕ) :=
      (mem_theorem9EligibleBidders N round bidder).mp hbidder
    simpa [fluidBalanceSpentBefore, fluidBalanceAllocation,
      fluidBalanceRoundIncrement, heligible] using hsaturated

/-- Strictly subunit allocation implies saturation of every eligible bidder. -/
theorem fluidBalance_no_discard_unless_all_eligible_saturated
    (N : ℕ) (round : Fin N)
    (hdiscard :
      (∑ bidder ∈ theorem9EligibleBidders N round,
        fluidBalanceAllocation N round bidder) < 1) :
    ∀ bidder : Fin N, bidder ∈ theorem9EligibleBidders N round →
      fluidBalanceSpentBefore N round bidder +
        fluidBalanceAllocation N round bidder = 1 := by
  rcases fluidBalance_round_full_or_all_eligible_saturated N round with hfull | hsaturated
  · linarith
  · exact hsaturated

/-- The round increments telescope to the stated final spend of every bidder. -/
theorem fluidBalance_finalSpend_eq_sum_allocation
    (N : ℕ) (bidder : Fin N) :
    fluidBalanceFinalSpend N bidder =
      ∑ round : Fin N, fluidBalanceAllocation N round bidder := by
  let f : ℕ → ℝ := fluidCappedSpendBefore N
  have hfin_to_nat :
      (∑ round : Fin N, fluidBalanceAllocation N round bidder) =
        ∑ round ∈ Finset.range N,
          if round ≤ (bidder : ℕ) then f (round + 1) - f round else 0 := by
    symm
    simpa [fluidBalanceAllocation, fluidBalanceRoundIncrement, f] using
      (Finset.sum_range
        (n := N)
        (fun round : ℕ =>
          if round ≤ (bidder : ℕ) then f (round + 1) - f round else 0))
  have hprefix_set :
      (Finset.range N).filter (fun round => round ≤ (bidder : ℕ)) =
        Finset.range ((bidder : ℕ) + 1) := by
    ext round
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · intro hround
      exact Nat.lt_succ_of_le hround.2
    · intro hround
      have hle : round ≤ (bidder : ℕ) := Nat.le_of_lt_succ hround
      exact ⟨lt_of_le_of_lt hle bidder.isLt, hle⟩
  rw [hfin_to_nat, ← Finset.sum_filter, hprefix_set]
  rw [Finset.sum_range_sub]
  simp [fluidBalanceFinalSpend, f, fluidCappedSpendBefore,
    fluidHarmonicBefore]

/-- Nat-indexed telescoping prefix used to connect decision-time state to prior allocations. -/
theorem fluidBalance_natPrefix_telescope
    (N r : ℕ) (bidder : Fin N) :
    (∑ round ∈ Finset.range r,
      if round ≤ (bidder : ℕ) then
        fluidBalanceRoundIncrement N round
      else 0) =
      fluidCappedSpendBefore N (min r ((bidder : ℕ) + 1)) := by
  have hset :
      (Finset.range r).filter (fun round => round ≤ (bidder : ℕ)) =
        Finset.range (min r ((bidder : ℕ) + 1)) := by
    ext round
    simp
  rw [← Finset.sum_filter, hset]
  unfold fluidBalanceRoundIncrement
  rw [Finset.sum_range_sub]
  simp [fluidCappedSpendBefore, fluidHarmonicBefore]

/--
At every decision time, `spentBefore` is exactly the sum of this bidder's
allocations in earlier rounds; it is not an independently stipulated state.
-/
theorem fluidBalance_spentBefore_eq_prior_allocations
    (N : ℕ) (round bidder : Fin N) :
    fluidBalanceSpentBefore N round bidder =
      ∑ previous : Fin N,
        if (previous : ℕ) < (round : ℕ) then
          fluidBalanceAllocation N previous bidder
        else 0 := by
  have hfin_to_nat :
      (∑ previous : Fin N,
        if (previous : ℕ) < (round : ℕ) then
          fluidBalanceAllocation N previous bidder
        else 0) =
      ∑ previous ∈ Finset.range N,
        if previous < (round : ℕ) then
          (if previous ≤ (bidder : ℕ) then
            fluidBalanceRoundIncrement N previous else 0)
        else 0 := by
    symm
    simpa [fluidBalanceAllocation] using
      (Finset.sum_range
        (n := N)
        (fun previous : ℕ =>
          if previous < (round : ℕ) then
            (if previous ≤ (bidder : ℕ) then
              fluidBalanceRoundIncrement N previous else 0)
          else 0))
  have hround_set :
      (Finset.range N).filter (fun previous => previous < (round : ℕ)) =
        Finset.range (round : ℕ) := by
    ext previous
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · intro h
      exact h.2
    · intro h
      exact ⟨lt_trans h round.isLt, h⟩
  rw [hfin_to_nat, ← Finset.sum_filter, hround_set]
  rw [fluidBalance_natPrefix_telescope]
  by_cases h : (round : ℕ) ≤ (bidder : ℕ)
  · have hmin : min (round : ℕ) ((bidder : ℕ) + 1) = round := by
      omega
    simp [fluidBalanceSpentBefore, h, hmin]
  · have hmin : min (round : ℕ) ((bidder : ℕ) + 1) =
        (bidder : ℕ) + 1 := by
      omega
    simp [fluidBalanceSpentBefore, h, hmin]

/-- Consecutive round states update by exactly the current round allocation. -/
theorem fluidBalance_state_update
    (N : ℕ) (round next bidder : Fin N)
    (hnext : (next : ℕ) = (round : ℕ) + 1) :
    fluidBalanceSpentBefore N next bidder =
      fluidBalanceSpentBefore N round bidder +
        fluidBalanceAllocation N round bidder := by
  by_cases hcur : (round : ℕ) ≤ (bidder : ℕ)
  · by_cases hnxt : (next : ℕ) ≤ (bidder : ℕ)
    · have hnot : ¬ (bidder : ℕ) ≤ (round : ℕ) := by omega
      have hnotFin : ¬ bidder ≤ round := by
        intro h
        exact hnot h
      simp [fluidBalanceSpentBefore, fluidBalanceAllocation,
        fluidBalanceRoundIncrement, hcur, hnxt, hnext, hnot, hnotFin]
    · have hb : (bidder : ℕ) = (round : ℕ) := by omega
      simp [fluidBalanceSpentBefore, fluidBalanceAllocation,
        fluidBalanceRoundIncrement, hcur, hnxt, hnext, hb]
  · have hnxt : ¬ (next : ℕ) ≤ (bidder : ℕ) := by omega
    simp [fluidBalanceSpentBefore, fluidBalanceAllocation, hcur, hnxt]

/-- The explicit final spend is the paper's capped harmonic prefix. -/
theorem fluidBalance_finalSpend_eq_harmonicCap
    (N : ℕ) (bidder : Fin N) :
    fluidBalanceFinalSpend N bidder = theorem9BidderSpendUpperBound N bidder := by
  let g : ℕ → ℝ := fun round => 1 / ((N - round : ℕ) : ℝ)
  have hfin_to_nat :
      (∑ round : Fin N,
        if (round : ℕ) ≤ (bidder : ℕ) then g round else 0) =
        ∑ round ∈ Finset.range N,
          if round ≤ (bidder : ℕ) then g round else 0 := by
    symm
    simpa using
      (Finset.sum_range
        (n := N)
        (fun round : ℕ =>
          if round ≤ (bidder : ℕ) then g round else 0))
  have hprefix_set :
      (Finset.range N).filter (fun round => round ≤ (bidder : ℕ)) =
        Finset.range ((bidder : ℕ) + 1) := by
    ext round
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · intro hround
      exact Nat.lt_succ_of_le hround.2
    · intro hround
      have hle : round ≤ (bidder : ℕ) := Nat.le_of_lt_succ hround
      exact ⟨lt_of_le_of_lt hle bidder.isLt, hle⟩
  unfold fluidBalanceFinalSpend fluidCappedSpendBefore fluidHarmonicBefore
    theorem9BidderSpendUpperBound
  rw [hfin_to_nat, ← Finset.sum_filter, hprefix_set]

/--
A precise fluid BALANCE execution certificate for the nested suffix-round
family.  Its fields expose rather than assume the algorithmic invariants.
-/
structure FluidBalanceExecution (N : ℕ) where
  allocation : Fin N → Fin N → ℝ
  spentBefore : Fin N → Fin N → ℝ
  finalSpend : Fin N → ℝ
  zero_of_ineligible : ∀ (round bidder : Fin N),
    ¬ (round : ℕ) ≤ (bidder : ℕ) → allocation round bidder = 0
  eligible_equal_least_spend : ∀ (round bidder bidder' : Fin N),
    (round : ℕ) ≤ (bidder : ℕ) →
    (round : ℕ) ≤ (bidder' : ℕ) →
      spentBefore round bidder = spentBefore round bidder'
  allocation_nonneg : ∀ (round bidder : Fin N), 0 ≤ allocation round bidder
  budget_feasible : ∀ (round bidder : Fin N),
    spentBefore round bidder + allocation round bidder ≤ 1
  spentBefore_eq_prefix : ∀ (round bidder : Fin N),
    spentBefore round bidder =
      ∑ previous : Fin N,
        if (previous : ℕ) < (round : ℕ) then allocation previous bidder else 0
  state_update : ∀ (round next bidder : Fin N),
    (next : ℕ) = (round : ℕ) + 1 →
      spentBefore next bidder = spentBefore round bidder + allocation round bidder
  round_conservation : ∀ (round : Fin N),
    (∑ bidder ∈ theorem9EligibleBidders N round,
      allocation round bidder) ≤ 1
  work_conserving_or_saturated : ∀ (round : Fin N),
    (∑ bidder ∈ theorem9EligibleBidders N round,
      allocation round bidder) = 1 ∨
    ∀ bidder : Fin N, bidder ∈ theorem9EligibleBidders N round →
      spentBefore round bidder + allocation round bidder = 1
  finalSpend_eq_sum : ∀ bidder : Fin N,
    finalSpend bidder = ∑ round : Fin N, allocation round bidder

/-- The explicit water-filling construction satisfies the fluid BALANCE certificate. -/
noncomputable def nestedSuffixFluidBalanceExecution (N : ℕ) :
    FluidBalanceExecution N where
  allocation := fluidBalanceAllocation N
  spentBefore := fluidBalanceSpentBefore N
  finalSpend := fluidBalanceFinalSpend N
  zero_of_ineligible := fluidBalanceAllocation_zero_of_ineligible N
  eligible_equal_least_spend := fluidBalance_eligible_equal_least_spend N
  allocation_nonneg := fluidBalanceAllocation_nonneg N
  budget_feasible := fluidBalance_budget_feasible N
  spentBefore_eq_prefix := fluidBalance_spentBefore_eq_prior_allocations N
  state_update := fluidBalance_state_update N
  round_conservation := fluidBalance_round_allocation_conservation N
  work_conserving_or_saturated :=
    fluidBalance_round_full_or_all_eligible_saturated N
  finalSpend_eq_sum := fluidBalance_finalSpend_eq_sum_allocation N

/-- Unit-mass eligibility profile obtained by fluidizing one hard-instance round. -/
def theorem9HardFluidRoundMass (N : ℕ) (round bidder : Fin N) : ℝ :=
  if (round : ℕ) ≤ (bidder : ℕ) then 1 else 0

/--
With `m` occurrences of bid `1/m`, the concrete identity-permutation hard
instance has exactly the unit round mass used by the fluid execution.
-/
theorem theorem9HardInstance_identity_round_bid_mass
    (N m : ℕ) (hm : 0 < m) (round bidder : Fin N) :
    (∑ copy : Fin m,
      (theorem9HardInstance N m (1 / (m : ℝ)) (Equiv.refl (Fin N))).bid
        bidder (round, copy)) =
      theorem9HardFluidRoundMass N round bidder := by
  change (∑ _copy : Fin m,
      theorem9RoundBid N (1 / (m : ℝ)) (Equiv.refl (Fin N)) round bidder) = _
  rw [theorem9RoundBid_formula]
  by_cases heligible : (round : ℕ) ≤ (bidder : ℕ)
  · simp [theorem9HardFluidRoundMass, heligible]
    field_simp [Nat.cast_ne_zero.mpr (ne_of_gt hm)]
  · simp [theorem9HardFluidRoundMass, heligible]

/-- The concrete aggregate round-bid profiles converge pointwise to the fluid input. -/
theorem theorem9HardInstance_identity_round_bid_mass_tendsto
    (N : ℕ) (round bidder : Fin N) :
    Filter.Tendsto
      (fun m : ℕ =>
        ∑ copy : Fin (m + 1),
          (theorem9HardInstance N (m + 1) (1 / ((m + 1 : ℕ) : ℝ))
            (Equiv.refl (Fin N))).bid bidder (round, copy))
      Filter.atTop
      (nhds (theorem9HardFluidRoundMass N round bidder)) := by
  have hprofile :
      (fun m : ℕ =>
        ∑ copy : Fin (m + 1),
          (theorem9HardInstance N (m + 1) (1 / ((m + 1 : ℕ) : ℝ))
            (Equiv.refl (Fin N))).bid bidder (round, copy)) =
        fun _m : ℕ => theorem9HardFluidRoundMass N round bidder := by
    funext m
    exact theorem9HardInstance_identity_round_bid_mass
      N (m + 1) (Nat.succ_pos m) round bidder
  rw [hprofile]
  exact tendsto_const_nhds

/-- The concrete hard family is genuinely in the paper's small-bids regime. -/
theorem theorem9HardInstance_bid_size_tendsto_zero :
    Filter.Tendsto (fun m : ℕ => (1 / (m : ℝ) : ℝ))
      Filter.atTop (nhds 0) := by
  simpa using (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))

/--
Formal small-bids fluidization contract for the concrete Theorem 9 occurrence
family.  It pins the fluid input to exact finite round bid masses while bid size
tends to zero, and it requires the allocation-derived, work-conserving BALANCE
rules rather than stipulating only a payoff formula.
-/
structure Theorem9HardBalanceFluidLimit (N : ℕ) where
  execution : FluidBalanceExecution N
  finite_round_bid_mass : ∀ m : ℕ, 0 < m → ∀ round bidder : Fin N,
    (∑ copy : Fin m,
      (theorem9HardInstance N m (1 / (m : ℝ)) (Equiv.refl (Fin N))).bid
        bidder (round, copy)) = theorem9HardFluidRoundMass N round bidder
  bid_size_tendsto_zero :
    Filter.Tendsto (fun m : ℕ => (1 / (m : ℝ) : ℝ))
      Filter.atTop (nhds 0)
  finite_round_bid_mass_tendsto : ∀ round bidder : Fin N,
    Filter.Tendsto
      (fun m : ℕ =>
        ∑ copy : Fin (m + 1),
          (theorem9HardInstance N (m + 1) (1 / ((m + 1 : ℕ) : ℝ))
            (Equiv.refl (Fin N))).bid bidder (round, copy))
      Filter.atTop
      (nhds (theorem9HardFluidRoundMass N round bidder))
  allocation_zero_of_zero_round_mass : ∀ round bidder,
    theorem9HardFluidRoundMass N round bidder = 0 →
      execution.allocation round bidder = 0
  eligible_equal_least_spend : ∀ round bidder bidder',
    theorem9HardFluidRoundMass N round bidder = 1 →
    theorem9HardFluidRoundMass N round bidder' = 1 →
      execution.spentBefore round bidder = execution.spentBefore round bidder'
  spentBefore_eq_prior_allocations : ∀ round bidder,
    execution.spentBefore round bidder =
      ∑ previous : Fin N,
        if (previous : ℕ) < (round : ℕ) then
          execution.allocation previous bidder
        else 0
  budget_feasible : ∀ round bidder,
    execution.spentBefore round bidder + execution.allocation round bidder ≤ 1
  work_conserving_or_saturated : ∀ round,
    (∑ bidder ∈ theorem9EligibleBidders N round,
      execution.allocation round bidder) = 1 ∨
    ∀ bidder, bidder ∈ theorem9EligibleBidders N round →
      execution.spentBefore round bidder + execution.allocation round bidder = 1
  finalSpend_eq_sum : ∀ bidder,
    execution.finalSpend bidder =
      ∑ round : Fin N, execution.allocation round bidder

/-- The explicit harmonic water-filling execution satisfies the full fluid-limit contract. -/
noncomputable def theorem9NestedSuffixBalanceFluidLimit (N : ℕ) :
    Theorem9HardBalanceFluidLimit N where
  execution := nestedSuffixFluidBalanceExecution N
  finite_round_bid_mass := theorem9HardInstance_identity_round_bid_mass N
  bid_size_tendsto_zero := theorem9HardInstance_bid_size_tendsto_zero
  finite_round_bid_mass_tendsto :=
    theorem9HardInstance_identity_round_bid_mass_tendsto N
  allocation_zero_of_zero_round_mass := by
    intro round bidder hmass
    have hineligible : ¬ (round : ℕ) ≤ (bidder : ℕ) := by
      intro heligible
      simp [theorem9HardFluidRoundMass, heligible] at hmass
    exact (nestedSuffixFluidBalanceExecution N).zero_of_ineligible
      round bidder hineligible
  eligible_equal_least_spend := by
    intro round bidder bidder' hmass hmass'
    have heligible : (round : ℕ) ≤ (bidder : ℕ) := by
      by_contra h
      simp [theorem9HardFluidRoundMass, h] at hmass
    have heligible' : (round : ℕ) ≤ (bidder' : ℕ) := by
      by_contra h
      simp [theorem9HardFluidRoundMass, h] at hmass'
    exact (nestedSuffixFluidBalanceExecution N).eligible_equal_least_spend
      round bidder bidder' heligible heligible'
  spentBefore_eq_prior_allocations :=
    (nestedSuffixFluidBalanceExecution N).spentBefore_eq_prefix
  budget_feasible := (nestedSuffixFluidBalanceExecution N).budget_feasible
  work_conserving_or_saturated :=
    (nestedSuffixFluidBalanceExecution N).work_conserving_or_saturated
  finalSpend_eq_sum := (nestedSuffixFluidBalanceExecution N).finalSpend_eq_sum

/-! ## Section 4: an execution that realizes the tight factor-LP witness -/

/-- Size of the nested active cohort at a finite tightness stage. -/
def finiteTightActiveCount (m stage : ℕ) : ℕ :=
  (m + 1) ^ (m - stage) * m ^ stage

/-- The number of bidders that leave after a preterminal stage. -/
def finiteTightDepartingCount (m stage : ℕ) : ℕ :=
  finiteTightActiveCount m stage / (m + 1)

/-- The finite query identifiers in the nested-cohort tight instance. -/
inductive FiniteTightQuery (m : ℕ) where
  | stage (stage : Fin m) (target : Fin (finiteTightActiveCount m stage)) :
      FiniteTightQuery m
  | final (bidder : Fin (finiteTightActiveCount m m)) : FiniteTightQuery m
  | reserve (bidder : Fin (finiteTightActiveCount m m)) (copy : Fin m) :
      FiniteTightQuery m
  deriving DecidableEq, Fintype

abbrev FiniteTightAdvertiser (m : ℕ) := Fin ((m + 1) ^ m)

theorem finiteTightActiveCount_at_final (m : ℕ) :
    finiteTightActiveCount m m = m ^ m := by
  simp [finiteTightActiveCount]

theorem finiteTightDepartingCount_formula (m stage : ℕ) (hstage : stage < m) :
    finiteTightDepartingCount m stage =
      (m + 1) ^ (m - (stage + 1)) * m ^ stage := by
  unfold finiteTightDepartingCount finiteTightActiveCount
  have hsub : m - stage = (m - (stage + 1)) + 1 := by omega
  rw [hsub, pow_succ]
  calc
    ((m + 1) ^ (m - (stage + 1)) * (m + 1) * m ^ stage) / (m + 1) =
        ((m + 1) ^ (m - (stage + 1)) * m ^ stage * (m + 1)) / (m + 1) := by
          congr 1
          ring
    _ = (m + 1) ^ (m - (stage + 1)) * m ^ stage := by
          rw [Nat.mul_comm]
          exact Nat.mul_div_right _ (by omega)

theorem finiteTightDepartingCount_mul_width (m stage : ℕ) (hstage : stage < m) :
    finiteTightDepartingCount m stage * (m + 1) =
      finiteTightActiveCount m stage := by
  rw [finiteTightDepartingCount_formula m stage hstage]
  unfold finiteTightActiveCount
  have hsub : m - stage = (m - (stage + 1)) + 1 := by omega
  rw [hsub, pow_succ]
  ring

theorem finiteTightActiveCount_sub_succ (m stage : ℕ) (hstage : stage < m) :
    finiteTightActiveCount m stage - finiteTightActiveCount m (stage + 1) =
      finiteTightDepartingCount m stage := by
  rw [finiteTightDepartingCount_formula m stage hstage]
  unfold finiteTightActiveCount
  have hsub : m - stage = (m - (stage + 1)) + 1 := by omega
  have hwidth : (m + 1) ^ (m - stage) =
      (m + 1) ^ (m - (stage + 1)) * (m + 1) := by
    rw [hsub, pow_succ]
  have hstagepow : m ^ (stage + 1) = m ^ stage * m := by
    rw [pow_succ]
  rw [hwidth, hstagepow]
  calc
    ((m + 1) ^ (m - (stage + 1)) * (m + 1)) * m ^ stage -
        (m + 1) ^ (m - (stage + 1)) * (m ^ stage * m) =
        ((m + 1) ^ (m - (stage + 1)) * m ^ stage) * (m + 1) -
          ((m + 1) ^ (m - (stage + 1)) * m ^ stage) * m := by
      congr 1 <;> ring
    _ = ((m + 1) ^ (m - (stage + 1)) * m ^ stage) * ((m + 1) - m) := by
      rw [Nat.mul_sub_left_distrib]
    _ = (m + 1) ^ (m - (stage + 1)) * m ^ stage := by
      have hone : m + 1 - m = 1 := by omega
      rw [hone, Nat.mul_one]

/-- Every active cohort is contained in the initial population. -/
theorem finiteTightActiveCount_le_population (m stage : ℕ) (hstage : stage ≤ m) :
    finiteTightActiveCount m stage ≤ (m + 1) ^ m := by
  unfold finiteTightActiveCount
  calc
    (m + 1) ^ (m - stage) * m ^ stage ≤
        (m + 1) ^ (m - stage) * (m + 1) ^ stage := by
      apply Nat.mul_le_mul_left
      exact Nat.pow_le_pow_left (by omega) stage
    _ = (m + 1) ^ m := by
      rw [← pow_add]
      congr 1
      omega

/-- Include a member of an active cohort in the original bidder population. -/
def finiteTightEmbedActive (m stage : ℕ) (hstage : stage ≤ m) :
    Fin (finiteTightActiveCount m stage) → Fin ((m + 1) ^ m) := fun a =>
  ⟨a.val, lt_of_lt_of_le a.isLt
    (finiteTightActiveCount_le_population m stage hstage)⟩

/-- Bidders eligible for a query in the finite nested-cohort construction. -/
def finiteTightEligible (m : ℕ) (a : FiniteTightAdvertiser m)
    (q : FiniteTightQuery m) : Prop :=
  match q with
  | .stage stage _ => a.val < finiteTightActiveCount m stage
  | .final _ => a.val < finiteTightActiveCount m m
  | .reserve _ _ => a.val < finiteTightActiveCount m m

/-- The concrete unit-budget finite tightness instance. -/
noncomputable def finiteTightInstance (m : ℕ) :
    AdWordsInstance (FiniteTightAdvertiser m) (FiniteTightQuery m) := by
  classical
  exact
    { budget := fun _ => 1
      bid := fun a q =>
        if finiteTightEligible m a q then 1 / ((m + 1 : ℕ) : ℝ) else 0 }

/-- The intended fixed-priority target for each query. -/
def finiteTightQueryTarget (m : ℕ) :
    FiniteTightQuery m → FiniteTightAdvertiser m
  | .stage stage a => finiteTightEmbedActive m stage stage.isLt.le a
  | .final a => finiteTightEmbedActive m m le_rfl a
  | .reserve a _ => finiteTightEmbedActive m m le_rfl a

theorem finiteTightQueryTarget_eligible (m : ℕ) (q : FiniteTightQuery m) :
    finiteTightEligible m (finiteTightQueryTarget m q) q := by
  cases q with
  | stage stage a => exact a.isLt
  | final a => exact a.isLt
  | reserve a copy => exact a.isLt

theorem finiteTightInstance_target_bid (m : ℕ) (q : FiniteTightQuery m) :
    (finiteTightInstance m).bid (finiteTightQueryTarget m q) q =
      1 / ((m + 1 : ℕ) : ℝ) := by
  classical
  unfold finiteTightInstance
  change (if finiteTightEligible m (finiteTightQueryTarget m q) q then
    1 / ((m + 1 : ℕ) : ℝ) else 0) = 1 / ((m + 1 : ℕ) : ℝ)
  rw [if_pos (finiteTightQueryTarget_eligible m q)]

/-- A query whose eligible bidders form a prefix chooses the first unserved
member of that prefix under Balance. -/
theorem finiteTight_target_isBalance_of_prefix_state
    (m n : ℕ) (q : FiniteTightQuery m)
    (hactive : ∀ b : FiniteTightAdvertiser m,
      finiteTightEligible m b q ↔ b.val < n)
    (A : AdWordsInstance.Assignment (FiniteTightAdvertiser m) (FiniteTightQuery m))
    (c : ℝ)
    (hc : c < 1)
    (hcstep : c + 1 / ((m + 1 : ℕ) : ℝ) ≤ 1)
    (hspend : ∀ b : FiniteTightAdvertiser m,
      b.val < n →
        (finiteTightInstance m).spend A b =
          if b.val < (finiteTightQueryTarget m q).val then
            c + 1 / ((m + 1 : ℕ) : ℝ) else c) :
    (finiteTightInstance m).IsBalanceChoice A q (finiteTightQueryTarget m q) := by
  classical
  let I := finiteTightInstance m
  let a := finiteTightQueryTarget m q
  have hdelta : 0 < 1 / ((m + 1 : ℕ) : ℝ) := by positivity
  have ha_eq : a = finiteTightQueryTarget m q := rfl
  have ha_active : a.val < n :=
    (hactive a).mp (finiteTightQueryTarget_eligible m q)
  have hspend_a : I.spend A a = c := by
    rw [hspend a ha_active]
    simp [ha_eq]
  have hbid_a : I.bid a q = 1 / ((m + 1 : ℕ) : ℝ) := by
    simpa [I, a] using finiteTightInstance_target_bid m q
  have hbudget_a : I.budget a = 1 := by rfl
  refine ⟨?_, ?_⟩
  · unfold AdWordsInstance.CanAssign
    rw [hspend_a, hbid_a, hbudget_a]
    exact hcstep
  · intro b _hcan
    by_cases hb_active : b.val < n
    · by_cases hb_before : b.val < a.val
      · have hspend_b : I.spend A b = c + 1 / ((m + 1 : ℕ) : ℝ) := by
          rw [hspend b hb_active, if_pos hb_before]
        have hbid_b : I.bid b q = 1 / ((m + 1 : ℕ) : ℝ) := by
          change (if finiteTightEligible m b q then _ else _) = _
          rw [if_pos ((hactive b).mpr hb_active)]
        have hbudget_b : I.budget b = 1 := by rfl
        have hfrac_a : I.spentFraction A a = c := by
          unfold AdWordsInstance.spentFraction
          rw [hspend_a, hbudget_a, div_one]
        have hfrac_b : I.spentFraction A b = c + 1 / ((m + 1 : ℕ) : ℝ) := by
          unfold AdWordsInstance.spentFraction
          rw [hspend_b, hbudget_b, div_one]
        have hdisc : AdWordsInstance.balanceDiscount (I.spentFraction A b) <
            AdWordsInstance.balanceDiscount (I.spentFraction A a) := by
          rw [hfrac_a, hfrac_b]
          exact AdWordsInstance.balanceDiscount_strictAnti (by linarith)
        unfold AdWordsInstance.balanceScore
        rw [hbid_b, hbid_a]
        exact le_of_lt (mul_lt_mul_of_pos_left hdisc hdelta)
      · have hspend_b : I.spend A b = c := by
          rw [hspend b hb_active, if_neg hb_before]
        have hbid_b : I.bid b q = 1 / ((m + 1 : ℕ) : ℝ) := by
          change (if finiteTightEligible m b q then _ else _) = _
          rw [if_pos ((hactive b).mpr hb_active)]
        have hbudget_b : I.budget b = 1 := by rfl
        have hfrac_a : I.spentFraction A a = c := by
          unfold AdWordsInstance.spentFraction
          rw [hspend_a, hbudget_a, div_one]
        have hfrac_b : I.spentFraction A b = c := by
          unfold AdWordsInstance.spentFraction
          rw [hspend_b, hbudget_b, div_one]
        unfold AdWordsInstance.balanceScore
        rw [hbid_b, hbid_a, hfrac_a, hfrac_b]
    · have hbid_b : I.bid b q = 0 := by
        change (if finiteTightEligible m b q then _ else _) = 0
        rw [if_neg fun hb => hb_active ((hactive b).mp hb)]
      have hfrac_a : I.spentFraction A a = c := by
        unfold AdWordsInstance.spentFraction
        rw [hspend_a, hbudget_a, div_one]
      have hscore_a_pos : 0 < I.balanceScore A a q := by
        unfold AdWordsInstance.balanceScore
        rw [hbid_a, hfrac_a]
        exact mul_pos hdelta (AdWordsInstance.balanceDiscount_pos_of_lt_one hc)
      unfold AdWordsInstance.balanceScore
      rw [hbid_b]
      rw [show (finiteTightInstance m).bid (finiteTightQueryTarget m q) q =
          1 / ((m + 1 : ℕ) : ℝ) by exact finiteTightInstance_target_bid m q]
      rw [show (finiteTightInstance m).spentFraction A (finiteTightQueryTarget m q) = c by
        simpa [I, a] using hfrac_a]
      simpa using (le_of_lt (mul_pos hdelta
        (AdWordsInstance.balanceDiscount_pos_of_lt_one hc)))

/-- A fixed deterministic Balance tie rule that gives the displayed target
priority whenever that target is a scaled-bid maximizer. -/
noncomputable def finiteTightBalanceRule (m : ℕ) :
    AdWordsInstance.ChoiceRule (FiniteTightAdvertiser m) (FiniteTightQuery m) := by
  classical
  exact fun A q =>
    if h : (finiteTightInstance m).IsBalanceChoice A q
        (finiteTightQueryTarget m q) then
      some (finiteTightQueryTarget m q)
    else
      (finiteTightInstance m).balanceChoiceRule A q

theorem finiteTightBalanceRule_isBalanceChoice_of_eq_some
    (m : ℕ) (A : AdWordsInstance.Assignment
      (FiniteTightAdvertiser m) (FiniteTightQuery m))
    (q : FiniteTightQuery m) (a : FiniteTightAdvertiser m)
    (hchoice : finiteTightBalanceRule m A q = some a) :
    (finiteTightInstance m).IsBalanceChoice A q a := by
  classical
  by_cases htarget : (finiteTightInstance m).IsBalanceChoice A q
      (finiteTightQueryTarget m q)
  · have htarget_eq : a = finiteTightQueryTarget m q := by
      symm
      simpa [finiteTightBalanceRule, htarget] using hchoice
    simpa [htarget_eq] using htarget
  · have hcanonical : (finiteTightInstance m).balanceChoiceRule A q = some a := by
      simpa [finiteTightBalanceRule, htarget] using hchoice
    exact (finiteTightInstance m).balanceChoiceRule_isBalanceChoice_of_eq_some
      A q a hcanonical

theorem finiteTightBalanceRule_feasible (m : ℕ) :
    (finiteTightInstance m).ChoiceRuleFeasible (finiteTightBalanceRule m) := by
  intro A q a hchoice
  exact (finiteTightBalanceRule_isBalanceChoice_of_eq_some m A q a hchoice).1

theorem finiteTightBalanceRule_eq_target_of_isBalanceChoice
    (m : ℕ) (A : AdWordsInstance.Assignment
      (FiniteTightAdvertiser m) (FiniteTightQuery m))
    (q : FiniteTightQuery m)
    (hchoice : (finiteTightInstance m).IsBalanceChoice A q
      (finiteTightQueryTarget m q)) :
    finiteTightBalanceRule m A q = some (finiteTightQueryTarget m q) := by
  classical
  simp [finiteTightBalanceRule, hchoice]

/-- In a stage whose already-served targets carry one extra bid, the next
target is a strict Balance maximizer among the active cohort. -/
theorem finiteTight_stage_target_isBalance
    (m : ℕ) (stage : Fin m) (target : Fin (finiteTightActiveCount m stage))
    (A : AdWordsInstance.Assignment (FiniteTightAdvertiser m) (FiniteTightQuery m))
    (c : ℝ)
    (hc : c < 1)
    (hcstep : c + 1 / ((m + 1 : ℕ) : ℝ) ≤ 1)
    (hspend : ∀ b : FiniteTightAdvertiser m,
      b.val < finiteTightActiveCount m stage →
        (finiteTightInstance m).spend A b =
          if b.val < target.val then c + 1 / ((m + 1 : ℕ) : ℝ) else c) :
    (finiteTightInstance m).IsBalanceChoice A (.stage stage target)
      (finiteTightQueryTarget m (.stage stage target)) := by
  classical
  let I := finiteTightInstance m
  let q : FiniteTightQuery m := .stage stage target
  let a := finiteTightQueryTarget m q
  have hdelta : 0 < 1 / ((m + 1 : ℕ) : ℝ) := by positivity
  have ha_val : a.val = target.val := by rfl
  have ha_active : a.val < finiteTightActiveCount m stage := by
    simpa [ha_val] using target.isLt
  have hspend_a : I.spend A a = c := by
    rw [hspend a ha_active]
    simp [ha_val]
  have hbid_a : I.bid a q = 1 / ((m + 1 : ℕ) : ℝ) := by
    simpa [I, q, a] using finiteTightInstance_target_bid m q
  have hbudget_a : I.budget a = 1 := by rfl
  refine ⟨?_, ?_⟩
  · unfold AdWordsInstance.CanAssign
    rw [hspend_a, hbid_a, hbudget_a]
    exact hcstep
  · intro b _hcan
    by_cases hb_active : b.val < finiteTightActiveCount m stage
    · by_cases hb_before : b.val < target.val
      · have hspend_b : I.spend A b = c + 1 / ((m + 1 : ℕ) : ℝ) := by
          rw [hspend b hb_active, if_pos hb_before]
        have hbid_b : I.bid b q = 1 / ((m + 1 : ℕ) : ℝ) := by
          simpa [I, q, finiteTightInstance, finiteTightEligible, hb_active]
        have hbudget_b : I.budget b = 1 := by rfl
        have hfrac_a : I.spentFraction A a = c := by
          unfold AdWordsInstance.spentFraction
          rw [hspend_a, hbudget_a, div_one]
        have hfrac_b : I.spentFraction A b = c + 1 / ((m + 1 : ℕ) : ℝ) := by
          unfold AdWordsInstance.spentFraction
          rw [hspend_b, hbudget_b, div_one]
        have hdisc : AdWordsInstance.balanceDiscount (I.spentFraction A b) <
            AdWordsInstance.balanceDiscount (I.spentFraction A a) := by
          rw [hfrac_a, hfrac_b]
          exact AdWordsInstance.balanceDiscount_strictAnti (by linarith)
        unfold AdWordsInstance.balanceScore
        rw [hbid_b, hbid_a]
        exact le_of_lt (mul_lt_mul_of_pos_left hdisc hdelta)
      · have hspend_b : I.spend A b = c := by
          rw [hspend b hb_active, if_neg hb_before]
        have hbid_b : I.bid b q = 1 / ((m + 1 : ℕ) : ℝ) := by
          simpa [I, q, finiteTightInstance, finiteTightEligible, hb_active]
        have hbudget_b : I.budget b = 1 := by rfl
        have hfrac_a : I.spentFraction A a = c := by
          unfold AdWordsInstance.spentFraction
          rw [hspend_a, hbudget_a, div_one]
        have hfrac_b : I.spentFraction A b = c := by
          unfold AdWordsInstance.spentFraction
          rw [hspend_b, hbudget_b, div_one]
        unfold AdWordsInstance.balanceScore
        rw [hbid_b, hbid_a, hfrac_a, hfrac_b]
    · have hbid_b : I.bid b q = 0 := by
        simpa [I, q, finiteTightInstance, finiteTightEligible, hb_active]
      have hfrac_a : I.spentFraction A a = c := by
        unfold AdWordsInstance.spentFraction
        rw [hspend_a, hbudget_a, div_one]
      have hscore_a_pos : 0 < I.balanceScore A a q := by
        unfold AdWordsInstance.balanceScore
        rw [hbid_a, hfrac_a]
        exact mul_pos hdelta (AdWordsInstance.balanceDiscount_pos_of_lt_one hc)
      unfold AdWordsInstance.balanceScore
      rw [hbid_b]
      rw [show (finiteTightInstance m).bid
          (finiteTightQueryTarget m (.stage stage target)) (.stage stage target) =
          1 / ((m + 1 : ℕ) : ℝ) by
        exact finiteTightInstance_target_bid m (.stage stage target)]
      rw [show (finiteTightInstance m).spentFraction A
          (finiteTightQueryTarget m (.stage stage target)) = c by
        simpa [I, q, a] using hfrac_a]
      simpa using (le_of_lt (mul_pos hdelta
        (AdWordsInstance.balanceDiscount_pos_of_lt_one hc)))

/-- The fixed tie rule makes the certified stage choice in the actual runner. -/
theorem finiteTight_stage_step_eq_assignQuery
    (m : ℕ) (stage : Fin m) (target : Fin (finiteTightActiveCount m stage))
    (S : AdWordsInstance.HistoryState (FiniteTightAdvertiser m) (FiniteTightQuery m))
    (c : ℝ)
    (hc : c < 1)
    (hcstep : c + 1 / ((m + 1 : ℕ) : ℝ) ≤ 1)
    (hspend : ∀ b : FiniteTightAdvertiser m,
      b.val < finiteTightActiveCount m stage →
        (finiteTightInstance m).spend S.assignment b =
          if b.val < target.val then c + 1 / ((m + 1 : ℕ) : ℝ) else c)
    (hnew : FiniteTightQuery.stage stage target ∉ S.seen) :
    AdWordsInstance.stepHistoryState (finiteTightInstance m)
      (finiteTightBalanceRule m) S (.stage stage target) =
      { assignment := AdWordsInstance.assignQuery S.assignment
          (.stage stage target) (finiteTightQueryTarget m (.stage stage target))
        seen := insert (.stage stage target) S.seen } := by
  classical
  have hchoice := finiteTightBalanceRule_eq_target_of_isBalanceChoice m S.assignment
    (.stage stage target) (finiteTight_stage_target_isBalance m stage target
      S.assignment c hc hcstep hspend)
  simp [AdWordsInstance.stepHistoryState, hnew, hchoice]

/-- The first `r` stage queries, in the fixed priority order used by the
finite tightness construction. -/
def finiteTightStageHistory (m : ℕ) (stage : Fin m) :
    ∀ r : ℕ, r ≤ finiteTightActiveCount m stage → List (FiniteTightQuery m)
  | 0, _ => []
  | r + 1, hr =>
      finiteTightStageHistory m stage r (Nat.le_of_succ_le hr) ++
        [.stage stage ⟨r, Nat.lt_of_lt_of_le (Nat.lt_succ_self r) hr⟩]

theorem finiteTightStageHistory_not_mem
    (m : ℕ) (stage : Fin m) (r : ℕ)
    (hr : r ≤ finiteTightActiveCount m stage)
    (target : Fin (finiteTightActiveCount m stage))
    (hfuture : r ≤ target.val) :
    FiniteTightQuery.stage stage target ∉
      finiteTightStageHistory m stage r hr := by
  induction r with
  | zero => simp [finiteTightStageHistory]
  | succ r ih =>
      rw [finiteTightStageHistory]
      simp only [List.mem_append, List.mem_singleton, not_or]
      constructor
      · exact ih (Nat.le_of_succ_le hr) (by omega)
      · intro h
        have heq : target.val = r := by
          simpa using congrArg (fun q : FiniteTightQuery m =>
            match q with
            | .stage _ t => t.val
            | .final _ => 0
            | .reserve _ _ => 0) h
        omega

/-- Running a whole stage raises every active bidder by precisely one bid. -/
theorem finiteTight_runStage_spend
    (m : ℕ) (stage : Fin m)
    (S : AdWordsInstance.HistoryState (FiniteTightAdvertiser m) (FiniteTightQuery m))
    (c : ℝ)
    (hc : c < 1)
    (hcstep : c + 1 / ((m + 1 : ℕ) : ℝ) ≤ 1)
    (hstate : (finiteTightInstance m).StateInvariant S)
    (hfresh : ∀ target : Fin (finiteTightActiveCount m stage),
      FiniteTightQuery.stage stage target ∉ S.seen)
    (hbase : ∀ b : FiniteTightAdvertiser m,
      b.val < finiteTightActiveCount m stage →
        (finiteTightInstance m).spend S.assignment b = c) :
    ∀ (r : ℕ) (hr : r ≤ finiteTightActiveCount m stage)
      (b : FiniteTightAdvertiser m),
      b.val < finiteTightActiveCount m stage →
        (finiteTightInstance m).spend
          (AdWordsInstance.runHistoryStateFrom (finiteTightInstance m)
            (finiteTightBalanceRule m) S
            (finiteTightStageHistory m stage r hr)).assignment b =
          if b.val < r then c + 1 / ((m + 1 : ℕ) : ℝ) else c := by
  intro r
  induction r with
  | zero =>
      intro hr b hb
      simpa [finiteTightStageHistory, AdWordsInstance.runHistoryStateFrom]
        using hbase b hb
  | succ r ih =>
      intro hr b hb
      let I := finiteTightInstance m
      let H := finiteTightStageHistory m stage r (Nat.le_of_succ_le hr)
      let T := AdWordsInstance.runHistoryStateFrom I (finiteTightBalanceRule m) S H
      let q : FiniteTightQuery m := .stage stage
        ⟨r, Nat.lt_of_lt_of_le (Nat.lt_succ_self r) hr⟩
      have hTspend : ∀ a : FiniteTightAdvertiser m,
          a.val < finiteTightActiveCount m stage →
            I.spend T.assignment a =
              if a.val < r then c + 1 / ((m + 1 : ℕ) : ℝ) else c := by
        intro a ha
        simpa [I, H, T] using ih (Nat.le_of_succ_le hr) a ha
      have hTstate : I.StateInvariant T := by
        dsimp [T]
        exact AdWordsInstance.runHistoryStateFrom_invariant I
          (finiteTightBalanceRule m) (finiteTightBalanceRule_feasible m) H S hstate
      have hq_not_H : q ∉ AdWordsInstance.historyFinset H := by
        intro hmem
        apply finiteTightStageHistory_not_mem m stage r
          (Nat.le_of_succ_le hr) ⟨r, Nat.lt_of_lt_of_le (Nat.lt_succ_self r) hr⟩ le_rfl
        exact AdWordsInstance.mem_historyFinset.mp hmem
      have hq_not_S : q ∉ S.seen := by
        dsimp [q]
        exact hfresh _
      have hq_new : q ∉ T.seen := by
        rw [show T.seen = AdWordsInstance.historyFinset H ∪ S.seen by
          dsimp [T]
          exact AdWordsInstance.runHistoryStateFrom_seen I
            (finiteTightBalanceRule m) H S]
        simp [hq_not_H, hq_not_S]
      have hchoiceState := finiteTight_stage_step_eq_assignQuery m stage
        ⟨r, Nat.lt_of_lt_of_le (Nat.lt_succ_self r) hr⟩ T c hc hcstep hTspend hq_new
      have hrun :
          AdWordsInstance.runHistoryStateFrom I (finiteTightBalanceRule m) S
            (finiteTightStageHistory m stage (r + 1) hr) =
            AdWordsInstance.stepHistoryState I (finiteTightBalanceRule m) T q := by
        rw [finiteTightStageHistory,
          AdWordsInstance.runHistoryStateFrom_append]
        simp [AdWordsInstance.runHistoryStateFrom, I, H, T, q]
      rw [hrun, hchoiceState]
      have hq_unassigned : T.assignment q = none := hTstate.2 q hq_new
      by_cases hb_eq : b.val = r
      · have hb_target : b = finiteTightQueryTarget m q := by
          apply Fin.ext
          simpa [q] using hb_eq
        subst b
        rw [AdWordsInstance.spend_assignQuery_self_of_unassigned I T.assignment q
          (finiteTightQueryTarget m q) hq_unassigned]
        have htarget_active : (finiteTightQueryTarget m q).val <
            finiteTightActiveCount m stage := by
          simpa [q] using (Nat.lt_of_lt_of_le (Nat.lt_succ_self r) hr)
        have hbidq : I.bid (finiteTightQueryTarget m q) q =
            1 / ((m + 1 : ℕ) : ℝ) := by
          simpa [I] using finiteTightInstance_target_bid m q
        rw [hTspend _ htarget_active, hbidq]
        have htarget_val : (finiteTightQueryTarget m q).val = r := by rfl
        simp [htarget_val]
      · have hb_ne_target : b ≠ finiteTightQueryTarget m q := by
          intro heq
          apply hb_eq
          simpa [q] using congrArg Fin.val heq
        rw [AdWordsInstance.spend_assignQuery_other_of_unassigned I T.assignment q
          hq_unassigned hb_ne_target]
        rw [hTspend b hb]
        have hlt : (b.val < r + 1) ↔ b.val < r := by omega
        simp [hlt]

/-- The concrete runner earns one bid for each query in a stage. -/
theorem finiteTight_runStage_revenue
    (m : ℕ) (stage : Fin m)
    (S : AdWordsInstance.HistoryState (FiniteTightAdvertiser m) (FiniteTightQuery m))
    (c : ℝ)
    (hc : c < 1)
    (hcstep : c + 1 / ((m + 1 : ℕ) : ℝ) ≤ 1)
    (hstate : (finiteTightInstance m).StateInvariant S)
    (hfresh : ∀ target : Fin (finiteTightActiveCount m stage),
      FiniteTightQuery.stage stage target ∉ S.seen)
    (hbase : ∀ b : FiniteTightAdvertiser m,
      b.val < finiteTightActiveCount m stage →
        (finiteTightInstance m).spend S.assignment b = c) :
    ∀ (r : ℕ) (hr : r ≤ finiteTightActiveCount m stage),
      (finiteTightInstance m).revenue
        (AdWordsInstance.runHistoryStateFrom (finiteTightInstance m)
          (finiteTightBalanceRule m) S
          (finiteTightStageHistory m stage r hr)).assignment =
        (finiteTightInstance m).revenue S.assignment +
          (r : ℝ) * (1 / ((m + 1 : ℕ) : ℝ)) := by
  intro r
  induction r with
  | zero =>
      intro hr
      simp [finiteTightStageHistory, AdWordsInstance.runHistoryStateFrom]
  | succ r ih =>
      intro hr
      let I := finiteTightInstance m
      let H := finiteTightStageHistory m stage r (Nat.le_of_succ_le hr)
      let T := AdWordsInstance.runHistoryStateFrom I (finiteTightBalanceRule m) S H
      let q : FiniteTightQuery m := .stage stage
        ⟨r, Nat.lt_of_lt_of_le (Nat.lt_succ_self r) hr⟩
      have hTspend : ∀ a : FiniteTightAdvertiser m,
          a.val < finiteTightActiveCount m stage →
            I.spend T.assignment a =
              if a.val < r then c + 1 / ((m + 1 : ℕ) : ℝ) else c := by
        intro a ha
        simpa [I, H, T] using finiteTight_runStage_spend m stage S c hc hcstep
          hstate hfresh hbase r (Nat.le_of_succ_le hr) a ha
      have hTstate : I.StateInvariant T := by
        dsimp [T]
        exact AdWordsInstance.runHistoryStateFrom_invariant I
          (finiteTightBalanceRule m) (finiteTightBalanceRule_feasible m) H S hstate
      have hq_not_H : q ∉ AdWordsInstance.historyFinset H := by
        intro hmem
        apply finiteTightStageHistory_not_mem m stage r
          (Nat.le_of_succ_le hr) ⟨r, Nat.lt_of_lt_of_le (Nat.lt_succ_self r) hr⟩ le_rfl
        exact AdWordsInstance.mem_historyFinset.mp hmem
      have hq_not_S : q ∉ S.seen := by
        dsimp [q]
        exact hfresh _
      have hq_new : q ∉ T.seen := by
        rw [show T.seen = AdWordsInstance.historyFinset H ∪ S.seen by
          dsimp [T]
          exact AdWordsInstance.runHistoryStateFrom_seen I
            (finiteTightBalanceRule m) H S]
        simp [hq_not_H, hq_not_S]
      have hchoiceState := finiteTight_stage_step_eq_assignQuery m stage
        ⟨r, Nat.lt_of_lt_of_le (Nat.lt_succ_self r) hr⟩ T c hc hcstep hTspend hq_new
      have hrun :
          AdWordsInstance.runHistoryStateFrom I (finiteTightBalanceRule m) S
            (finiteTightStageHistory m stage (r + 1) hr) =
            AdWordsInstance.stepHistoryState I (finiteTightBalanceRule m) T q := by
        rw [finiteTightStageHistory,
          AdWordsInstance.runHistoryStateFrom_append]
        simp [AdWordsInstance.runHistoryStateFrom, I, H, T, q]
      rw [hrun, hchoiceState]
      have hq_unassigned : T.assignment q = none := hTstate.2 q hq_new
      rw [AdWordsInstance.revenue_assignQuery_of_unassigned I T.assignment q
        (finiteTightQueryTarget m q) hq_unassigned]
      have hbidq : I.bid (finiteTightQueryTarget m q) q =
          1 / ((m + 1 : ℕ) : ℝ) := by
        simpa [I] using finiteTightInstance_target_bid m q
      rw [hbidq]
      have hprefix := ih (Nat.le_of_succ_le hr)
      change I.revenue T.assignment + 1 / ((m + 1 : ℕ) : ℝ) = _
      rw [show I.revenue T.assignment = I.revenue S.assignment +
          (r : ℝ) * (1 / ((m + 1 : ℕ) : ℝ)) by
        simpa [I, H, T] using hprefix]
      rw [Nat.cast_add]
      norm_num
      ring

/-- The first `s` preterminal stages in the nested-cohort construction. -/
def finiteTightPreterminalHistory (m : ℕ) :
    ∀ s : ℕ, s ≤ m → List (FiniteTightQuery m)
  | 0, _ => []
  | s + 1, hs =>
      finiteTightPreterminalHistory m s (Nat.le_of_succ_le hs) ++
        finiteTightStageHistory m ⟨s, Nat.lt_of_lt_of_le (Nat.lt_succ_self s) hs⟩
          (finiteTightActiveCount m s) le_rfl

theorem finiteTightStageHistory_mem_same_stage
    (m : ℕ) (stage : Fin m) (r : ℕ)
    (hr : r ≤ finiteTightActiveCount m stage)
    (q : FiniteTightQuery m)
    (hmem : q ∈ finiteTightStageHistory m stage r hr) :
    ∃ target : Fin (finiteTightActiveCount m stage),
      q = .stage stage target := by
  induction r with
  | zero => simp [finiteTightStageHistory] at hmem
  | succ r ih =>
      rw [finiteTightStageHistory] at hmem
      rcases List.mem_append.mp hmem with hmem | hmem
      · exact ih (Nat.le_of_succ_le hr) hmem
      · rw [List.mem_singleton.mp hmem]
        exact ⟨⟨r, Nat.lt_of_lt_of_le (Nat.lt_succ_self r) hr⟩, rfl⟩

theorem finiteTightPreterminalHistory_not_mem
    (m : ℕ) (r s : ℕ) (hr : r ≤ m) (hs : s < m) (hfuture : r ≤ s)
    (target : Fin (finiteTightActiveCount m s)) :
    .stage ⟨s, hs⟩ target ∉ finiteTightPreterminalHistory m r hr := by
  induction r with
  | zero => simp [finiteTightPreterminalHistory]
  | succ r ih =>
      rw [finiteTightPreterminalHistory]
      simp only [List.mem_append, not_or]
      constructor
      · exact ih (Nat.le_of_succ_le hr) (by omega)
      · intro hmem
        obtain ⟨other, heq⟩ := finiteTightStageHistory_mem_same_stage m
          ⟨r, Nat.lt_of_lt_of_le (Nat.lt_succ_self r) hr⟩
          (finiteTightActiveCount m r) le_rfl _ hmem
        have hstage : r = s := by
          have hcomponent := congrArg (fun q : FiniteTightQuery m =>
            match q with
            | .stage stage _ => stage.val
            | .final _ => 0
            | .reserve _ _ => 0) heq
          simpa using hcomponent.symm
        omega

theorem finiteTightActiveCount_succ_le (m s : ℕ) (hs : s < m) :
    finiteTightActiveCount m (s + 1) ≤ finiteTightActiveCount m s := by
  unfold finiteTightActiveCount
  have hsub : m - s = (m - (s + 1)) + 1 := by omega
  rw [hsub, pow_succ, pow_succ]
  calc
    (m + 1) ^ (m - (s + 1)) * (m ^ s * m) ≤
        (m + 1) ^ (m - (s + 1)) * (m ^ s * (m + 1)) := by
      apply Nat.mul_le_mul_left
      exact Nat.mul_le_mul_left _ (by omega)
    _ = ((m + 1) ^ (m - (s + 1)) * (m + 1)) * m ^ s := by ring

/-- The nested active cohorts are antitone over the stages that occur in the
finite construction. -/
theorem finiteTightActiveCount_antitone
    (m i j : ℕ) (hij : i ≤ j) (hj : j ≤ m) :
    finiteTightActiveCount m j ≤ finiteTightActiveCount m i := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
      exact (finiteTightActiveCount_succ_le m j (by omega)).trans (ih (by omega))

/-- A bidder cohort is either the portion that leaves after one preterminal
stage, or a bidder who remains active through the final stage. -/
abbrev FiniteTightDeparture (m : ℕ) :=
  Sigma fun stage : Fin m => Fin (finiteTightDepartingCount m stage)

abbrev FiniteTightCohort (m : ℕ) :=
  FiniteTightDeparture m ⊕ Fin (finiteTightActiveCount m m)

theorem finiteTight_departing_sum (m : ℕ) :
    (∑ i ∈ Finset.range m, finiteTightDepartingCount m i) +
      finiteTightActiveCount m m = (m + 1) ^ m := by
  have htel : ∀ r : ℕ, r ≤ m →
      (∑ i ∈ Finset.range r,
        (finiteTightActiveCount m i - finiteTightActiveCount m (i + 1))) +
          finiteTightActiveCount m r = finiteTightActiveCount m 0 := by
    intro r hr
    induction r with
    | zero => simp
    | succ r ih =>
        have hrm : r < m := by omega
        have hprev := ih (by omega)
        have hle := finiteTightActiveCount_succ_le m r hrm
        rw [Finset.sum_range_succ]
        omega
  rw [show (∑ i ∈ Finset.range m, finiteTightDepartingCount m i) =
      ∑ i ∈ Finset.range m,
        (finiteTightActiveCount m i - finiteTightActiveCount m (i + 1)) by
    apply Finset.sum_congr rfl
    intro i hi
    rw [finiteTightActiveCount_sub_succ m i (Finset.mem_range.mp hi)]]
  rw [htel m le_rfl]
  simp [finiteTightActiveCount]

/-- The concrete position of a departing or surviving cohort member in the
original bidder population. -/
def finiteTightCohortEmbed (m : ℕ) :
    FiniteTightCohort m → FiniteTightAdvertiser m
  | .inl ⟨stage, departure⟩ =>
      ⟨finiteTightActiveCount m (stage.val + 1) + departure.val, by
        have hstage : stage.val < m := stage.isLt
        have hdeparture : departure.val <
            finiteTightActiveCount m stage.val -
              finiteTightActiveCount m (stage.val + 1) := by
          rw [finiteTightActiveCount_sub_succ m stage.val hstage]
          exact departure.isLt
        have hlt : finiteTightActiveCount m (stage.val + 1) + departure.val <
            finiteTightActiveCount m stage.val := by
          rw [← Nat.add_sub_of_le (finiteTightActiveCount_succ_le m stage.val hstage)]
          exact Nat.add_lt_add_left hdeparture _
        exact lt_of_lt_of_le hlt
          (finiteTightActiveCount_le_population m stage.val stage.isLt.le)⟩
  | .inr survivor => finiteTightEmbedActive m m le_rfl survivor

theorem finiteTightCohortEmbed_injective (m : ℕ) :
    Function.Injective (finiteTightCohortEmbed m) := by
  intro x y hxy
  cases x with
  | inl x =>
      cases y with
      | inl y =>
          obtain ⟨stage, departure⟩ := x
          obtain ⟨stage', departure'⟩ := y
          have hval : finiteTightActiveCount m (stage.val + 1) + departure.val =
              finiteTightActiveCount m (stage'.val + 1) + departure'.val :=
            congrArg Fin.val hxy
          have hstage_eq : stage = stage' := by
            apply Fin.ext
            by_contra hne
            rcases lt_or_gt_of_ne hne with hlt | hgt
            · have hboundleft : finiteTightActiveCount m stage'.val ≤
                finiteTightActiveCount m (stage.val + 1) := by
                apply finiteTightActiveCount_antitone m (stage.val + 1) stage'.val
                · omega
                · exact stage'.isLt.le
              have hlt_right : finiteTightActiveCount m (stage'.val + 1) + departure'.val <
                  finiteTightActiveCount m (stage'.val + 1) +
                    finiteTightDepartingCount m stage'.val := by
                exact Nat.add_lt_add_left departure'.isLt _
              have heq_right : finiteTightActiveCount m (stage'.val + 1) +
                    finiteTightDepartingCount m stage'.val =
                  finiteTightActiveCount m stage'.val := by
                rw [← finiteTightActiveCount_sub_succ m stage'.val stage'.isLt]
                exact Nat.add_sub_of_le (finiteTightActiveCount_succ_le m stage'.val stage'.isLt)
              have hright : finiteTightActiveCount m (stage'.val + 1) + departure'.val <
                  finiteTightActiveCount m (stage.val + 1) := by
                rw [heq_right] at hlt_right
                exact hlt_right.trans_le hboundleft
              have hleft : finiteTightActiveCount m (stage.val + 1) ≤
                  finiteTightActiveCount m (stage.val + 1) + departure.val := by omega
              omega
            · have hboundright : finiteTightActiveCount m stage.val ≤
                finiteTightActiveCount m (stage'.val + 1) := by
                apply finiteTightActiveCount_antitone m (stage'.val + 1) stage.val
                · omega
                · exact stage.isLt.le
              have hlt_left : finiteTightActiveCount m (stage.val + 1) + departure.val <
                  finiteTightActiveCount m (stage.val + 1) +
                    finiteTightDepartingCount m stage.val := by
                exact Nat.add_lt_add_left departure.isLt _
              have heq_left : finiteTightActiveCount m (stage.val + 1) +
                    finiteTightDepartingCount m stage.val =
                  finiteTightActiveCount m stage.val := by
                rw [← finiteTightActiveCount_sub_succ m stage.val stage.isLt]
                exact Nat.add_sub_of_le (finiteTightActiveCount_succ_le m stage.val stage.isLt)
              have hleft : finiteTightActiveCount m (stage.val + 1) + departure.val <
                  finiteTightActiveCount m (stage'.val + 1) := by
                rw [heq_left] at hlt_left
                exact hlt_left.trans_le hboundright
              have hright : finiteTightActiveCount m (stage'.val + 1) ≤
                  finiteTightActiveCount m (stage'.val + 1) + departure'.val := by omega
              omega
          subst stage'
          have hdeparture : departure = departure' := by
            apply Fin.ext
            simpa using hval
          subst departure'
          rfl
      | inr survivor =>
          obtain ⟨stage, departure⟩ := x
          have hleft : finiteTightActiveCount m (stage.val + 1) ≤
              finiteTightActiveCount m (stage.val + 1) + departure.val := by omega
          have hbound : finiteTightActiveCount m m ≤
              finiteTightActiveCount m (stage.val + 1) := by
            apply finiteTightActiveCount_antitone m (stage.val + 1) m
            · omega
            · omega
          have hright : (finiteTightEmbedActive m m le_rfl survivor).val <
              finiteTightActiveCount m m := survivor.isLt
          have hval : finiteTightActiveCount m (stage.val + 1) + departure.val =
              (finiteTightEmbedActive m m le_rfl survivor).val := by
            simpa [finiteTightCohortEmbed] using congrArg Fin.val hxy
          have : False := by omega
          exact this.elim
  | inr survivor =>
      cases y with
      | inl y =>
          obtain ⟨stage, departure⟩ := y
          have hleft : finiteTightActiveCount m (stage.val + 1) ≤
              finiteTightActiveCount m (stage.val + 1) + departure.val := by omega
          have hbound : finiteTightActiveCount m m ≤
              finiteTightActiveCount m (stage.val + 1) := by
            apply finiteTightActiveCount_antitone m (stage.val + 1) m
            · omega
            · omega
          have hright : (finiteTightEmbedActive m m le_rfl survivor).val <
              finiteTightActiveCount m m := survivor.isLt
          have hval : (finiteTightEmbedActive m m le_rfl survivor).val =
              finiteTightActiveCount m (stage.val + 1) + departure.val := by
            simpa [finiteTightCohortEmbed] using congrArg Fin.val hxy
          have : False := by omega
          exact this.elim
      | inr survivor' =>
          have hval : survivor.val = survivor'.val := by
            simpa [finiteTightCohortEmbed, finiteTightEmbedActive] using congrArg Fin.val hxy
          exact congrArg Sum.inr (Fin.ext hval)

theorem finiteTightCohort_card (m : ℕ) :
    Fintype.card (FiniteTightCohort m) = Fintype.card (FiniteTightAdvertiser m) := by
  simp only [Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range]
  exact finiteTight_departing_sum m

/-- The departing cohorts and final survivors partition the initial bidder
population. -/
noncomputable def finiteTightCohortEquiv (m : ℕ) :
    FiniteTightCohort m ≃ FiniteTightAdvertiser m :=
  Equiv.ofBijective (finiteTightCohortEmbed m)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨finiteTightCohortEmbed_injective m, finiteTightCohort_card m⟩)

/-- The slots in one preterminal stage split into a departure-cohort member
and one of that member's `m + 1` queries. -/
def finiteTightStageSlotEquiv (m : ℕ) (stage : Fin m) :
    Fin (finiteTightActiveCount m stage) ≃
      Fin (finiteTightDepartingCount m stage) × Fin (m + 1) :=
  (Equiv.cast (congrArg Fin
    (finiteTightDepartingCount_mul_width m stage stage.isLt).symm)).trans
      finProdFinEquiv.symm

/-- Every query is paired with a unique bidder cohort member and one of that
member's `m + 1` offline slots. -/
noncomputable def finiteTightQueryCohortSlotEquiv (m : ℕ) :
    FiniteTightQuery m ≃ FiniteTightCohort m × Fin (m + 1) where
  toFun
    | .stage stage target =>
        let slot := finiteTightStageSlotEquiv m stage target
        (.inl ⟨stage, slot.1⟩, slot.2)
    | .final survivor => (.inr survivor, 0)
    | .reserve survivor copy => (.inr survivor, copy.succ)
  invFun
    | (.inl ⟨stage, departure⟩, copy) =>
        .stage stage ((finiteTightStageSlotEquiv m stage).symm (departure, copy))
    | (.inr survivor, copy) =>
        Fin.cases (.final survivor) (fun reserveCopy => .reserve survivor reserveCopy) copy
  left_inv q := by
    cases q with
    | stage stage target =>
        simp only
        rw [Equiv.symm_apply_apply]
    | final survivor => simp
    | reserve survivor copy => simp
  right_inv x := by
    rcases x with ⟨cohort, copy⟩
    cases cohort with
    | inl departure =>
        obtain ⟨stage, departure⟩ := departure
        simp only
        rw [Equiv.apply_symm_apply]
    | inr survivor =>
        refine Fin.cases ?_ (fun copy => ?_) copy
        · simp
        · simp

/-- Query slots reindexed directly by their offline owner in the original
bidder population. -/
noncomputable def finiteTightQuerySlotEquiv (m : ℕ) :
    FiniteTightQuery m ≃ FiniteTightAdvertiser m × Fin (m + 1) :=
  (finiteTightQueryCohortSlotEquiv m).trans
    (Equiv.prodCongr (finiteTightCohortEquiv m) (Equiv.refl _))

theorem finiteTightQuerySlot_owner_eligible
    (m : ℕ) (q : FiniteTightQuery m) :
    finiteTightEligible m ((finiteTightQuerySlotEquiv m q).1) q := by
  cases q with
  | stage stage target =>
      change (finiteTightCohortEmbed m (.inl ⟨stage,
        (finiteTightStageSlotEquiv m stage target).1⟩)).val <
          finiteTightActiveCount m stage
      change finiteTightActiveCount m (stage.val + 1) +
          (finiteTightStageSlotEquiv m stage target).1.val <
            finiteTightActiveCount m stage.val
      have hdeparture : (finiteTightStageSlotEquiv m stage target).1.val <
          finiteTightActiveCount m stage.val -
            finiteTightActiveCount m (stage.val + 1) := by
        calc
          (finiteTightStageSlotEquiv m stage target).1.val <
              finiteTightDepartingCount m stage.val :=
            (finiteTightStageSlotEquiv m stage target).1.isLt
          _ = finiteTightActiveCount m stage.val -
              finiteTightActiveCount m (stage.val + 1) :=
            (finiteTightActiveCount_sub_succ m stage.val stage.isLt).symm
      calc
        finiteTightActiveCount m (stage.val + 1) +
            (finiteTightStageSlotEquiv m stage target).1.val <
            finiteTightActiveCount m (stage.val + 1) +
              (finiteTightActiveCount m stage.val -
                finiteTightActiveCount m (stage.val + 1)) :=
          Nat.add_lt_add_left hdeparture _
        _ = finiteTightActiveCount m stage.val :=
          Nat.add_sub_of_le (finiteTightActiveCount_succ_le m stage.val stage.isLt)
  | final survivor =>
      change (finiteTightCohortEmbed m (.inr survivor)).val <
        finiteTightActiveCount m m
      exact survivor.isLt
  | reserve survivor copy =>
      change (finiteTightCohortEmbed m (.inr survivor)).val <
        finiteTightActiveCount m m
      exact survivor.isLt

/-- The concrete offline allocation sends each query to the bidder paired with
its unique offline slot. -/
noncomputable def finiteTightOfflineAssignment (m : ℕ) :
    AdWordsInstance.Assignment (FiniteTightAdvertiser m) (FiniteTightQuery m) :=
  fun q => some (finiteTightQuerySlotEquiv m q).1

theorem finiteTightOffline_owner_bid
    (m : ℕ) (q : FiniteTightQuery m) :
    (finiteTightInstance m).bid (finiteTightQuerySlotEquiv m q).1 q =
      1 / ((m + 1 : ℕ) : ℝ) := by
  classical
  unfold finiteTightInstance
  change (if finiteTightEligible m (finiteTightQuerySlotEquiv m q).1 q then
    1 / ((m + 1 : ℕ) : ℝ) else 0) = 1 / ((m + 1 : ℕ) : ℝ)
  rw [if_pos (finiteTightQuerySlot_owner_eligible m q)]

/-- The explicit offline allocation fills every unit budget exactly. -/
theorem finiteTightOffline_spend
    (m : ℕ) (b : FiniteTightAdvertiser m) :
    (finiteTightInstance m).spend (finiteTightOfflineAssignment m) b = 1 := by
  classical
  unfold AdWordsInstance.spend finiteTightOfflineAssignment
  rw [Fintype.sum_equiv (finiteTightQuerySlotEquiv m)
    (fun q => if (finiteTightQuerySlotEquiv m q).1 = b then
      (finiteTightInstance m).bid b q else 0)
    (fun slot => if slot.1 = b then 1 / ((m + 1 : ℕ) : ℝ) else 0) (by
      intro q
      by_cases howner : (finiteTightQuerySlotEquiv m q).1 = b
      · subst b
        simp [finiteTightOffline_owner_bid]
      · simp [howner])]
  rw [Fintype.sum_prod_type]
  simp
  field_simp

/-- The actual runner reaches the geometric common spend after every
preterminal stage. -/
theorem finiteTight_preterminal_spend
    (m : ℕ) :
    ∀ (s : ℕ) (hs : s ≤ m) (b : FiniteTightAdvertiser m),
      b.val < finiteTightActiveCount m s →
        (finiteTightInstance m).spend
          (AdWordsInstance.runHistoryStateFrom (finiteTightInstance m)
            (finiteTightBalanceRule m)
            (AdWordsInstance.initialHistoryState :
              AdWordsInstance.HistoryState (FiniteTightAdvertiser m) (FiniteTightQuery m))
            (finiteTightPreterminalHistory m s hs)).assignment b =
          (s : ℝ) / ((m + 1 : ℕ) : ℝ) := by
  intro s
  induction s with
  | zero =>
      intro hs b hb
      simpa [finiteTightPreterminalHistory, AdWordsInstance.runHistoryStateFrom,
        AdWordsInstance.initialHistoryState] using
        (AdWordsInstance.spend_emptyAssignment (finiteTightInstance m) b)
  | succ s ih =>
      intro hs b hb
      let I := finiteTightInstance m
      let S0 : AdWordsInstance.HistoryState (FiniteTightAdvertiser m) (FiniteTightQuery m) :=
        AdWordsInstance.initialHistoryState
      let H := finiteTightPreterminalHistory m s (Nat.le_of_succ_le hs)
      let T := AdWordsInstance.runHistoryStateFrom I (finiteTightBalanceRule m) S0 H
      have hsm : s < m := by omega
      have hstate : I.StateInvariant T := by
        dsimp [T]
        exact AdWordsInstance.runHistoryStateFrom_invariant I
          (finiteTightBalanceRule m) (finiteTightBalanceRule_feasible m) H S0
          (AdWordsInstance.initialHistoryState_invariant I (by
            intro a
            change (0 : ℝ) ≤ 1
            norm_num))
      have hfresh : ∀ target : Fin (finiteTightActiveCount m s),
          .stage ⟨s, hsm⟩ target ∉ T.seen := by
        intro target hseen
        rw [show T.seen = AdWordsInstance.historyFinset H ∪ S0.seen by
          dsimp [T]
          exact AdWordsInstance.runHistoryStateFrom_seen I
            (finiteTightBalanceRule m) H S0] at hseen
        rcases Finset.mem_union.mp hseen with hprior | hinitial
        · exact finiteTightPreterminalHistory_not_mem m s s
            (Nat.le_of_succ_le hs) hsm le_rfl target
            (AdWordsInstance.mem_historyFinset.mp hprior)
        · change .stage ⟨s, hsm⟩ target ∈ (∅ : Finset (FiniteTightQuery m)) at hinitial
          simp at hinitial
      have hbase : ∀ a : FiniteTightAdvertiser m,
          a.val < finiteTightActiveCount m s → I.spend T.assignment a =
            (s : ℝ) / ((m + 1 : ℕ) : ℝ) := by
        intro a ha
        simpa [I, S0, H, T] using ih (Nat.le_of_succ_le hs) a ha
      have hden : 0 < ((m + 1 : ℕ) : ℝ) := by positivity
      have hc : (s : ℝ) / ((m + 1 : ℕ) : ℝ) < 1 := by
        apply (div_lt_one hden).2
        exact_mod_cast (show s < m + 1 by omega)
      have hcstep : (s : ℝ) / ((m + 1 : ℕ) : ℝ) +
          1 / ((m + 1 : ℕ) : ℝ) ≤ 1 := by
        rw [← add_div]
        apply (div_le_one hden).2
        exact_mod_cast (show s + 1 ≤ m + 1 by omega)
      rw [finiteTightPreterminalHistory,
        AdWordsInstance.runHistoryStateFrom_append]
      have hactive : b.val < finiteTightActiveCount m s := by
        exact lt_of_lt_of_le hb (finiteTightActiveCount_succ_le m s hsm)
      have hstage := finiteTight_runStage_spend m ⟨s, hsm⟩ T
        ((s : ℝ) / ((m + 1 : ℕ) : ℝ)) hc hcstep hstate hfresh hbase
        (finiteTightActiveCount m s) le_rfl b hactive
      simp [hactive] at hstage
      have hformula : (s : ℝ) / ((m + 1 : ℕ) : ℝ) +
          1 / ((m + 1 : ℕ) : ℝ) =
          ((s + 1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) := by
        field_simp [ne_of_gt hden]
        norm_num [Nat.cast_add]
      calc
        I.spend
            (AdWordsInstance.runHistoryStateFrom I (finiteTightBalanceRule m) T
              (finiteTightStageHistory m ⟨s, hsm⟩
                (finiteTightActiveCount m s) le_rfl)).assignment b =
            (s : ℝ) / ((m + 1 : ℕ) : ℝ) + 1 / ((m + 1 : ℕ) : ℝ) := by
              simpa [I, S0, H, T] using hstage
        _ = ((s + 1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) := hformula

/-- The runner's revenue after any number of preterminal stages. -/
theorem finiteTight_preterminal_revenue
    (m : ℕ) :
    ∀ (s : ℕ) (hs : s ≤ m),
      (finiteTightInstance m).revenue
        (AdWordsInstance.runHistoryStateFrom (finiteTightInstance m)
          (finiteTightBalanceRule m)
          (AdWordsInstance.initialHistoryState :
            AdWordsInstance.HistoryState (FiniteTightAdvertiser m) (FiniteTightQuery m))
          (finiteTightPreterminalHistory m s hs)).assignment =
        ∑ i ∈ Finset.range s,
          (finiteTightActiveCount m i : ℝ) * (1 / ((m + 1 : ℕ) : ℝ)) := by
  intro s
  induction s with
  | zero =>
      intro hs
      simp [finiteTightPreterminalHistory, AdWordsInstance.runHistoryStateFrom,
        AdWordsInstance.initialHistoryState, AdWordsInstance.revenue_emptyAssignment]
  | succ s ih =>
      intro hs
      let I := finiteTightInstance m
      let S0 : AdWordsInstance.HistoryState (FiniteTightAdvertiser m) (FiniteTightQuery m) :=
        AdWordsInstance.initialHistoryState
      let H := finiteTightPreterminalHistory m s (Nat.le_of_succ_le hs)
      let T := AdWordsInstance.runHistoryStateFrom I (finiteTightBalanceRule m) S0 H
      have hsm : s < m := by omega
      have hstate : I.StateInvariant T := by
        dsimp [T]
        exact AdWordsInstance.runHistoryStateFrom_invariant I
          (finiteTightBalanceRule m) (finiteTightBalanceRule_feasible m) H S0
          (AdWordsInstance.initialHistoryState_invariant I (by
            intro a
            change (0 : ℝ) ≤ 1
            norm_num))
      have hfresh : ∀ target : Fin (finiteTightActiveCount m s),
          .stage ⟨s, hsm⟩ target ∉ T.seen := by
        intro target hseen
        rw [show T.seen = AdWordsInstance.historyFinset H ∪ S0.seen by
          dsimp [T]
          exact AdWordsInstance.runHistoryStateFrom_seen I
            (finiteTightBalanceRule m) H S0] at hseen
        rcases Finset.mem_union.mp hseen with hprior | hinitial
        · exact finiteTightPreterminalHistory_not_mem m s s
            (Nat.le_of_succ_le hs) hsm le_rfl target
            (AdWordsInstance.mem_historyFinset.mp hprior)
        · change .stage ⟨s, hsm⟩ target ∈ (∅ : Finset (FiniteTightQuery m)) at hinitial
          simp at hinitial
      have hbase : ∀ a : FiniteTightAdvertiser m,
          a.val < finiteTightActiveCount m s → I.spend T.assignment a =
            (s : ℝ) / ((m + 1 : ℕ) : ℝ) := by
        intro a ha
        simpa [I, S0, H, T] using finiteTight_preterminal_spend m s
          (Nat.le_of_succ_le hs) a ha
      have hden : 0 < ((m + 1 : ℕ) : ℝ) := by positivity
      have hc : (s : ℝ) / ((m + 1 : ℕ) : ℝ) < 1 := by
        apply (div_lt_one hden).2
        exact_mod_cast (show s < m + 1 by omega)
      have hcstep : (s : ℝ) / ((m + 1 : ℕ) : ℝ) +
          1 / ((m + 1 : ℕ) : ℝ) ≤ 1 := by
        rw [← add_div]
        apply (div_le_one hden).2
        exact_mod_cast (show s + 1 ≤ m + 1 by omega)
      rw [finiteTightPreterminalHistory,
        AdWordsInstance.runHistoryStateFrom_append]
      have hstage := finiteTight_runStage_revenue m ⟨s, hsm⟩ T
        ((s : ℝ) / ((m + 1 : ℕ) : ℝ)) hc hcstep hstate hfresh hbase
        (finiteTightActiveCount m s) le_rfl
      have hprefix := ih (Nat.le_of_succ_le hs)
      calc
        I.revenue
            (AdWordsInstance.runHistoryStateFrom I (finiteTightBalanceRule m) T
              (finiteTightStageHistory m ⟨s, hsm⟩
                (finiteTightActiveCount m s) le_rfl)).assignment =
            I.revenue T.assignment +
              (finiteTightActiveCount m s : ℝ) * (1 / ((m + 1 : ℕ) : ℝ)) := by
              simpa [I, S0, H, T] using hstage
        _ = (∑ i ∈ Finset.range s,
              (finiteTightActiveCount m i : ℝ) * (1 / ((m + 1 : ℕ) : ℝ))) +
              (finiteTightActiveCount m s : ℝ) * (1 / ((m + 1 : ℕ) : ℝ)) := by
                rw [show I.revenue T.assignment =
                  ∑ i ∈ Finset.range s,
                    (finiteTightActiveCount m i : ℝ) *
                      (1 / ((m + 1 : ℕ) : ℝ)) by
                  simpa [I, S0, H, T] using hprefix]
        _ = ∑ i ∈ Finset.range (s + 1),
              (finiteTightActiveCount m i : ℝ) * (1 / ((m + 1 : ℕ) : ℝ)) := by
                rw [Finset.sum_range_succ]

/-- The final-stage queries, in the same fixed priority order. -/
def finiteTightFinalHistory (m : ℕ) :
    ∀ r : ℕ, r ≤ finiteTightActiveCount m m → List (FiniteTightQuery m)
  | 0, _ => []
  | r + 1, hr =>
      finiteTightFinalHistory m r (Nat.le_of_succ_le hr) ++
        [.final ⟨r, Nat.lt_of_lt_of_le (Nat.lt_succ_self r) hr⟩]

theorem finiteTightFinalHistory_not_mem
    (m r : ℕ) (hr : r ≤ finiteTightActiveCount m m)
    (target : Fin (finiteTightActiveCount m m))
    (hfuture : r ≤ target.val) :
    .final target ∉ finiteTightFinalHistory m r hr := by
  induction r with
  | zero => simp [finiteTightFinalHistory]
  | succ r ih =>
      rw [finiteTightFinalHistory]
      simp only [List.mem_append, List.mem_singleton, not_or]
      constructor
      · exact ih (Nat.le_of_succ_le hr) (by omega)
      · intro h
        have heq : target.val = r := by
          simpa using congrArg (fun q : FiniteTightQuery m =>
            match q with
            | .stage _ _ => 0
            | .final t => t.val
            | .reserve _ _ => 0) h
        omega

/-- The fixed tie rule makes the certified final-stage choice in the actual runner. -/
theorem finiteTight_final_step_eq_assignQuery
    (m : ℕ) (target : Fin (finiteTightActiveCount m m))
    (S : AdWordsInstance.HistoryState (FiniteTightAdvertiser m) (FiniteTightQuery m))
    (c : ℝ)
    (hc : c < 1)
    (hcstep : c + 1 / ((m + 1 : ℕ) : ℝ) ≤ 1)
    (hspend : ∀ b : FiniteTightAdvertiser m,
      b.val < finiteTightActiveCount m m →
        (finiteTightInstance m).spend S.assignment b =
          if b.val < target.val then c + 1 / ((m + 1 : ℕ) : ℝ) else c)
    (hnew : FiniteTightQuery.final target ∉ S.seen) :
    AdWordsInstance.stepHistoryState (finiteTightInstance m)
      (finiteTightBalanceRule m) S (.final target) =
      { assignment := AdWordsInstance.assignQuery S.assignment
          (.final target) (finiteTightQueryTarget m (.final target))
        seen := insert (.final target) S.seen } := by
  classical
  have hactive : ∀ b : FiniteTightAdvertiser m,
      finiteTightEligible m b (.final target) ↔
        b.val < finiteTightActiveCount m m := by
    intro b
    rfl
  have hchoice := finiteTightBalanceRule_eq_target_of_isBalanceChoice m S.assignment
    (.final target) (finiteTight_target_isBalance_of_prefix_state m
      (finiteTightActiveCount m m) (.final target) hactive S.assignment c hc hcstep hspend)
  simp [AdWordsInstance.stepHistoryState, hnew, hchoice]

/-- Running the final stage saturates every surviving active bidder. -/
theorem finiteTight_runFinal_spend
    (m : ℕ)
    (S : AdWordsInstance.HistoryState (FiniteTightAdvertiser m) (FiniteTightQuery m))
    (c : ℝ)
    (hc : c < 1)
    (hcstep : c + 1 / ((m + 1 : ℕ) : ℝ) ≤ 1)
    (hstate : (finiteTightInstance m).StateInvariant S)
    (hfresh : ∀ target : Fin (finiteTightActiveCount m m),
      .final target ∉ S.seen)
    (hbase : ∀ b : FiniteTightAdvertiser m,
      b.val < finiteTightActiveCount m m →
        (finiteTightInstance m).spend S.assignment b = c) :
    ∀ (r : ℕ) (hr : r ≤ finiteTightActiveCount m m)
      (b : FiniteTightAdvertiser m),
      b.val < finiteTightActiveCount m m →
        (finiteTightInstance m).spend
          (AdWordsInstance.runHistoryStateFrom (finiteTightInstance m)
            (finiteTightBalanceRule m) S
            (finiteTightFinalHistory m r hr)).assignment b =
          if b.val < r then c + 1 / ((m + 1 : ℕ) : ℝ) else c := by
  intro r
  induction r with
  | zero =>
      intro hr b hb
      simpa [finiteTightFinalHistory, AdWordsInstance.runHistoryStateFrom]
        using hbase b hb
  | succ r ih =>
      intro hr b hb
      let I := finiteTightInstance m
      let H := finiteTightFinalHistory m r (Nat.le_of_succ_le hr)
      let T := AdWordsInstance.runHistoryStateFrom I (finiteTightBalanceRule m) S H
      let q : FiniteTightQuery m := .final
        ⟨r, Nat.lt_of_lt_of_le (Nat.lt_succ_self r) hr⟩
      have hTspend : ∀ a : FiniteTightAdvertiser m,
          a.val < finiteTightActiveCount m m →
            I.spend T.assignment a =
              if a.val < r then c + 1 / ((m + 1 : ℕ) : ℝ) else c := by
        intro a ha
        simpa [I, H, T] using ih (Nat.le_of_succ_le hr) a ha
      have hTstate : I.StateInvariant T := by
        dsimp [T]
        exact AdWordsInstance.runHistoryStateFrom_invariant I
          (finiteTightBalanceRule m) (finiteTightBalanceRule_feasible m) H S hstate
      have hq_not_H : q ∉ AdWordsInstance.historyFinset H := by
        intro hmem
        apply finiteTightFinalHistory_not_mem m r (Nat.le_of_succ_le hr)
          ⟨r, Nat.lt_of_lt_of_le (Nat.lt_succ_self r) hr⟩ le_rfl
        exact AdWordsInstance.mem_historyFinset.mp hmem
      have hq_not_S : q ∉ S.seen := by
        dsimp [q]
        exact hfresh _
      have hq_new : q ∉ T.seen := by
        rw [show T.seen = AdWordsInstance.historyFinset H ∪ S.seen by
          dsimp [T]
          exact AdWordsInstance.runHistoryStateFrom_seen I
            (finiteTightBalanceRule m) H S]
        simp [hq_not_H, hq_not_S]
      have hchoiceState := finiteTight_final_step_eq_assignQuery m
        ⟨r, Nat.lt_of_lt_of_le (Nat.lt_succ_self r) hr⟩ T c hc hcstep hTspend hq_new
      have hrun :
          AdWordsInstance.runHistoryStateFrom I (finiteTightBalanceRule m) S
            (finiteTightFinalHistory m (r + 1) hr) =
            AdWordsInstance.stepHistoryState I (finiteTightBalanceRule m) T q := by
        rw [finiteTightFinalHistory,
          AdWordsInstance.runHistoryStateFrom_append]
        simp [AdWordsInstance.runHistoryStateFrom, I, H, T, q]
      rw [hrun, hchoiceState]
      have hq_unassigned : T.assignment q = none := hTstate.2 q hq_new
      by_cases hb_eq : b.val = r
      · have hb_target : b = finiteTightQueryTarget m q := by
          apply Fin.ext
          simpa [q] using hb_eq
        subst b
        rw [AdWordsInstance.spend_assignQuery_self_of_unassigned I T.assignment q
          (finiteTightQueryTarget m q) hq_unassigned]
        have htarget_active : (finiteTightQueryTarget m q).val <
            finiteTightActiveCount m m := by
          simpa [q] using (Nat.lt_of_lt_of_le (Nat.lt_succ_self r) hr)
        have hbidq : I.bid (finiteTightQueryTarget m q) q =
            1 / ((m + 1 : ℕ) : ℝ) := by
          simpa [I] using finiteTightInstance_target_bid m q
        rw [hTspend _ htarget_active, hbidq]
        have htarget_val : (finiteTightQueryTarget m q).val = r := by rfl
        simp [htarget_val]
      · have hb_ne_target : b ≠ finiteTightQueryTarget m q := by
          intro heq
          apply hb_eq
          simpa [q] using congrArg Fin.val heq
        rw [AdWordsInstance.spend_assignQuery_other_of_unassigned I T.assignment q
          hq_unassigned hb_ne_target]
        rw [hTspend b hb]
        have hlt : (b.val < r + 1) ↔ b.val < r := by omega
        simp [hlt]

/-- The concrete runner earns one bid for each final-stage query. -/
theorem finiteTight_runFinal_revenue
    (m : ℕ)
    (S : AdWordsInstance.HistoryState (FiniteTightAdvertiser m) (FiniteTightQuery m))
    (c : ℝ)
    (hc : c < 1)
    (hcstep : c + 1 / ((m + 1 : ℕ) : ℝ) ≤ 1)
    (hstate : (finiteTightInstance m).StateInvariant S)
    (hfresh : ∀ target : Fin (finiteTightActiveCount m m),
      .final target ∉ S.seen)
    (hbase : ∀ b : FiniteTightAdvertiser m,
      b.val < finiteTightActiveCount m m →
        (finiteTightInstance m).spend S.assignment b = c) :
    ∀ (r : ℕ) (hr : r ≤ finiteTightActiveCount m m),
      (finiteTightInstance m).revenue
        (AdWordsInstance.runHistoryStateFrom (finiteTightInstance m)
          (finiteTightBalanceRule m) S
          (finiteTightFinalHistory m r hr)).assignment =
        (finiteTightInstance m).revenue S.assignment +
          (r : ℝ) * (1 / ((m + 1 : ℕ) : ℝ)) := by
  intro r
  induction r with
  | zero =>
      intro hr
      simp [finiteTightFinalHistory, AdWordsInstance.runHistoryStateFrom]
  | succ r ih =>
      intro hr
      let I := finiteTightInstance m
      let H := finiteTightFinalHistory m r (Nat.le_of_succ_le hr)
      let T := AdWordsInstance.runHistoryStateFrom I (finiteTightBalanceRule m) S H
      let q : FiniteTightQuery m := .final
        ⟨r, Nat.lt_of_lt_of_le (Nat.lt_succ_self r) hr⟩
      have hTspend : ∀ a : FiniteTightAdvertiser m,
          a.val < finiteTightActiveCount m m →
            I.spend T.assignment a =
              if a.val < r then c + 1 / ((m + 1 : ℕ) : ℝ) else c := by
        intro a ha
        simpa [I, H, T] using finiteTight_runFinal_spend m S c hc hcstep
          hstate hfresh hbase r (Nat.le_of_succ_le hr) a ha
      have hTstate : I.StateInvariant T := by
        dsimp [T]
        exact AdWordsInstance.runHistoryStateFrom_invariant I
          (finiteTightBalanceRule m) (finiteTightBalanceRule_feasible m) H S hstate
      have hq_not_H : q ∉ AdWordsInstance.historyFinset H := by
        intro hmem
        apply finiteTightFinalHistory_not_mem m r (Nat.le_of_succ_le hr)
          ⟨r, Nat.lt_of_lt_of_le (Nat.lt_succ_self r) hr⟩ le_rfl
        exact AdWordsInstance.mem_historyFinset.mp hmem
      have hq_not_S : q ∉ S.seen := by
        dsimp [q]
        exact hfresh _
      have hq_new : q ∉ T.seen := by
        rw [show T.seen = AdWordsInstance.historyFinset H ∪ S.seen by
          dsimp [T]
          exact AdWordsInstance.runHistoryStateFrom_seen I
            (finiteTightBalanceRule m) H S]
        simp [hq_not_H, hq_not_S]
      have hchoiceState := finiteTight_final_step_eq_assignQuery m
        ⟨r, Nat.lt_of_lt_of_le (Nat.lt_succ_self r) hr⟩ T c hc hcstep hTspend hq_new
      have hrun :
          AdWordsInstance.runHistoryStateFrom I (finiteTightBalanceRule m) S
            (finiteTightFinalHistory m (r + 1) hr) =
            AdWordsInstance.stepHistoryState I (finiteTightBalanceRule m) T q := by
        rw [finiteTightFinalHistory,
          AdWordsInstance.runHistoryStateFrom_append]
        simp [AdWordsInstance.runHistoryStateFrom, I, H, T, q]
      rw [hrun, hchoiceState]
      have hq_unassigned : T.assignment q = none := hTstate.2 q hq_new
      rw [AdWordsInstance.revenue_assignQuery_of_unassigned I T.assignment q
        (finiteTightQueryTarget m q) hq_unassigned]
      have hbidq : I.bid (finiteTightQueryTarget m q) q =
          1 / ((m + 1 : ℕ) : ℝ) := by
        simpa [I] using finiteTightInstance_target_bid m q
      rw [hbidq]
      have hprefix := ih (Nat.le_of_succ_le hr)
      change I.revenue T.assignment + 1 / ((m + 1 : ℕ) : ℝ) = _
      rw [show I.revenue T.assignment = I.revenue S.assignment +
          (r : ℝ) * (1 / ((m + 1 : ℕ) : ℝ)) by
        simpa [I, H, T] using hprefix]
      rw [Nat.cast_add]
      norm_num
      ring

theorem finiteTightPreterminalHistory_not_mem_final
    (m r : ℕ) (hr : r ≤ m)
    (target : Fin (finiteTightActiveCount m m)) :
    .final target ∉ finiteTightPreterminalHistory m r hr := by
  induction r with
  | zero => simp [finiteTightPreterminalHistory]
  | succ r ih =>
      rw [finiteTightPreterminalHistory]
      simp only [List.mem_append, not_or]
      constructor
      · exact ih (Nat.le_of_succ_le hr)
      · intro hmem
        obtain ⟨other, heq⟩ := finiteTightStageHistory_mem_same_stage m
          ⟨r, Nat.lt_of_lt_of_le (Nat.lt_succ_self r) hr⟩
          (finiteTightActiveCount m r) le_rfl _ hmem
        cases heq

/-- All online queries carrying a positive bid in the finite tight instance. -/
def finiteTightOnlineCoreHistory (m : ℕ) : List (FiniteTightQuery m) :=
  finiteTightPreterminalHistory m m le_rfl ++
    finiteTightFinalHistory m (finiteTightActiveCount m m) le_rfl

/-- The actual runner saturates every bidder who survives through the final stage. -/
theorem finiteTight_online_core_survivor_spend
    (m : ℕ) (b : FiniteTightAdvertiser m)
    (hb : b.val < finiteTightActiveCount m m) :
    (finiteTightInstance m).spend
      (AdWordsInstance.runHistoryState (finiteTightInstance m)
        (finiteTightBalanceRule m) (finiteTightOnlineCoreHistory m)).assignment b = 1 := by
  let I := finiteTightInstance m
  let S0 : AdWordsInstance.HistoryState (FiniteTightAdvertiser m) (FiniteTightQuery m) :=
    AdWordsInstance.initialHistoryState
  let H := finiteTightPreterminalHistory m m le_rfl
  let T := AdWordsInstance.runHistoryStateFrom I (finiteTightBalanceRule m) S0 H
  have hstate : I.StateInvariant T := by
    dsimp [T]
    exact AdWordsInstance.runHistoryStateFrom_invariant I
      (finiteTightBalanceRule m) (finiteTightBalanceRule_feasible m) H S0
      (AdWordsInstance.initialHistoryState_invariant I (by
        intro a
        change (0 : ℝ) ≤ 1
        norm_num))
  have hfresh : ∀ target : Fin (finiteTightActiveCount m m),
      .final target ∉ T.seen := by
    intro target hseen
    rw [show T.seen = AdWordsInstance.historyFinset H ∪ S0.seen by
      dsimp [T]
      exact AdWordsInstance.runHistoryStateFrom_seen I
        (finiteTightBalanceRule m) H S0] at hseen
    rcases Finset.mem_union.mp hseen with hprior | hinitial
    · exact finiteTightPreterminalHistory_not_mem_final m m le_rfl target
        (AdWordsInstance.mem_historyFinset.mp hprior)
    · change .final target ∈ (∅ : Finset (FiniteTightQuery m)) at hinitial
      simp at hinitial
  have hbase : ∀ a : FiniteTightAdvertiser m,
      a.val < finiteTightActiveCount m m → I.spend T.assignment a =
        (m : ℝ) / ((m + 1 : ℕ) : ℝ) := by
    intro a ha
    simpa [I, S0, H, T] using finiteTight_preterminal_spend m m le_rfl a ha
  have hden : 0 < ((m + 1 : ℕ) : ℝ) := by positivity
  have hc : (m : ℝ) / ((m + 1 : ℕ) : ℝ) < 1 := by
    apply (div_lt_one hden).2
    exact_mod_cast (Nat.lt_succ_self m)
  have hcstep : (m : ℝ) / ((m + 1 : ℕ) : ℝ) +
      1 / ((m + 1 : ℕ) : ℝ) ≤ 1 := by
    rw [← add_div]
    apply (div_le_one hden).2
    norm_num
  unfold finiteTightOnlineCoreHistory
  unfold AdWordsInstance.runHistoryState
  rw [AdWordsInstance.runHistoryStateFrom_append]
  have hfinal := finiteTight_runFinal_spend m T
    ((m : ℝ) / ((m + 1 : ℕ) : ℝ)) hc hcstep hstate hfresh hbase
    (finiteTightActiveCount m m) le_rfl b hb
  simp [hb] at hfinal
  have hformula : (m : ℝ) / ((m + 1 : ℕ) : ℝ) +
      1 / ((m + 1 : ℕ) : ℝ) = 1 := by
    field_simp [ne_of_gt hden]
    norm_num [Nat.cast_add]
  calc
    I.spend
        (AdWordsInstance.runHistoryStateFrom I (finiteTightBalanceRule m) T
          (finiteTightFinalHistory m (finiteTightActiveCount m m) le_rfl)).assignment b =
        (m : ℝ) / ((m + 1 : ℕ) : ℝ) + 1 / ((m + 1 : ℕ) : ℝ) := by
          simpa [I, S0, H, T] using hfinal
    _ = 1 := hformula

/-- Exact total revenue of the positive-bid core of the finite instance. -/
theorem finiteTight_online_core_revenue
    (m : ℕ) :
    (finiteTightInstance m).revenue
      (AdWordsInstance.runHistoryState (finiteTightInstance m)
        (finiteTightBalanceRule m) (finiteTightOnlineCoreHistory m)).assignment =
      ∑ i ∈ Finset.range (m + 1),
        (finiteTightActiveCount m i : ℝ) * (1 / ((m + 1 : ℕ) : ℝ)) := by
  let I := finiteTightInstance m
  let S0 : AdWordsInstance.HistoryState (FiniteTightAdvertiser m) (FiniteTightQuery m) :=
    AdWordsInstance.initialHistoryState
  let H := finiteTightPreterminalHistory m m le_rfl
  let T := AdWordsInstance.runHistoryStateFrom I (finiteTightBalanceRule m) S0 H
  have hstate : I.StateInvariant T := by
    dsimp [T]
    exact AdWordsInstance.runHistoryStateFrom_invariant I
      (finiteTightBalanceRule m) (finiteTightBalanceRule_feasible m) H S0
      (AdWordsInstance.initialHistoryState_invariant I (by
        intro a
        change (0 : ℝ) ≤ 1
        norm_num))
  have hfresh : ∀ target : Fin (finiteTightActiveCount m m),
      .final target ∉ T.seen := by
    intro target hseen
    rw [show T.seen = AdWordsInstance.historyFinset H ∪ S0.seen by
      dsimp [T]
      exact AdWordsInstance.runHistoryStateFrom_seen I
        (finiteTightBalanceRule m) H S0] at hseen
    rcases Finset.mem_union.mp hseen with hprior | hinitial
    · exact finiteTightPreterminalHistory_not_mem_final m m le_rfl target
        (AdWordsInstance.mem_historyFinset.mp hprior)
    · change .final target ∈ (∅ : Finset (FiniteTightQuery m)) at hinitial
      simp at hinitial
  have hbase : ∀ a : FiniteTightAdvertiser m,
      a.val < finiteTightActiveCount m m → I.spend T.assignment a =
        (m : ℝ) / ((m + 1 : ℕ) : ℝ) := by
    intro a ha
    simpa [I, S0, H, T] using finiteTight_preterminal_spend m m le_rfl a ha
  have hden : 0 < ((m + 1 : ℕ) : ℝ) := by positivity
  have hc : (m : ℝ) / ((m + 1 : ℕ) : ℝ) < 1 := by
    apply (div_lt_one hden).2
    exact_mod_cast (Nat.lt_succ_self m)
  have hcstep : (m : ℝ) / ((m + 1 : ℕ) : ℝ) +
      1 / ((m + 1 : ℕ) : ℝ) ≤ 1 := by
    rw [← add_div]
    apply (div_le_one hden).2
    norm_num
  unfold finiteTightOnlineCoreHistory
  unfold AdWordsInstance.runHistoryState
  rw [AdWordsInstance.runHistoryStateFrom_append]
  have hfinal := finiteTight_runFinal_revenue m T
    ((m : ℝ) / ((m + 1 : ℕ) : ℝ)) hc hcstep hstate hfresh hbase
    (finiteTightActiveCount m m) le_rfl
  calc
    I.revenue
        (AdWordsInstance.runHistoryStateFrom I (finiteTightBalanceRule m) T
          (finiteTightFinalHistory m (finiteTightActiveCount m m) le_rfl)).assignment =
        I.revenue T.assignment +
          (finiteTightActiveCount m m : ℝ) * (1 / ((m + 1 : ℕ) : ℝ)) := by
            simpa [I, S0, H, T] using hfinal
    _ = (∑ i ∈ Finset.range m,
          (finiteTightActiveCount m i : ℝ) * (1 / ((m + 1 : ℕ) : ℝ))) +
          (finiteTightActiveCount m m : ℝ) * (1 / ((m + 1 : ℕ) : ℝ)) := by
            rw [show I.revenue T.assignment =
              ∑ i ∈ Finset.range m,
                (finiteTightActiveCount m i : ℝ) *
                  (1 / ((m + 1 : ℕ) : ℝ)) by
              simpa [I, S0, H, T] using finiteTight_preterminal_revenue m m le_rfl]
    _ = ∑ i ∈ Finset.range (m + 1),
          (finiteTightActiveCount m i : ℝ) * (1 / ((m + 1 : ℕ) : ℝ)) := by
            rw [Finset.sum_range_succ]

/-- All reserve queries, enumerated once by their surviving bidder and copy. -/
def finiteTightReserveHistory (m : ℕ) : List (FiniteTightQuery m) :=
  (List.ofFn (finProdFinEquiv.symm :
    Fin (finiteTightActiveCount m m * m) →
      Fin (finiteTightActiveCount m m) × Fin m)).map fun p => .reserve p.1 p.2

theorem finiteTightInstance_nonnegativeBids (m : ℕ) :
    (finiteTightInstance m).NonnegativeBids := by
  classical
  intro a q
  unfold finiteTightInstance
  change 0 ≤ if finiteTightEligible m a q then 1 / ((m + 1 : ℕ) : ℝ) else 0
  split <;> positivity

theorem finiteTightInstance_reserve_active_bid
    (m : ℕ) (a : FiniteTightAdvertiser m)
    (target : Fin (finiteTightActiveCount m m)) (copy : Fin m)
    (ha : a.val < finiteTightActiveCount m m) :
    (finiteTightInstance m).bid a (.reserve target copy) =
      1 / ((m + 1 : ℕ) : ℝ) := by
  simp [finiteTightInstance, finiteTightEligible, ha]

/-- On a reserve query, every nonzero-bid bidder is one of the saturated
survivors of the positive-bid core. -/
theorem finiteTight_reserve_zero_or_saturated
    (m : ℕ)
    (S : AdWordsInstance.HistoryState (FiniteTightAdvertiser m) (FiniteTightQuery m))
    (hsurvivor : ∀ b : FiniteTightAdvertiser m,
      b.val < finiteTightActiveCount m m →
        (finiteTightInstance m).spend S.assignment b = 1)
    (target : Fin (finiteTightActiveCount m m)) (copy : Fin m)
    (a : FiniteTightAdvertiser m) :
    (finiteTightInstance m).bid a (.reserve target copy) = 0 ∨
      (finiteTightInstance m).spend S.assignment a = (finiteTightInstance m).budget a := by
  by_cases ha : a.val < finiteTightActiveCount m m
  · right
    simpa [finiteTightInstance] using hsurvivor a ha
  · left
    simp [finiteTightInstance, finiteTightEligible, ha]

theorem finiteTight_reserve_step_survivor_spend
    (m : ℕ)
    (S : AdWordsInstance.HistoryState (FiniteTightAdvertiser m) (FiniteTightQuery m))
    (hstate : (finiteTightInstance m).StateInvariant S)
    (hsurvivor : ∀ b : FiniteTightAdvertiser m,
      b.val < finiteTightActiveCount m m →
        (finiteTightInstance m).spend S.assignment b = 1)
    (target : Fin (finiteTightActiveCount m m)) (copy : Fin m)
    (b : FiniteTightAdvertiser m)
    (hb : b.val < finiteTightActiveCount m m) :
    (finiteTightInstance m).spend
      (AdWordsInstance.stepHistoryState (finiteTightInstance m)
        (finiteTightBalanceRule m) S (.reserve target copy)).assignment b = 1 := by
  have hfull : (finiteTightInstance m).spend S.assignment b =
      (finiteTightInstance m).budget b := by
    simpa [finiteTightInstance] using hsurvivor b hb
  have hpositive : 0 < (finiteTightInstance m).bid b (.reserve target copy) := by
    rw [finiteTightInstance_reserve_active_bid m b target copy hb]
    positivity
  rw [AdWordsInstance.spend_stepHistoryState_eq_of_saturated_positive
    (finiteTightInstance m) (finiteTightBalanceRule m)
    (finiteTightBalanceRule_feasible m) S (.reserve target copy) b hstate hfull hpositive]
  exact hsurvivor b hb

/-- Reserve queries leave the core revenue unchanged and preserve saturation of
every surviving bidder. -/
theorem finiteTight_runReserve
    (m : ℕ)
    (S : AdWordsInstance.HistoryState (FiniteTightAdvertiser m) (FiniteTightQuery m))
    (hstate : (finiteTightInstance m).StateInvariant S)
    (hsurvivor : ∀ b : FiniteTightAdvertiser m,
      b.val < finiteTightActiveCount m m →
        (finiteTightInstance m).spend S.assignment b = 1)
    (history : List (Fin (finiteTightActiveCount m m) × Fin m)) :
    (finiteTightInstance m).revenue
      (AdWordsInstance.runHistoryStateFrom (finiteTightInstance m)
        (finiteTightBalanceRule m) S
        (history.map fun p => FiniteTightQuery.reserve p.1 p.2)).assignment =
        (finiteTightInstance m).revenue S.assignment ∧
      ∀ b : FiniteTightAdvertiser m,
        b.val < finiteTightActiveCount m m →
          (finiteTightInstance m).spend
            (AdWordsInstance.runHistoryStateFrom (finiteTightInstance m)
              (finiteTightBalanceRule m) S
              (history.map fun p => FiniteTightQuery.reserve p.1 p.2)).assignment b = 1 := by
  induction history generalizing S with
  | nil =>
      constructor
      · simp [AdWordsInstance.runHistoryStateFrom]
      · exact hsurvivor
  | cons p history ih =>
      let q : FiniteTightQuery m := .reserve p.1 p.2
      let T := AdWordsInstance.stepHistoryState (finiteTightInstance m)
        (finiteTightBalanceRule m) S q
      have hTstate : (finiteTightInstance m).StateInvariant T := by
        dsimp [T]
        exact AdWordsInstance.stepHistoryState_invariant (finiteTightInstance m)
          (finiteTightBalanceRule m) (finiteTightBalanceRule_feasible m) S q hstate
      have hTsurvivor : ∀ b : FiniteTightAdvertiser m,
          b.val < finiteTightActiveCount m m →
            (finiteTightInstance m).spend T.assignment b = 1 := by
        intro b hb
        dsimp [T, q]
        exact finiteTight_reserve_step_survivor_spend m S hstate hsurvivor
          p.1 p.2 b hb
      have hstepRevenue : (finiteTightInstance m).revenue T.assignment =
          (finiteTightInstance m).revenue S.assignment := by
        dsimp [T, q]
        apply AdWordsInstance.revenue_stepHistoryState_eq_of_zero_or_saturated
          (finiteTightInstance m) (finiteTightInstance_nonnegativeBids m)
          (finiteTightBalanceRule m) (finiteTightBalanceRule_feasible m) S
          (.reserve p.1 p.2) hstate
        exact finiteTight_reserve_zero_or_saturated m S hsurvivor p.1 p.2
      have htail := ih T hTstate hTsurvivor
      constructor
      · simpa [AdWordsInstance.runHistoryStateFrom, q, T] using htail.1.trans hstepRevenue
      · intro b hb
        simpa [AdWordsInstance.runHistoryStateFrom, q, T] using htail.2 b hb

/-- The complete finite query order: the positive-bid core followed by reserve
queries that Balance cannot charge to a survivor. -/
def finiteTightOnlineHistory (m : ℕ) : List (FiniteTightQuery m) :=
  finiteTightOnlineCoreHistory m ++ finiteTightReserveHistory m

theorem finiteTightStageHistory_mem
    (m : ℕ) (stage : Fin m) :
    ∀ (r : ℕ) (hr : r ≤ finiteTightActiveCount m stage)
      (target : Fin (finiteTightActiveCount m stage)),
      target.val < r → .stage stage target ∈ finiteTightStageHistory m stage r hr := by
  intro r
  induction r with
  | zero =>
      intro hr target htarget
      omega
  | succ r ih =>
      intro hr target htarget
      rw [finiteTightStageHistory]
      simp only [List.mem_append, List.mem_singleton]
      by_cases hprior : target.val < r
      · left
        exact ih (Nat.le_of_succ_le hr) target hprior
      · right
        have hval : target.val = r := by omega
        congr 1
        exact Fin.ext hval

theorem finiteTightPreterminalHistory_mem_stage
    (m : ℕ) :
    ∀ (r : ℕ) (hr : r ≤ m) (stage : Fin m)
      (_hstage : stage.val < r)
      (target : Fin (finiteTightActiveCount m stage)),
      .stage stage target ∈ finiteTightPreterminalHistory m r hr := by
  intro r
  induction r with
  | zero =>
      intro hr stage hstage target
      omega
  | succ r ih =>
      intro hr stage hstage target
      rw [finiteTightPreterminalHistory]
      simp only [List.mem_append]
      by_cases hprior : stage.val < r
      · left
        exact ih (Nat.le_of_succ_le hr) stage hprior target
      · right
        have hval : stage.val = r := by omega
        have hstage_eq : stage = ⟨r,
            Nat.lt_of_lt_of_le (Nat.lt_succ_self r) hr⟩ := Fin.ext hval
        subst stage
        exact finiteTightStageHistory_mem m
          ⟨r, Nat.lt_of_lt_of_le (Nat.lt_succ_self r) hr⟩
          (finiteTightActiveCount m r) le_rfl target target.isLt

theorem finiteTightFinalHistory_mem
    (m : ℕ) :
    ∀ (r : ℕ) (hr : r ≤ finiteTightActiveCount m m)
      (target : Fin (finiteTightActiveCount m m)),
      target.val < r → .final target ∈ finiteTightFinalHistory m r hr := by
  intro r
  induction r with
  | zero =>
      intro hr target htarget
      omega
  | succ r ih =>
      intro hr target htarget
      rw [finiteTightFinalHistory]
      simp only [List.mem_append, List.mem_singleton]
      by_cases hprior : target.val < r
      · left
        exact ih (Nat.le_of_succ_le hr) target hprior
      · right
        have hval : target.val = r := by omega
        congr 1
        exact Fin.ext hval

theorem finiteTightReserveHistory_mem
    (m : ℕ) (target : Fin (finiteTightActiveCount m m)) (copy : Fin m) :
    .reserve target copy ∈ finiteTightReserveHistory m := by
  unfold finiteTightReserveHistory
  have hpair : (target, copy) ∈ List.ofFn (finProdFinEquiv.symm :
      Fin (finiteTightActiveCount m m * m) →
        Fin (finiteTightActiveCount m m) × Fin m) := by
    rw [List.mem_ofFn']
    exact ⟨finProdFinEquiv (target, copy), by simp⟩
  exact List.mem_map_of_mem hpair

/-- The displayed online order presents every query of the finite instance. -/
theorem finiteTightOnlineHistory_covers (m : ℕ) :
    AdWordsInstance.historyFinset (finiteTightOnlineHistory m) = Finset.univ := by
  ext q
  rw [AdWordsInstance.mem_historyFinset]
  simp only [Finset.mem_univ, iff_true]
  cases q with
  | stage stage target =>
      unfold finiteTightOnlineHistory finiteTightOnlineCoreHistory
      simp only [List.mem_append]
      exact Or.inl (Or.inl (finiteTightPreterminalHistory_mem_stage m m le_rfl
        stage stage.isLt target))
  | final target =>
      unfold finiteTightOnlineHistory finiteTightOnlineCoreHistory
      simp only [List.mem_append]
      exact Or.inl (Or.inr (finiteTightFinalHistory_mem m
        (finiteTightActiveCount m m) le_rfl target target.isLt))
  | reserve target copy =>
      unfold finiteTightOnlineHistory
      simp only [List.mem_append]
      exact Or.inr (finiteTightReserveHistory_mem m target copy)

/-- The full finite run earns exactly the revenue earned before reserve
queries arrive. -/
theorem finiteTight_online_revenue_eq_core
    (m : ℕ) :
    (finiteTightInstance m).revenue
      (AdWordsInstance.runHistoryState (finiteTightInstance m)
        (finiteTightBalanceRule m) (finiteTightOnlineHistory m)).assignment =
      (finiteTightInstance m).revenue
        (AdWordsInstance.runHistoryState (finiteTightInstance m)
          (finiteTightBalanceRule m) (finiteTightOnlineCoreHistory m)).assignment := by
  let I := finiteTightInstance m
  let S := AdWordsInstance.runHistoryState I (finiteTightBalanceRule m)
    (finiteTightOnlineCoreHistory m)
  have hstate : I.StateInvariant S := by
    dsimp [S]
    exact AdWordsInstance.runHistoryState_invariant I (by
      intro a
      change (0 : ℝ) ≤ 1
      norm_num) (finiteTightBalanceRule m) (finiteTightBalanceRule_feasible m)
      (finiteTightOnlineCoreHistory m)
  have hsurvivor : ∀ b : FiniteTightAdvertiser m,
      b.val < finiteTightActiveCount m m → I.spend S.assignment b = 1 := by
    intro b hb
    simpa [I, S] using finiteTight_online_core_survivor_spend m b hb
  unfold finiteTightOnlineHistory finiteTightReserveHistory
  unfold AdWordsInstance.runHistoryState
  rw [AdWordsInstance.runHistoryStateFrom_append]
  have hreserve := finiteTight_runReserve m S hstate hsurvivor
    (List.ofFn (finProdFinEquiv.symm :
      Fin (finiteTightActiveCount m m * m) →
        Fin (finiteTightActiveCount m m) × Fin m))
  simpa [I, S] using hreserve.1

/-- Remaining active bidder mass before a slab in the geometric tight execution. -/
noncomputable def factorLPTightActiveMass (m : ℕ) (N : ℝ) (stage : ℕ) : ℝ :=
  N * (1 - 1 / ((m + 1 : ℕ) : ℝ)) ^ stage

/-- Mass that exits after reaching final type `i+1`. -/
noncomputable def factorLPTightTypeMass (m : ℕ) (N : ℝ) (i : Fin m) : ℝ :=
  MSVV07SourceLemmas.paperRoutePrimalCandidate (m := m) N i

/-- Spend fraction of the cohort that exits after slab `i+1`. -/
noncomputable def factorLPTightFinalSpendFraction (m : ℕ) (i : Fin m) : ℝ :=
  ((i.val + 1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ)

/-- Remaining cohort reaches full spend after the final slab. -/
noncomputable def factorLPTightFullMass (m : ℕ) (N : ℝ) : ℝ :=
  factorLPTightActiveMass m N m

/-- Revenue computed from the realized final-spend distribution. -/
noncomputable def factorLPTightFluidRevenue (m : ℕ) (N : ℝ) : ℝ :=
  (∑ i : Fin m,
    factorLPTightTypeMass m N i * factorLPTightFinalSpendFraction m i) +
    factorLPTightFullMass m N

/-- One slab raises every still-active bidder by exactly `1/(m+1)`. -/
noncomputable def factorLPTightSpentBeforeSlab (m stage : ℕ) : ℝ :=
  (stage : ℝ) / ((m + 1 : ℕ) : ℝ)

noncomputable def factorLPTightAllocationPerActiveBidder (m : ℕ) : ℝ :=
  1 / ((m + 1 : ℕ) : ℝ)

/-- Query mass in a slab is exactly the amount allocated by its active cohort. -/
noncomputable def factorLPTightQueryMassAtSlab
    (m : ℕ) (N : ℝ) (stage : ℕ) : ℝ :=
  factorLPTightActiveMass m N stage / ((m + 1 : ℕ) : ℝ)

/-- The common per-bidder state advances by exactly the common slab allocation. -/
theorem factorLPTight_state_update (m stage : ℕ) :
    factorLPTightSpentBeforeSlab m (stage + 1) =
      factorLPTightSpentBeforeSlab m stage +
        factorLPTightAllocationPerActiveBidder m := by
  simp [factorLPTightSpentBeforeSlab,
    factorLPTightAllocationPerActiveBidder, Nat.cast_add]
  ring

/-- Through the final slab, the common post-slab state respects the unit budget. -/
theorem factorLPTight_budget_feasible
    (m stage : ℕ) (hstage : stage ≤ m) :
    factorLPTightSpentBeforeSlab m stage +
        factorLPTightAllocationPerActiveBidder m ≤ 1 := by
  have hden : 0 < (((m + 1 : ℕ) : ℝ)) := by positivity
  have hcast : (stage : ℝ) + 1 ≤ ((m + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ hstage
  rw [factorLPTightSpentBeforeSlab,
    factorLPTightAllocationPerActiveBidder, ← add_div]
  exact (div_le_one hden).2 hcast

/-- Every slab's active cohort allocates exactly that slab's query mass. -/
theorem factorLPTight_slab_work_conservation
    (m : ℕ) (N : ℝ) (stage : ℕ) :
    factorLPTightActiveMass m N stage *
        factorLPTightAllocationPerActiveBidder m =
      factorLPTightQueryMassAtSlab m N stage := by
  unfold factorLPTightAllocationPerActiveBidder
    factorLPTightQueryMassAtSlab
  ring

/-- The geometric active-mass drop is exactly the displayed LP type mass. -/
theorem factorLPTight_active_mass_drop_realizes_type
    (m : ℕ) (N : ℝ) (i : Fin m) :
    factorLPTightActiveMass m N i.val -
        factorLPTightActiveMass m N (i.val + 1) =
      factorLPTightTypeMass m N i := by
  unfold factorLPTightActiveMass factorLPTightTypeMass
    MSVV07SourceLemmas.paperRoutePrimalCandidate
  rw [pow_succ]
  ring

/-- Partial type masses together with the fully spent remainder total `N`. -/
theorem factorLPTight_type_mass_partition (m : ℕ) (N : ℝ) :
    (∑ i : Fin m, factorLPTightTypeMass m N i) +
      factorLPTightFullMass m N = N := by
  let K : ℝ := ((m + 1 : ℕ) : ℝ)
  let r : ℝ := 1 - 1 / K
  have hgeom :
      (∑ i ∈ Finset.range m, r ^ i) * (1 - r) = 1 - r ^ m :=
    geom_sum_mul_neg r m
  change (∑ i : Fin m, N / K * r ^ i.val) + N * r ^ m = N
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => N / K * r ^ i) m]
  calc
    (∑ i ∈ Finset.range m, N / K * r ^ i) + N * r ^ m =
        N * ((1 / K) * (∑ i ∈ Finset.range m, r ^ i) + r ^ m) := by
          rw [mul_add]
          apply congrArg (fun z : ℝ => z + N * r ^ m)
          calc
            (∑ i ∈ Finset.range m, N / K * r ^ i) =
                ∑ i ∈ Finset.range m, (N * (1 / K)) * r ^ i := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  ring
            _ = (N * (1 / K)) *
                (∑ i ∈ Finset.range m, r ^ i) := by
                  rw [Finset.mul_sum]
            _ = N * ((1 / K) *
                (∑ i ∈ Finset.range m, r ^ i)) := by ring
    _ = N * ((1 - r) * (∑ i ∈ Finset.range m, r ^ i) + r ^ m) := by
          dsimp [r]
          ring
    _ = N := by
          rw [mul_comm (1 - r), hgeom]
          ring

/-- A type's spent and unspent fractions sum to one. -/
theorem factorLPTight_spent_add_unspent
    (m : ℕ) (i : Fin m) :
    factorLPTightFinalSpendFraction m i +
      MSVV07SourceLemmas.paperRoutePrimalObjectiveCoeff i = 1 := by
  have hi : i.val ≤ m := Nat.le_of_lt i.isLt
  unfold factorLPTightFinalSpendFraction
    MSVV07SourceLemmas.paperRoutePrimalObjectiveCoeff
  rw [Nat.cast_sub hi]
  have hK : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  field_simp [ne_of_gt hK]
  norm_num
  ring

/-- Execution revenue plus the realized unspent-budget LP objective is total budget. -/
theorem factorLPTight_revenue_add_objective_eq_N (m : ℕ) (N : ℝ) :
    factorLPTightFluidRevenue m N +
        MSVV07SourceLemmas.paperRoutePrimalObjective
          (factorLPTightTypeMass m N) = N := by
  unfold factorLPTightFluidRevenue
    MSVV07SourceLemmas.paperRoutePrimalObjective
  calc
    ((∑ i : Fin m,
          factorLPTightTypeMass m N i * factorLPTightFinalSpendFraction m i) +
        factorLPTightFullMass m N) +
        ∑ i : Fin m,
          MSVV07SourceLemmas.paperRoutePrimalObjectiveCoeff i *
            factorLPTightTypeMass m N i =
      (∑ i : Fin m,
        factorLPTightTypeMass m N i *
          (factorLPTightFinalSpendFraction m i +
            MSVV07SourceLemmas.paperRoutePrimalObjectiveCoeff i)) +
        factorLPTightFullMass m N := by
          rw [add_assoc,
            add_comm (factorLPTightFullMass m N), ← add_assoc]
          rw [← Finset.sum_add_distrib]
          apply congrArg (fun z : ℝ => z + factorLPTightFullMass m N)
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = (∑ i : Fin m, factorLPTightTypeMass m N i) +
        factorLPTightFullMass m N := by
          apply congrArg (fun z : ℝ => z + factorLPTightFullMass m N)
          apply Finset.sum_congr rfl
          intro i hi
          rw [factorLPTight_spent_add_unspent]
          ring
    _ = N := factorLPTight_type_mass_partition m N

/-- The realized execution revenue is `N` minus the exact tight LP objective. -/
theorem factorLPTight_revenue_eq_N_sub_lpValue (m : ℕ) (N : ℝ) :
    factorLPTightFluidRevenue m N =
      N - MSVV07SourceLemmas.factorRevealingLPValue m N := by
  have htotal := factorLPTight_revenue_add_objective_eq_N m N
  have hobjective :
      MSVV07SourceLemmas.paperRoutePrimalObjective
          (factorLPTightTypeMass m N) =
        MSVV07SourceLemmas.factorRevealingLPValue m N := by
    simpa [factorLPTightTypeMass] using
      (MSVV07SourceLemmas.paperRoutePrimalCandidate_objective_value
        (m := m) N)
  rw [hobjective] at htotal
  exact eq_sub_of_add_eq htotal

/--
The explicit cohort-fluid BALANCE realization at unit total budget approaches
the MSVV ratio.  This is an internal limiting witness; it does not purport to
identify the external finite exact instance cited from KP00 in MSVV07.
-/
theorem factorLPTightFluidRevenue_tendsTo_msvvRatio :
    Sequence.SeqTendsTo
      (fun m : ℕ => factorLPTightFluidRevenue m 1)
      paperMsvvRatio := by
  intro delta hdelta
  obtain ⟨K, hK⟩ :=
    MSVV07SourceLemmas.lemma3_factor_revealing_lp_value_tends (1 : ℝ) delta hdelta
  refine ⟨K, ?_⟩
  intro m hm
  have hvalue := hK (m + 1) (by omega)
  have hfactor :
      MSVV07SourceLemmas.factorRevealingLPValue m 1 =
        1 * (1 - 1 / ((m + 1 : ℕ) : ℝ)) ^ (m + 1) := by
    rfl
  change |factorLPTightFluidRevenue m 1 - paperMsvvRatio| ≤ delta
  rw [factorLPTight_revenue_eq_N_sub_lpValue, hfactor]
  calc
    |1 - 1 * (1 - 1 / ((m + 1 : ℕ) : ℝ)) ^ (m + 1) - paperMsvvRatio| =
        |-(1 * (1 - 1 / ((m + 1 : ℕ) : ℝ)) ^ (m + 1) -
          1 / Real.exp 1)| := by
            congr 1
            simp only [paperMsvvRatio]
            ring
    _ = |1 * (1 - 1 / ((m + 1 : ℕ) : ℝ)) ^ (m + 1) -
          1 / Real.exp 1| := abs_neg _
    _ ≤ delta := hvalue

/-- Revenue is the sum of the query mass actually allocated in every slab. -/
theorem factorLPTight_sum_slab_allocations_eq_revenue (m : ℕ) (N : ℝ) :
    (∑ stage ∈ Finset.range (m + 1),
      factorLPTightActiveMass m N stage *
        factorLPTightAllocationPerActiveBidder m) =
      factorLPTightFluidRevenue m N := by
  let K : ℝ := ((m + 1 : ℕ) : ℝ)
  let r : ℝ := 1 - 1 / K
  have hr : 1 - r = 1 / K := by
    dsimp [r]
    ring
  have hgeom :
      (∑ stage ∈ Finset.range (m + 1), r ^ stage) * (1 - r) =
        1 - r ^ (m + 1) :=
    geom_sum_mul_neg r (m + 1)
  change
    (∑ stage ∈ Finset.range (m + 1),
      (N * r ^ stage) * (1 / K)) = factorLPTightFluidRevenue m N
  calc
    (∑ stage ∈ Finset.range (m + 1),
        (N * r ^ stage) * (1 / K)) =
        N * ((∑ stage ∈ Finset.range (m + 1), r ^ stage) *
          (1 - r)) := by
            rw [hr]
            calc
              (∑ stage ∈ Finset.range (m + 1),
                  (N * r ^ stage) * (1 / K)) =
                  ∑ stage ∈ Finset.range (m + 1),
                    (N * (1 / K)) * r ^ stage := by
                      apply Finset.sum_congr rfl
                      intro stage hstage
                      ring
              _ = (N * (1 / K)) *
                    (∑ stage ∈ Finset.range (m + 1), r ^ stage) := by
                      rw [Finset.mul_sum]
              _ = N *
                    ((∑ stage ∈ Finset.range (m + 1), r ^ stage) *
                      (1 / K)) := by ring
    _ = N * (1 - r ^ (m + 1)) := by rw [hgeom]
    _ = N - MSVV07SourceLemmas.factorRevealingLPValue m N := by
      simp [MSVV07SourceLemmas.factorRevealingLPValue,
        MSVV07SourceLemmas.paperRouteCandidateValue, r, K]
      ring
    _ = factorLPTightFluidRevenue m N :=
      (factorLPTight_revenue_eq_N_sub_lpValue m N).symm

/-- The finite active-cohort count agrees exactly with the geometric mass. -/
theorem finiteTightActiveCount_real_eq
    (m stage : ℕ) (hstage : stage ≤ m) :
    (finiteTightActiveCount m stage : ℝ) =
      (((m + 1) ^ m : ℕ) : ℝ) *
        (1 - 1 / ((m + 1 : ℕ) : ℝ)) ^ stage := by
  have hden : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  unfold finiteTightActiveCount
  simp only [Nat.cast_mul, Nat.cast_pow]
  have hpow : ((m + 1 : ℕ) : ℝ) ^ m =
      ((m + 1 : ℕ) : ℝ) ^ (m - stage) *
        ((m + 1 : ℕ) : ℝ) ^ stage := by
    rw [← pow_add]
    congr 1
    omega
  have hratio : 1 - 1 / ((m + 1 : ℕ) : ℝ) =
      (m : ℝ) / ((m + 1 : ℕ) : ℝ) := by
    field_simp
    norm_num
  rw [hpow, hratio]
  have hcancel : ((m + 1 : ℕ) : ℝ) *
      ((m : ℝ) / ((m + 1 : ℕ) : ℝ)) = m := by
    field_simp
  calc
    ((m + 1 : ℕ) : ℝ) ^ (m - stage) * (m : ℝ) ^ stage =
        ((m + 1 : ℕ) : ℝ) ^ (m - stage) *
          (((m + 1 : ℕ) : ℝ) ^ stage *
            ((m : ℝ) / ((m + 1 : ℕ) : ℝ)) ^ stage) := by
          congr 1
          rw [← mul_pow, hcancel]
    _ = ((m + 1 : ℕ) : ℝ) ^ (m - stage) *
          ((m + 1 : ℕ) : ℝ) ^ stage *
            ((m : ℝ) / ((m + 1 : ℕ) : ℝ)) ^ stage := by ring

/-- The actual finite Balance run has exactly the geometric factor-LP value. -/
theorem finiteTight_online_core_revenue_eq_fluid
    (m : ℕ) :
    (finiteTightInstance m).revenue
      (AdWordsInstance.runHistoryState (finiteTightInstance m)
        (finiteTightBalanceRule m) (finiteTightOnlineCoreHistory m)).assignment =
      factorLPTightFluidRevenue m (((m + 1) ^ m : ℕ) : ℝ) := by
  rw [finiteTight_online_core_revenue]
  symm
  rw [← factorLPTight_sum_slab_allocations_eq_revenue]
  apply Finset.sum_congr rfl
  intro stage hstage
  unfold factorLPTightActiveMass factorLPTightAllocationPerActiveBidder
  rw [finiteTightActiveCount_real_eq m stage
    (Nat.le_of_lt_succ (Finset.mem_range.mp hstage))]

theorem finiteTightOffline_feasible (m : ℕ) :
    (finiteTightInstance m).Feasible (finiteTightOfflineAssignment m) := by
  intro b
  rw [finiteTightOffline_spend]
  rfl

/-- The concrete offline assignment realizes the complete population value. -/
theorem finiteTightOffline_revenue (m : ℕ) :
    (finiteTightInstance m).revenue (finiteTightOfflineAssignment m) =
      (((m + 1) ^ m : ℕ) : ℝ) := by
  rw [AdWordsInstance.revenue_eq_sum_spend]
  simp_rw [finiteTightOffline_spend]
  simp

/-- The exact finite offline optimum is the sum of the unit bidder budgets. -/
theorem finiteTight_offlineOptimumValue (m : ℕ) :
    (finiteTightInstance m).offlineOptimumValue (by
      intro a
      change (0 : ℝ) ≤ 1
      norm_num) = (((m + 1) ^ m : ℕ) : ℝ) := by
  let I := finiteTightInstance m
  have hbudget : I.NonnegativeBudgets := by
    intro a
    change (0 : ℝ) ≤ 1
    norm_num
  have hfeasible : I.Feasible (finiteTightOfflineAssignment m) := by
    simpa [I] using finiteTightOffline_feasible m
  have hlower := AdWordsInstance.revenue_le_offlineOptimumValue I hbudget
    (finiteTightOfflineAssignment m) hfeasible
  have hupper := AdWordsInstance.offlineOptimumValue_le_totalBudget I hbudget
  have hoffline : I.revenue (finiteTightOfflineAssignment m) =
      (((m + 1) ^ m : ℕ) : ℝ) := by
    simpa [I] using finiteTightOffline_revenue m
  change I.offlineOptimumValue hbudget = _
  rw [hoffline] at hlower
  have htotal : (∑ a : FiniteTightAdvertiser m, I.budget a) =
      (((m + 1) ^ m : ℕ) : ℝ) := by
    change (∑ _ : FiniteTightAdvertiser m, (1 : ℝ)) = _
    simp
  rw [htotal] at hupper
  linarith

/-- Reserve queries do not alter the actual finite run's factor-LP value. -/
theorem finiteTight_online_revenue_eq_fluid (m : ℕ) :
    (finiteTightInstance m).revenue
      (AdWordsInstance.runHistoryState (finiteTightInstance m)
        (finiteTightBalanceRule m) (finiteTightOnlineHistory m)).assignment =
      factorLPTightFluidRevenue m (((m + 1) ^ m : ℕ) : ℝ) := by
  rw [finiteTight_online_revenue_eq_core]
  exact finiteTight_online_core_revenue_eq_fluid m

theorem factorLPTightFluidRevenue_scale (m : ℕ) (N : ℝ) :
    factorLPTightFluidRevenue m N = N * factorLPTightFluidRevenue m 1 := by
  unfold factorLPTightFluidRevenue factorLPTightTypeMass
    factorLPTightFinalSpendFraction factorLPTightFullMass factorLPTightActiveMass
    MSVV07SourceLemmas.paperRoutePrimalCandidate
  calc
    (∑ i : Fin m, N / ((m + 1 : ℕ) : ℝ) *
        (1 - 1 / ((m + 1 : ℕ) : ℝ)) ^ i.val *
          (((i.val + 1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ))) +
        N * (1 - 1 / ((m + 1 : ℕ) : ℝ)) ^ m =
      (∑ i : Fin m, N * (1 / ((m + 1 : ℕ) : ℝ) *
        (1 - 1 / ((m + 1 : ℕ) : ℝ)) ^ i.val *
          (((i.val + 1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ)))) +
        N * (1 - 1 / ((m + 1 : ℕ) : ℝ)) ^ m := by
          congr 1
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = N * (∑ i : Fin m, 1 / ((m + 1 : ℕ) : ℝ) *
        (1 - 1 / ((m + 1 : ℕ) : ℝ)) ^ i.val *
          (((i.val + 1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ))) +
        N * (1 - 1 / ((m + 1 : ℕ) : ℝ)) ^ m := by
          rw [Finset.mul_sum]
    _ = N * ((∑ i : Fin m, 1 / ((m + 1 : ℕ) : ℝ) *
        (1 - 1 / ((m + 1 : ℕ) : ℝ)) ^ i.val *
          (((i.val + 1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ))) +
        1 * (1 - 1 / ((m + 1 : ℕ) : ℝ)) ^ m) := by ring

/-- The exact finite competitive ratio is the unit-mass factor-LP value. -/
theorem finiteTight_ratio_eq_fluid_unit (m : ℕ) :
    (finiteTightInstance m).revenue
      (AdWordsInstance.runHistoryState (finiteTightInstance m)
        (finiteTightBalanceRule m) (finiteTightOnlineHistory m)).assignment /
      (finiteTightInstance m).offlineOptimumValue (by
        intro a
        change (0 : ℝ) ≤ 1
        norm_num) = factorLPTightFluidRevenue m 1 := by
  rw [finiteTight_online_revenue_eq_fluid, finiteTight_offlineOptimumValue]
  rw [factorLPTightFluidRevenue_scale]
  have hpop : (((m + 1) ^ m : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

theorem finiteTight_ratio_tendsTo_msvvRatio :
    Sequence.SeqTendsTo (fun m : ℕ =>
      (finiteTightInstance m).revenue
        (AdWordsInstance.runHistoryState (finiteTightInstance m)
          (finiteTightBalanceRule m) (finiteTightOnlineHistory m)).assignment /
        (finiteTightInstance m).offlineOptimumValue (by
          intro a
          change (0 : ℝ) ≤ 1
          norm_num)) paperMsvvRatio := by
  intro delta hdelta
  obtain ⟨M, hM⟩ := factorLPTightFluidRevenue_tendsTo_msvvRatio delta hdelta
  refine ⟨M, ?_⟩
  intro m hm
  simpa [finiteTight_ratio_eq_fluid_unit] using hM m hm

/--
Cohort-fluid BALANCE execution that realizes, rather than merely juxtaposes,
the displayed factor-LP witness.  Active bidders share the same slab state and
receive the same increment; their geometric mass drop is the final-type mass.
-/
structure FactorLPTightFluidRealization (m : ℕ) (N : ℝ) where
  typeMass : Fin m → ℝ
  activeMassBeforeSlab : ℕ → ℝ
  spentBeforeSlab : ℕ → ℝ
  allocationPerActiveBidder : ℕ → ℝ
  queryMassAtSlab : ℕ → ℝ
  fullMass : ℝ
  revenue : ℝ
  typeMass_eq_candidate : ∀ i,
    typeMass i = MSVV07SourceLemmas.paperRoutePrimalCandidate (m := m) N i
  active_mass_drop_eq_typeMass : ∀ i : Fin m,
    activeMassBeforeSlab i.val - activeMassBeforeSlab (i.val + 1) = typeMass i
  equal_least_spend_state : ∀ stage, stage ≤ m →
    spentBeforeSlab stage = (stage : ℝ) / ((m + 1 : ℕ) : ℝ)
  equal_allocation_increment : ∀ stage, stage ≤ m →
    allocationPerActiveBidder stage = 1 / ((m + 1 : ℕ) : ℝ)
  query_mass_formula : ∀ stage, stage ≤ m →
    queryMassAtSlab stage = activeMassBeforeSlab stage / ((m + 1 : ℕ) : ℝ)
  state_update : ∀ stage, stage < m →
    spentBeforeSlab (stage + 1) =
      spentBeforeSlab stage + allocationPerActiveBidder stage
  budget_feasible : ∀ stage, stage ≤ m →
    spentBeforeSlab stage + allocationPerActiveBidder stage ≤ 1
  slab_work_conservation : ∀ stage, stage ≤ m →
    activeMassBeforeSlab stage * allocationPerActiveBidder stage =
      queryMassAtSlab stage
  type_mass_partition : (∑ i : Fin m, typeMass i) + fullMass = N
  lp_rows_realized_tight : ∀ i,
    MSVV07SourceLemmas.paperRouteLPRow typeMass i =
      MSVV07SourceLemmas.paperRouteRhs N i
  revenue_from_final_types :
    revenue =
      (∑ i : Fin m,
        typeMass i * factorLPTightFinalSpendFraction m i) + fullMass
  revenue_from_slab_allocations :
    revenue = ∑ stage ∈ Finset.range (m + 1),
      activeMassBeforeSlab stage * allocationPerActiveBidder stage
  revenue_eq_N_sub_lpValue :
    revenue = N - MSVV07SourceLemmas.factorRevealingLPValue m N

/-- The geometric construction satisfies the complete factor-LP realization contract. -/
noncomputable def factorLPTightFluidExecution (m : ℕ) (N : ℝ) :
    FactorLPTightFluidRealization m N where
  typeMass := factorLPTightTypeMass m N
  activeMassBeforeSlab := factorLPTightActiveMass m N
  spentBeforeSlab := factorLPTightSpentBeforeSlab m
  allocationPerActiveBidder := fun _ => factorLPTightAllocationPerActiveBidder m
  queryMassAtSlab := factorLPTightQueryMassAtSlab m N
  fullMass := factorLPTightFullMass m N
  revenue := factorLPTightFluidRevenue m N
  typeMass_eq_candidate := fun _ => rfl
  active_mass_drop_eq_typeMass := factorLPTight_active_mass_drop_realizes_type m N
  equal_least_spend_state := by intro stage hstage; rfl
  equal_allocation_increment := by intro stage hstage; rfl
  query_mass_formula := by intro stage hstage; rfl
  state_update := by
    intro stage hstage
    exact factorLPTight_state_update m stage
  budget_feasible := factorLPTight_budget_feasible m
  slab_work_conservation := by
    intro stage hstage
    exact factorLPTight_slab_work_conservation m N stage
  type_mass_partition := factorLPTight_type_mass_partition m N
  lp_rows_realized_tight := by
    intro i
    exact MSVV07SourceLemmas.paperRoutePrimalCandidate_row_tight N i
  revenue_from_final_types := rfl
  revenue_from_slab_allocations :=
    (factorLPTight_sum_slab_allocations_eq_revenue m N).symm
  revenue_eq_N_sub_lpValue := factorLPTight_revenue_eq_N_sub_lpValue m N

/-- Total revenue executed by the explicit fluid BALANCE allocation. -/
noncomputable def theorem9BaseEqualSpreadBalanceRevenue (N : ℕ) : ℝ :=
  ∑ bidder : Fin N, (nestedSuffixFluidBalanceExecution N).finalSpend bidder

/-- The execution's normalized value is exactly the finite harmonic revenue expression. -/
theorem theorem9BaseEqualSpreadBalanceRevenue_normalized (N : ℕ) :
    theorem9BaseEqualSpreadBalanceRevenue N / (N : ℝ) =
      theorem9NormalizedRevenueUpperBound N := by
  unfold theorem9BaseEqualSpreadBalanceRevenue theorem9NormalizedRevenueUpperBound
  congr 1
  apply Finset.sum_congr rfl
  intro bidder _
  exact fluidBalance_finalSpend_eq_harmonicCap N bidder

/-- The equal-spread base-instance calculation is asymptotically at most `1-1/e`. -/
theorem theorem9_base_equal_spread_balance_eventually_le_msvvRatio_add :
    ∀ delta : ℝ, 0 < delta →
      ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
        theorem9BaseEqualSpreadBalanceRevenue N / (N : ℝ) ≤
          AdWordsInstance.msvvRatio + delta := by
  intro delta hdelta
  simpa [theorem9BaseEqualSpreadBalanceRevenue_normalized] using
    theorem9_harmonic_eventually_le_msvvRatio_add delta hdelta

end SourceRunner
end MSVV07PaperFacing
end Online
end AppliedModelingLib
