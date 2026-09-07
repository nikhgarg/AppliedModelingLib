import AppliedModelingLib.Algorithms.Online.AdWords
import AppliedModelingLib.Algorithms.Complexity.Yao
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Fin
import Mathlib.Data.Fintype.Perm

/-!
# Lower-Bound Interface for AdWords and b-Matching

Section 7 of the MSVV paper uses Yao's lemma: a hard input distribution for
deterministic algorithms implies a worst-case input for every randomized
algorithm. This file records the finite certificate interface needed for that
argument.
-/

namespace AppliedModelingLib
namespace Online

open AppliedModelingLib

/--
A finite Yao certificate for a randomized lower bound.

`normalizedRevenue algorithm input` should be the algorithm's revenue on the
input divided by the offline benchmark for that input. The certificate says
that the chosen input distribution gives every deterministic algorithm average
normalized revenue at most `ratio`.
-/
structure RandomizedLowerBoundCertificate
    (Algorithm Input : Type*) [Fintype Input] [DecidableEq Input]
    (ratio : ℝ) where
  distribution : PMF Input
  normalizedRevenue : Algorithm → Input → ℝ
  deterministicAverage_le :
    ∀ algorithm,
      pmfExp distribution (fun input => normalizedRevenue algorithm input) ≤
        ratio

namespace RandomizedLowerBoundCertificate

variable {Algorithm Input : Type*} {ratio : ℝ}
variable [Fintype Algorithm] [DecidableEq Algorithm]
variable [Fintype Input] [DecidableEq Input] [Nonempty Input]

/--
Every randomized algorithm has an input where its expected normalized revenue
is at most the certificate ratio.
-/
theorem exists_input_randomized_normalizedRevenue_le
    (C : RandomizedLowerBoundCertificate Algorithm Input ratio)
    (randomizedAlgorithm : PMF Algorithm) :
    ∃ input,
      pmfExp randomizedAlgorithm
          (fun algorithm => C.normalizedRevenue algorithm input) ≤
        ratio := by
  exact
    Decision.exists_input_randomized_payoff_le_of_forall_deterministic_average_le
      C.distribution randomizedAlgorithm C.normalizedRevenue ratio
      C.deterministicAverage_le

/--
No randomized algorithm can have normalized revenue strictly above the
certificate ratio on every input.
-/
theorem no_strictly_better_randomized_algorithm
    (C : RandomizedLowerBoundCertificate Algorithm Input ratio)
    (randomizedAlgorithm : PMF Algorithm) :
    ¬ ∀ input,
      ratio <
        pmfExp randomizedAlgorithm
          (fun algorithm => C.normalizedRevenue algorithm input) := by
  exact
    Decision.not_forall_input_bound_lt_randomized_payoff_of_forall_deterministic_average_le
      C.distribution randomizedAlgorithm C.normalizedRevenue ratio
      C.deterministicAverage_le

end RandomizedLowerBoundCertificate

/--
The Section 7 b-matching lower-bound certificate at the MSVV ratio `1 - 1/e`.
Later certificates in this file specialize the hard distribution to uniform
bidder permutations and progressively derive the deterministic average bound.
-/
abbrev BMatchingYaoLowerBoundCertificate
    (Algorithm Input : Type*) [Fintype Input] [DecidableEq Input] :=
  RandomizedLowerBoundCertificate Algorithm Input AdWordsInstance.msvvRatio

theorem bMatching_no_randomized_algorithm_beats_msvvRatio_of_certificate
    {Algorithm Input : Type*}
    [Fintype Algorithm] [DecidableEq Algorithm]
    [Fintype Input] [DecidableEq Input] [Nonempty Input]
    (C : BMatchingYaoLowerBoundCertificate Algorithm Input)
    (randomizedAlgorithm : PMF Algorithm) :
    ¬ ∀ input,
      AdWordsInstance.msvvRatio <
        pmfExp randomizedAlgorithm
          (fun algorithm => C.normalizedRevenue algorithm input) := by
  exact C.no_strictly_better_randomized_algorithm randomizedAlgorithm

/--
The paper's hard distribution chooses a permutation of the bidders uniformly.
The concrete b-matching instance for a permutation has round `i` adjacent to
permutation positions `i, i+1, ..., N-1`.
-/
noncomputable def uniformPermutationDistribution (N : ℕ) :
    PMF (Equiv.Perm (Fin N)) :=
  AppliedModelingLib.uniformPMF (Equiv.Perm (Fin N))

/--
Expectation under the paper's uniform permutation distribution is invariant
under any equivalence of the permutation space. This is the finite relabeling
step used to turn pointwise online-information symmetry into equality of
expected allocations.
-/
theorem uniformPermutationExpectation_eq_of_relabel
    {N : ℕ} (relabel : Equiv.Perm (Fin N) ≃ Equiv.Perm (Fin N))
    {f g : Equiv.Perm (Fin N) → ℝ}
    (h : ∀ permutation, f (relabel permutation) = g permutation) :
    pmfExp (uniformPermutationDistribution N) f =
      pmfExp (uniformPermutationDistribution N) g := by
  classical
  haveI : Nonempty (Equiv.Perm (Fin N)) := ⟨Equiv.refl (Fin N)⟩
  simpa [uniformPermutationDistribution] using
    AppliedModelingLib.pmfExp_uniformPMF_eq_of_comp_equiv
      (α := Equiv.Perm (Fin N)) relabel h

/--
The bidders eligible in Section 7 round `round`: in zero-based indexing these
are the positions `round, round + 1, ..., N - 1`.
-/
def theorem9EligibleBidders (N : ℕ) (round : Fin N) : Finset (Fin N) :=
  (Finset.univ.filter fun bidder => (round : ℕ) ≤ (bidder : ℕ))

@[simp] theorem mem_theorem9EligibleBidders
    (N : ℕ) (round bidder : Fin N) :
    bidder ∈ theorem9EligibleBidders N round ↔
      (round : ℕ) ≤ (bidder : ℕ) := by
  simp [theorem9EligibleBidders]

/--
The actual bidders adjacent to the Section 7 round under a concrete
permutation. Positions are the paper's random order; actual bidder labels are
the values of the permutation.
-/
def theorem9ActualEligibleBidders
    (N : ℕ) (permutation : Equiv.Perm (Fin N)) (round : Fin N) :
    Finset (Fin N) :=
  (theorem9EligibleBidders N round).image permutation

@[simp] theorem mem_theorem9ActualEligibleBidders
    (N : ℕ) (permutation : Equiv.Perm (Fin N)) (round bidder : Fin N) :
    bidder ∈ theorem9ActualEligibleBidders N permutation round ↔
      ∃ position : Fin N,
        (round : ℕ) ≤ (position : ℕ) ∧ permutation position = bidder := by
  simp [theorem9ActualEligibleBidders, mem_theorem9EligibleBidders]

theorem theorem9ActualEligibleBidders_not_mem_of_not_eligible
    {N : ℕ} {permutation : Equiv.Perm (Fin N)} {round position : Fin N}
    (hposition : ¬ (round : ℕ) ≤ (position : ℕ)) :
    permutation position ∉ theorem9ActualEligibleBidders N permutation round := by
  intro hmem
  rcases (mem_theorem9ActualEligibleBidders N permutation round
    (permutation position)).mp hmem with ⟨position', hposition', heq⟩
  have hsame : position' = position := permutation.injective heq
  subst position'
  exact hposition hposition'

/--
Summing over actual eligible bidders is the same as summing over eligible
positions and applying the permutation label map.
-/
theorem theorem9ActualEligibleBidders_sum_eq
    {N : ℕ} (permutation : Equiv.Perm (Fin N)) (round : Fin N)
    (f : Fin N → ℝ) :
    (∑ bidder ∈ theorem9ActualEligibleBidders N permutation round, f bidder) =
      ∑ position ∈ theorem9EligibleBidders N round, f (permutation position) := by
  unfold theorem9ActualEligibleBidders
  exact Finset.sum_image permutation.injective.injOn

/--
The prefix of the hard b-matching instance observed by an online algorithm at
`currentRound`: future rounds are hidden, while past and current rounds expose
their actual eligible bidder sets.
-/
def theorem9ObservedPrefix
    (N : ℕ) (permutation : Equiv.Perm (Fin N)) (currentRound query : Fin N) :
    Finset (Fin N) :=
  if (query : ℕ) ≤ (currentRound : ℕ) then
    theorem9ActualEligibleBidders N permutation query
  else
    ∅

theorem theorem9EligibleBidders_swap_mem_iff
    {N : ℕ} {query bidder bidder' position : Fin N}
    (hbidder : (query : ℕ) ≤ (bidder : ℕ))
    (hbidder' : (query : ℕ) ≤ (bidder' : ℕ)) :
    Equiv.swap bidder bidder' position ∈ theorem9EligibleBidders N query ↔
      position ∈ theorem9EligibleBidders N query := by
  by_cases hpos : position = bidder
  · subst position
    simp [mem_theorem9EligibleBidders, hbidder, hbidder']
  · by_cases hpos' : position = bidder'
    · subst position
      simp [mem_theorem9EligibleBidders, hbidder, hbidder']
    · simp [Equiv.swap_apply_of_ne_of_ne hpos hpos',
        mem_theorem9EligibleBidders]

/--
Swapping two positions that are both still eligible in a round does not change
that round's actual eligible bidder set.
-/
theorem theorem9ActualEligibleBidders_mul_swap_eq
    {N : ℕ} {query bidder bidder' : Fin N}
    (hbidder : (query : ℕ) ≤ (bidder : ℕ))
    (hbidder' : (query : ℕ) ≤ (bidder' : ℕ))
    (permutation : Equiv.Perm (Fin N)) :
    theorem9ActualEligibleBidders N
        (permutation * Equiv.swap bidder bidder') query =
      theorem9ActualEligibleBidders N permutation query := by
  ext actualBidder
  constructor
  · intro hmem
    rcases (mem_theorem9ActualEligibleBidders N
      (permutation * Equiv.swap bidder bidder') query actualBidder).mp hmem
      with ⟨position, hposition, hactual⟩
    refine (mem_theorem9ActualEligibleBidders N permutation query actualBidder).mpr
      ⟨Equiv.swap bidder bidder' position, ?_, ?_⟩
    · exact
        (mem_theorem9EligibleBidders N query
          (Equiv.swap bidder bidder' position)).1
          ((theorem9EligibleBidders_swap_mem_iff
            (N := N) (query := query) (bidder := bidder)
            (bidder' := bidder') (position := position)
            hbidder hbidder').2
            ((mem_theorem9EligibleBidders N query position).2 hposition))
    · simpa [Equiv.Perm.mul_apply] using hactual
  · intro hmem
    rcases (mem_theorem9ActualEligibleBidders N permutation query actualBidder).mp
      hmem with ⟨position, hposition, hactual⟩
    refine (mem_theorem9ActualEligibleBidders N
      (permutation * Equiv.swap bidder bidder') query actualBidder).mpr
      ⟨Equiv.swap bidder bidder' position, ?_, ?_⟩
    · exact
        (mem_theorem9EligibleBidders N query
          (Equiv.swap bidder bidder' position)).1
          ((theorem9EligibleBidders_swap_mem_iff
            (N := N) (query := query) (bidder := bidder)
            (bidder' := bidder') (position := position)
            hbidder hbidder').2
            ((mem_theorem9EligibleBidders N query position).2 hposition))
    · simpa [Equiv.Perm.mul_apply] using hactual

/--
Online-information invariance for the Section 7 hard instance: if two
positions are both eligible in the current round, swapping them in the random
permutation does not change any eligible set visible through that round.
-/
theorem theorem9ObservedPrefix_mul_swap_eq
    {N : ℕ} {round bidder bidder' : Fin N}
    (hbidder : (round : ℕ) ≤ (bidder : ℕ))
    (hbidder' : (round : ℕ) ≤ (bidder' : ℕ))
    (permutation : Equiv.Perm (Fin N)) :
    theorem9ObservedPrefix N
        (permutation * Equiv.swap bidder bidder') round =
      theorem9ObservedPrefix N permutation round := by
  funext query
  unfold theorem9ObservedPrefix
  by_cases hquery : (query : ℕ) ≤ (round : ℕ)
  · have hquery_bidder : (query : ℕ) ≤ (bidder : ℕ) :=
      hquery.trans hbidder
    have hquery_bidder' : (query : ℕ) ≤ (bidder' : ℕ) :=
      hquery.trans hbidder'
    simp [hquery,
      theorem9ActualEligibleBidders_mul_swap_eq
        (N := N) (query := query) (bidder := bidder)
        (bidder' := bidder') hquery_bidder hquery_bidder' permutation]
  · simp [hquery]

/--
There are exactly `N - round` eligible bidders in zero-based round `round`.
This is the denominator in the paper's `E[q_ij] <= 1 / (N - i + 1)` bound.
-/
theorem theorem9EligibleBidders_card (N : ℕ) (round : Fin N) :
    (theorem9EligibleBidders N round).card = N - (round : ℕ) := by
  let s : Finset ℕ := Finset.Ico (round : ℕ) N
  let hlt : ∀ m ∈ s, m < N := by
    intro m hm
    exact (Finset.mem_Ico.mp hm).2
  have hset : theorem9EligibleBidders N round = s.attachFin hlt := by
    ext bidder
    simp [theorem9EligibleBidders, s]
  rw [hset, Finset.card_attachFin]
  simp [s]

/--
Section 7 per-bidder upper bound:
`min {1, sum_{i <= j} 1 / (N - i)}` using zero-based `Fin N` indices.
-/
noncomputable def theorem9BidderSpendUpperBound (N : ℕ) (bidder : Fin N) : ℝ :=
  min 1
    (∑ round : Fin N,
      if (round : ℕ) ≤ (bidder : ℕ) then
        1 / ((N - (round : ℕ) : ℕ) : ℝ)
      else
        0)

/--
Nat-indexed version of the Section 7 harmonic prefix for bidder position `j`.
When `j < N`, this is the uncapped spend
`sum_{i = 0}^j 1 / (N - i)`.
-/
noncomputable def theorem9BidderHarmonicPrefixNat (N j : ℕ) : ℝ :=
  ∑ round ∈ Finset.range (j + 1),
    1 / ((N - round : ℕ) : ℝ)

/--
The one-step harmonic/log inequality used to telescope the Section 7 prefix:
`1 / (k + 1) <= log ((k + 1) / k)`.
-/
theorem theorem9_one_div_succ_le_log_succ_div
    {k : ℕ} (hk : 0 < k) :
    1 / ((k + 1 : ℕ) : ℝ) ≤
      Real.log (((k + 1 : ℕ) : ℝ) / (k : ℝ)) := by
  have hk_real : 0 < (k : ℝ) := by exact_mod_cast hk
  have hratio_pos : 0 < (((k + 1 : ℕ) : ℝ) / (k : ℝ)) := by
    positivity
  have hlog :=
    Real.one_sub_inv_le_log_of_pos hratio_pos
  calc
    1 / ((k + 1 : ℕ) : ℝ)
        = 1 - ((((k + 1 : ℕ) : ℝ) / (k : ℝ))⁻¹) := by
          field_simp [hk_real.ne']
          norm_num [Nat.cast_add, Nat.cast_one]
    _ ≤ Real.log (((k + 1 : ℕ) : ℝ) / (k : ℝ)) := hlog

/--
Logarithmic telescoping step:
`log (a / b) + log (b / c) = log (a / c)` for nonzero endpoints.
-/
theorem theorem9_log_div_add_log_div
    {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    Real.log (a / b) + Real.log (b / c) =
      Real.log (a / c) := by
  rw [← Real.log_mul (div_ne_zero ha hb) (div_ne_zero hb hc)]
  congr 1
  field_simp [hb, hc]

/--
The `Fin N` spend sum in the paper is exactly the Nat-indexed harmonic prefix
for that bidder. The cap can only reduce it.
-/
theorem theorem9BidderSpendUpperBound_le_harmonicPrefixNat
    (N : ℕ) (bidder : Fin N) :
    theorem9BidderSpendUpperBound N bidder ≤
      theorem9BidderHarmonicPrefixNat N bidder := by
  let f : ℕ → ℝ := fun round => 1 / ((N - round : ℕ) : ℝ)
  have hfin_to_nat :
      (∑ round : Fin N,
        if (round : ℕ) ≤ (bidder : ℕ) then
          1 / ((N - (round : ℕ) : ℕ) : ℝ)
        else
          0) =
        ∑ round ∈ Finset.range N,
          if round ≤ (bidder : ℕ) then f round else 0 := by
    symm
    simpa [f] using
      (Finset.sum_range
        (n := N)
        (fun round : ℕ =>
          if round ≤ (bidder : ℕ) then f round else 0))
  have hprefix_set :
      (Finset.range N).filter (fun round => round ≤ (bidder : ℕ)) =
        Finset.range ((bidder : ℕ) + 1) := by
    ext round
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · intro hround
      exact Nat.lt_succ_of_le hround.2
    · intro hround
      have hle_bidder : round ≤ (bidder : ℕ) :=
        Nat.le_of_lt_succ hround
      exact ⟨lt_of_le_of_lt hle_bidder bidder.isLt, hle_bidder⟩
  have hraw_eq :
      (∑ round : Fin N,
        if (round : ℕ) ≤ (bidder : ℕ) then
          1 / ((N - (round : ℕ) : ℕ) : ℝ)
        else
          0) =
        theorem9BidderHarmonicPrefixNat N bidder := by
    rw [hfin_to_nat]
    rw [← Finset.sum_filter]
    rw [hprefix_set]
    rfl
  unfold theorem9BidderSpendUpperBound
  rw [hraw_eq]
  exact min_le_right 1 _

/--
Section 7 harmonic-prefix/log comparison:
`sum_{i = 0}^j 1 / (N - i) <= log (N / (N - j - 1))`.
-/
theorem theorem9BidderHarmonicPrefixNat_le_log_tail
    {N j : ℕ} (h : j + 1 < N) :
    theorem9BidderHarmonicPrefixNat N j ≤
      Real.log ((N : ℝ) / ((N - j - 1 : ℕ) : ℝ)) := by
  induction j with
  | zero =>
      have htail_pos : 0 < N - 1 := by omega
      have hN_one : 1 ≤ N := Nat.one_le_of_lt h
      have hstep :=
        theorem9_one_div_succ_le_log_succ_div
          (k := N - 1) htail_pos
      have htail_succ : N - 1 + 1 = N :=
        Nat.sub_add_cancel hN_one
      simpa [theorem9BidderHarmonicPrefixNat, htail_succ] using hstep
  | succ j ih =>
      have hprev : j + 1 < N := by omega
      have htail_prev_pos : 0 < N - j - 1 := by omega
      have htail_new_pos : 0 < N - (j + 1) - 1 := by omega
      have hstep :=
        theorem9_one_div_succ_le_log_succ_div
          (k := N - (j + 1) - 1) htail_new_pos
      have htail_new_succ :
          N - (j + 1) - 1 + 1 = N - (j + 1) := by
        omega
      have hprev_tail_eq :
          N - j - 1 = N - (j + 1) := by
        omega
      have hstep' :
          1 / ((N - (j + 1) : ℕ) : ℝ) ≤
            Real.log
              (((N - j - 1 : ℕ) : ℝ) /
                ((N - (j + 1) - 1 : ℕ) : ℝ)) := by
        simpa [htail_new_succ, hprev_tail_eq] using hstep
      have hsum_le :
          theorem9BidderHarmonicPrefixNat N j +
              1 / ((N - (j + 1) : ℕ) : ℝ) ≤
            Real.log ((N : ℝ) / ((N - j - 1 : ℕ) : ℝ)) +
              Real.log
                (((N - j - 1 : ℕ) : ℝ) /
                  ((N - (j + 1) - 1 : ℕ) : ℝ)) :=
        add_le_add (ih hprev) hstep'
      have hN_ne : (N : ℝ) ≠ 0 := by
        exact_mod_cast
          (Nat.ne_of_gt (Nat.lt_trans (Nat.succ_pos j) hprev))
      have htail_prev_ne : ((N - j - 1 : ℕ) : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt htail_prev_pos)
      have htail_new_ne :
          ((N - (j + 1) - 1 : ℕ) : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt htail_new_pos)
      calc
        theorem9BidderHarmonicPrefixNat N (j + 1)
            =
          theorem9BidderHarmonicPrefixNat N j +
            1 / ((N - (j + 1) : ℕ) : ℝ) := by
            simp [theorem9BidderHarmonicPrefixNat, Finset.sum_range_succ]
        _ ≤
            Real.log ((N : ℝ) / ((N - j - 1 : ℕ) : ℝ)) +
              Real.log
                (((N - j - 1 : ℕ) : ℝ) /
                  ((N - (j + 1) - 1 : ℕ) : ℝ)) := hsum_le
        _ =
            Real.log
              ((N : ℝ) / ((N - (j + 1) - 1 : ℕ) : ℝ)) :=
          theorem9_log_div_add_log_div hN_ne htail_prev_ne htail_new_ne

/--
The Section 7 capped bidder spend is bounded by the logarithmic tail ratio.
-/
theorem theorem9BidderSpendUpperBound_le_log_tail
    {N : ℕ} (bidder : Fin N)
    (htail : 0 < N - (bidder : ℕ) - 1) :
    theorem9BidderSpendUpperBound N bidder ≤
      Real.log ((N : ℝ) / ((N - (bidder : ℕ) - 1 : ℕ) : ℝ)) := by
  have hprefix :=
    theorem9BidderSpendUpperBound_le_harmonicPrefixNat N bidder
  have hprefix_log :
      theorem9BidderHarmonicPrefixNat N bidder ≤
        Real.log ((N : ℝ) / ((N - (bidder : ℕ) - 1 : ℕ) : ℝ)) :=
    theorem9BidderHarmonicPrefixNat_le_log_tail (N := N)
      (j := bidder) (by omega)
  exact hprefix.trans hprefix_log

/--
The finite normalized revenue upper bound obtained by summing the Section 7
per-bidder spend caps and dividing by the offline optimum `N`.
-/
noncomputable def theorem9NormalizedRevenueUpperBound (N : ℕ) : ℝ :=
  (∑ bidder : Fin N, theorem9BidderSpendUpperBound N bidder) / (N : ℝ)

/--
The bidders whose Section 7 capped harmonic spend crosses the discrete layer
`(r + 1) / M`.
-/
noncomputable def theorem9HarmonicLayerBidders
    (N M r : ℕ) : Finset (Fin N) :=
  (Finset.univ.filter fun bidder =>
    (((r + 1 : ℕ) : ℝ) / (M : ℝ)) ≤
      theorem9BidderSpendUpperBound N bidder)

@[simp] theorem mem_theorem9HarmonicLayerBidders
    (N M r : ℕ) (bidder : Fin N) :
    bidder ∈ theorem9HarmonicLayerBidders N M r ↔
      (((r + 1 : ℕ) : ℝ) / (M : ℝ)) ≤
        theorem9BidderSpendUpperBound N bidder := by
  simp [theorem9HarmonicLayerBidders]

/--
The normalized layer-count upper bound obtained from the discrete layer-cake
decomposition of the Section 7 harmonic spend caps.
-/
noncomputable def theorem9HarmonicLayerAverageUpperBound
    (N M : ℕ) : ℝ :=
  1 / (M : ℝ) +
    (∑ r ∈ Finset.range M,
      ((theorem9HarmonicLayerBidders N M r).card : ℝ) / (N : ℝ)) /
      (M : ℝ)

/--
The finite layer-count estimate used in the Section 7 harmonic-limit proof:
at layer `(r + 1) / M`, at most an `exp (-(r + 1) / M)` fraction of bidders,
up to the finite `N + 1` endpoint slack, should cross the harmonic spend cap.
-/
def theorem9HarmonicLayerCountBound (N M : ℕ) : Prop :=
  ∀ r ∈ Finset.range M,
    ((theorem9HarmonicLayerBidders N M r).card : ℝ) / (N : ℝ) ≤
      (Real.exp (-(1 / (M : ℝ)))) ^ (r + 1) +
        1 / (N : ℝ)

theorem theorem9BidderSpendUpperBound_nonneg
    (N : ℕ) (bidder : Fin N) :
    0 ≤ theorem9BidderSpendUpperBound N bidder := by
  unfold theorem9BidderSpendUpperBound
  refine le_min zero_le_one ?_
  exact Finset.sum_nonneg fun round _ => by
    by_cases hround : (round : ℕ) ≤ (bidder : ℕ)
    · have hden_nonneg : 0 ≤ ((N - (round : ℕ) : ℕ) : ℝ) := by
        exact_mod_cast (Nat.zero_le (N - (round : ℕ)))
      simpa [hround] using one_div_nonneg.mpr hden_nonneg
    · simp [hround]

theorem theorem9BidderSpendUpperBound_le_one
    (N : ℕ) (bidder : Fin N) :
    theorem9BidderSpendUpperBound N bidder ≤ 1 := by
  unfold theorem9BidderSpendUpperBound
  exact min_le_left 1 _

/--
Finite layer-cake bound on `[0,1]`: a value is bounded by the fraction of
positive grid thresholds below it, plus one grid width.
-/
theorem theorem9UnitIntervalLayerCake
    {M : ℕ} (hM : 0 < M) {x : ℝ}
    (hx_nonneg : 0 ≤ x) (hx_le_one : x ≤ 1) :
    x ≤
      (((Finset.range M).filter fun r =>
          (((r + 1 : ℕ) : ℝ) / (M : ℝ)) ≤ x).card : ℝ) /
        (M : ℝ) + 1 / (M : ℝ) := by
  let K : ℕ := Nat.floor ((M : ℝ) * x)
  have hM_real : 0 < (M : ℝ) := by exact_mod_cast hM
  have hMx_nonneg : 0 ≤ (M : ℝ) * x :=
    mul_nonneg hM_real.le hx_nonneg
  have hK_le_M : K ≤ M := by
    dsimp [K]
    exact Nat.floor_le_of_le (by
      calc
        (M : ℝ) * x ≤ (M : ℝ) * 1 := by
          exact mul_le_mul_of_nonneg_left hx_le_one hM_real.le
        _ = (M : ℝ) := by ring)
  let s : Finset ℕ := (Finset.range M).filter fun r =>
    (((r + 1 : ℕ) : ℝ) / (M : ℝ)) ≤ x
  have hrange_subset : Finset.range K ⊆ s := by
    intro r hr
    have hr_lt_K : r < K := Finset.mem_range.mp hr
    have hr_succ_le_K : r + 1 ≤ K := Nat.succ_le_of_lt hr_lt_K
    have hr_lt_M : r < M := lt_of_lt_of_le hr_lt_K hK_le_M
    have hthreshold :
        (((r + 1 : ℕ) : ℝ) / (M : ℝ)) ≤ x := by
      rw [div_le_iff₀ hM_real]
      have hfloor_le : (K : ℝ) ≤ (M : ℝ) * x := by
        dsimp [K]
        exact Nat.floor_le hMx_nonneg
      have hsucc_le_real : ((r + 1 : ℕ) : ℝ) ≤ (K : ℝ) := by
        exact_mod_cast hr_succ_le_K
      exact hsucc_le_real.trans (by simpa [mul_comm] using hfloor_le)
    have hthreshold' :
        ((r : ℝ) + 1) / (M : ℝ) ≤ x := by
      simpa [Nat.cast_add, Nat.cast_one] using hthreshold
    simpa [s, hr_lt_M, hthreshold']
  have hK_le_card : K ≤ s.card := by
    have := Finset.card_le_card hrange_subset
    simpa [s] using this
  have hK_le_card_real : (K : ℝ) ≤ (s.card : ℝ) := by
    exact_mod_cast hK_le_card
  have hx_le_K :
      x ≤ ((K : ℝ) + 1) / (M : ℝ) := by
    rw [le_div_iff₀ hM_real]
    have hlt : (M : ℝ) * x < (K : ℝ) + 1 := by
      dsimp [K]
      exact Nat.lt_floor_add_one ((M : ℝ) * x)
    simpa [mul_comm] using hlt.le
  calc
    x ≤ ((K : ℝ) + 1) / (M : ℝ) := hx_le_K
    _ = (K : ℝ) / (M : ℝ) + 1 / (M : ℝ) := by ring
    _ ≤ (s.card : ℝ) / (M : ℝ) + 1 / (M : ℝ) := by
      have hdiv_le :
          (K : ℝ) / (M : ℝ) ≤ (s.card : ℝ) / (M : ℝ) :=
        div_le_div_of_nonneg_right hK_le_card_real hM_real.le
      linarith
    _ =
      (((Finset.range M).filter fun r =>
          (((r + 1 : ℕ) : ℝ) / (M : ℝ)) ≤ x).card : ℝ) /
        (M : ℝ) + 1 / (M : ℝ) := rfl

/--
The paper's finite harmonic revenue cap is bounded by the average discrete
layer count. The additive `1 / M` is the grid-width loss from discretizing
the capped interval `[0,1]`.
-/
theorem theorem9NormalizedRevenueUpperBound_le_harmonicLayerAverageUpperBound
    {N M : ℕ} (hN : 0 < N) (hM : 0 < M) :
    theorem9NormalizedRevenueUpperBound N ≤
      theorem9HarmonicLayerAverageUpperBound N M := by
  let countForBidder : Fin N → ℝ := fun bidder =>
    (((Finset.range M).filter fun r =>
      (((r + 1 : ℕ) : ℝ) / (M : ℝ)) ≤
        theorem9BidderSpendUpperBound N bidder).card : ℝ)
  have hbidder :
      ∀ bidder : Fin N,
        theorem9BidderSpendUpperBound N bidder ≤
          countForBidder bidder / (M : ℝ) + 1 / (M : ℝ) := by
    intro bidder
    simpa [countForBidder] using
      theorem9UnitIntervalLayerCake (M := M) hM
        (theorem9BidderSpendUpperBound_nonneg N bidder)
        (theorem9BidderSpendUpperBound_le_one N bidder)
  have hsum :
      (∑ bidder : Fin N, theorem9BidderSpendUpperBound N bidder) ≤
        ∑ bidder : Fin N,
          (countForBidder bidder / (M : ℝ) + 1 / (M : ℝ)) :=
    Finset.sum_le_sum (s := (Finset.univ : Finset (Fin N)))
      fun bidder _ => hbidder bidder
  have hcount_sum :
      (∑ bidder : Fin N, countForBidder bidder) =
        ∑ r ∈ Finset.range M,
          ((theorem9HarmonicLayerBidders N M r).card : ℝ) := by
    classical
    dsimp [countForBidder]
    calc
      (∑ bidder : Fin N,
          (((Finset.range M).filter fun r =>
            (((r + 1 : ℕ) : ℝ) / (M : ℝ)) ≤
              theorem9BidderSpendUpperBound N bidder).card : ℝ))
          =
        ∑ bidder : Fin N,
          ∑ r ∈ Finset.range M,
            if (((r + 1 : ℕ) : ℝ) / (M : ℝ)) ≤
                theorem9BidderSpendUpperBound N bidder then
              (1 : ℝ)
            else
              0 := by
            refine Finset.sum_congr rfl ?_
            intro bidder _
            rw [Finset.card_eq_sum_ones]
            simp
      _ =
        ∑ r ∈ Finset.range M,
          ∑ bidder : Fin N,
            if (((r + 1 : ℕ) : ℝ) / (M : ℝ)) ≤
                theorem9BidderSpendUpperBound N bidder then
              (1 : ℝ)
            else
              0 := by
            rw [Finset.sum_comm]
      _ =
        ∑ r ∈ Finset.range M,
          ((theorem9HarmonicLayerBidders N M r).card : ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro r _
            unfold theorem9HarmonicLayerBidders
            rw [Finset.card_eq_sum_ones]
            simp
  have hN_real : 0 < (N : ℝ) := by exact_mod_cast hN
  have hM_real : 0 < (M : ℝ) := by exact_mod_cast hM
  have hsum_eq :
      (∑ bidder : Fin N,
          (countForBidder bidder / (M : ℝ) + 1 / (M : ℝ))) =
        (∑ r ∈ Finset.range M,
          ((theorem9HarmonicLayerBidders N M r).card : ℝ)) /
            (M : ℝ) +
          (N : ℝ) / (M : ℝ) := by
    rw [Finset.sum_add_distrib]
    rw [show (∑ bidder : Fin N, countForBidder bidder / (M : ℝ)) =
        (∑ bidder : Fin N, countForBidder bidder) / (M : ℝ) by
      simp [div_eq_mul_inv, Finset.sum_mul]]
    rw [hcount_sum]
    simp [div_eq_mul_inv, mul_comm]
  have htarget_eq :
      (((∑ r ∈ Finset.range M,
          ((theorem9HarmonicLayerBidders N M r).card : ℝ)) /
            (M : ℝ) +
          (N : ℝ) / (M : ℝ)) / (N : ℝ)) =
        theorem9HarmonicLayerAverageUpperBound N M := by
    unfold theorem9HarmonicLayerAverageUpperBound
    rw [show
        (∑ r ∈ Finset.range M,
          ((theorem9HarmonicLayerBidders N M r).card : ℝ) / (N : ℝ)) =
          (∑ r ∈ Finset.range M,
            ((theorem9HarmonicLayerBidders N M r).card : ℝ)) /
            (N : ℝ) by
      simp [div_eq_mul_inv, Finset.sum_mul]]
    field_simp [hN_real.ne', hM_real.ne']
    ring
  unfold theorem9NormalizedRevenueUpperBound
  calc
    (∑ bidder : Fin N, theorem9BidderSpendUpperBound N bidder) / (N : ℝ)
        ≤
      (∑ bidder : Fin N,
          (countForBidder bidder / (M : ℝ) + 1 / (M : ℝ))) /
        (N : ℝ) := by
          exact div_le_div_of_nonneg_right hsum hN_real.le
    _ =
      (((∑ r ∈ Finset.range M,
          ((theorem9HarmonicLayerBidders N M r).card : ℝ)) /
            (M : ℝ) +
          (N : ℝ) / (M : ℝ)) / (N : ℝ)) := by
          rw [hsum_eq]
    _ = theorem9HarmonicLayerAverageUpperBound N M := htarget_eq

/--
The Section 7 bidder spend cap is monotone in the bidder's position: later
positions include weakly more round terms in the prefix sum.
-/
theorem theorem9BidderSpendUpperBound_mono_bidder
    {N : ℕ} {bidder bidder' : Fin N}
    (hbidder : (bidder : ℕ) ≤ (bidder' : ℕ)) :
    theorem9BidderSpendUpperBound N bidder ≤
      theorem9BidderSpendUpperBound N bidder' := by
  unfold theorem9BidderSpendUpperBound
  refine min_le_min_left 1 ?_
  exact Finset.sum_le_sum fun round _ => by
    by_cases hround : (round : ℕ) ≤ (bidder : ℕ)
    · have hround' : (round : ℕ) ≤ (bidder' : ℕ) :=
        hround.trans hbidder
      simp [hround, hround']
    · by_cases hround' : (round : ℕ) ≤ (bidder' : ℕ)
      · have hden_nonneg : 0 ≤ ((N - (round : ℕ) : ℕ) : ℝ) := by
          exact_mod_cast (Nat.zero_le (N - (round : ℕ)))
        simpa [hround, hround'] using one_div_nonneg.mpr hden_nonneg
      · simp [hround, hround']

/--
The finite right-endpoint geometric grid for `exp(-x)` on `[0,1]`, written in
the form used by the layer-count proof for the Theorem 9 harmonic cap.
-/
noncomputable def theorem9ExponentialGridUpperSum (M : ℕ) : ℝ :=
  (∑ r ∈ Finset.range M, (Real.exp (-(1 / (M : ℝ)))) ^ (r + 1)) /
    (M : ℝ)

/--
The exponential grid upper sum is already bounded by the MSVV ratio. This is
the finite geometric-series part of the Section 7 harmonic-cap limit proof.
-/
theorem theorem9ExponentialGridUpperSum_le_msvvRatio
    {M : ℕ} (hM : 0 < M) :
    theorem9ExponentialGridUpperSum M ≤ AdWordsInstance.msvvRatio := by
  let m : ℝ := M
  let a : ℝ := Real.exp (-(1 / m))
  have hm_pos : 0 < m := by
    dsimp [m]
    exact_mod_cast hM
  have hm_ne : m ≠ 0 := hm_pos.ne'
  have ha_pos : 0 < a := by
    dsimp [a]
    exact Real.exp_pos _
  have ha_nonneg : 0 ≤ a := le_of_lt ha_pos
  have ha_lt_one : a < 1 := by
    dsimp [a]
    have hneg : -(1 / m) < 0 := by
      have hdiv : 0 < 1 / m := one_div_pos.mpr hm_pos
      linarith
    calc
      Real.exp (-(1 / m)) < Real.exp 0 := Real.exp_lt_exp.mpr hneg
      _ = 1 := Real.exp_zero
  have hone_sub_pos : 0 < 1 - a := sub_pos.mpr ha_lt_one
  have ha_ne_one : a ≠ 1 := ne_of_lt ha_lt_one
  have hgeom :
      (∑ r ∈ Finset.range M, a ^ (r + 1)) =
        a * ((1 - a ^ M) / (1 - a)) := by
    calc
      (∑ r ∈ Finset.range M, a ^ (r + 1))
          = ∑ r ∈ Finset.range M, a * a ^ r := by
            refine Finset.sum_congr rfl ?_
            intro r _
            rw [pow_succ']
      _ = a * ∑ r ∈ Finset.range M, a ^ r := by
            rw [Finset.mul_sum]
      _ = a * ((1 - a ^ M) / (1 - a)) := by
            rw [geom_sum_eq ha_ne_one]
            field_simp [sub_ne_zero.mpr ha_ne_one]
            ring
  have ha_pow : a ^ M = 1 / Real.exp 1 := by
    dsimp [a, m]
    rw [← Real.exp_nat_mul]
    have hmul : (M : ℝ) * (-(1 / (M : ℝ))) = -1 := by
      field_simp [show (M : ℝ) ≠ 0 from by exact_mod_cast hM.ne']
    rw [hmul, Real.exp_neg]
    ring
  have ha_le_ratio : a ≤ m / (m + 1) := by
    have h_exp : 1 + 1 / m ≤ Real.exp (1 / m) := by
      simpa [add_comm] using Real.add_one_le_exp (1 / m)
    have hbase_pos : 0 < 1 + 1 / m := by positivity
    have hinv :
        (Real.exp (1 / m))⁻¹ ≤ (1 + 1 / m)⁻¹ :=
      (inv_le_inv₀ (Real.exp_pos _) hbase_pos).2 h_exp
    have hbase_inv : (1 + 1 / m)⁻¹ = m / (m + 1) := by
      field_simp [hm_ne]
    calc
      a = (Real.exp (1 / m))⁻¹ := by
        simp [a, Real.exp_neg]
      _ ≤ (1 + 1 / m)⁻¹ := hinv
      _ = m / (m + 1) := hbase_inv
  have hcoef_le_one : a / (m * (1 - a)) ≤ 1 := by
    have hm_one_sub_pos : 0 < m * (1 - a) :=
      mul_pos hm_pos hone_sub_pos
    rw [div_le_iff₀ hm_one_sub_pos]
    have hmul_le : a * (m + 1) ≤ m := by
      rwa [le_div_iff₀ (by positivity : 0 < m + 1)] at ha_le_ratio
    nlinarith
  unfold theorem9ExponentialGridUpperSum
  dsimp [a, m] at hgeom ha_pow
  calc
    (∑ r ∈ Finset.range M, (Real.exp (-(1 / (M : ℝ)))) ^ (r + 1)) /
        (M : ℝ)
        = (a * ((1 - a ^ M) / (1 - a))) / m := by
          change (∑ r ∈ Finset.range M, a ^ (r + 1)) / m =
            (a * ((1 - a ^ M) / (1 - a))) / m
          rw [hgeom]
    _ = (a / (m * (1 - a))) * AdWordsInstance.msvvRatio := by
          unfold AdWordsInstance.msvvRatio
          rw [ha_pow]
          field_simp [hm_ne, hone_sub_pos.ne', Real.exp_pos 1 |>.ne']
    _ ≤ 1 * AdWordsInstance.msvvRatio := by
          exact mul_le_mul_of_nonneg_right hcoef_le_one
            AdWordsInstance.msvvRatio_nonneg
    _ = AdWordsInstance.msvvRatio := by ring

/--
Finite harmonic-cap comparison from the layer-count estimate. The remaining
paper-local counting argument is isolated in `theorem9HarmonicLayerCountBound`;
this theorem combines it with the discrete layer-cake bound and the geometric
grid estimate.
-/
theorem theorem9NormalizedRevenueUpperBound_le_msvvRatio_add_gridErrors
    {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    (hlayer : theorem9HarmonicLayerCountBound N M) :
    theorem9NormalizedRevenueUpperBound N ≤
      AdWordsInstance.msvvRatio + 1 / (M : ℝ) + 1 / (N : ℝ) := by
  let layerSum : ℝ :=
    ∑ r ∈ Finset.range M,
      ((theorem9HarmonicLayerBidders N M r).card : ℝ) / (N : ℝ)
  let gridSum : ℝ :=
    ∑ r ∈ Finset.range M,
      (Real.exp (-(1 / (M : ℝ)))) ^ (r + 1)
  have hN_real : 0 < (N : ℝ) := by exact_mod_cast hN
  have hM_real : 0 < (M : ℝ) := by exact_mod_cast hM
  have hlayerSum_le :
      layerSum ≤ gridSum + (M : ℝ) / (N : ℝ) := by
    dsimp [layerSum, gridSum]
    calc
      (∑ r ∈ Finset.range M,
          ((theorem9HarmonicLayerBidders N M r).card : ℝ) /
            (N : ℝ))
          ≤
        ∑ r ∈ Finset.range M,
          ((Real.exp (-(1 / (M : ℝ)))) ^ (r + 1) +
            1 / (N : ℝ)) := by
            exact Finset.sum_le_sum fun r hr => hlayer r hr
      _ =
        (∑ r ∈ Finset.range M,
            (Real.exp (-(1 / (M : ℝ)))) ^ (r + 1)) +
          (M : ℝ) / (N : ℝ) := by
            rw [Finset.sum_add_distrib]
            simp [div_eq_mul_inv]
  have hcap_le :
      theorem9NormalizedRevenueUpperBound N ≤
        1 / (M : ℝ) + theorem9ExponentialGridUpperSum M +
          1 / (N : ℝ) := by
    calc
      theorem9NormalizedRevenueUpperBound N
          ≤ theorem9HarmonicLayerAverageUpperBound N M :=
            theorem9NormalizedRevenueUpperBound_le_harmonicLayerAverageUpperBound
              hN hM
      _ = 1 / (M : ℝ) + layerSum / (M : ℝ) := by
            unfold theorem9HarmonicLayerAverageUpperBound
            rfl
      _ ≤ 1 / (M : ℝ) +
            (gridSum + (M : ℝ) / (N : ℝ)) / (M : ℝ) := by
            have hdiv :
                layerSum / (M : ℝ) ≤
                  (gridSum + (M : ℝ) / (N : ℝ)) / (M : ℝ) :=
              div_le_div_of_nonneg_right hlayerSum_le hM_real.le
            linarith
      _ = 1 / (M : ℝ) + theorem9ExponentialGridUpperSum M +
            1 / (N : ℝ) := by
            unfold theorem9ExponentialGridUpperSum
            dsimp [gridSum]
            field_simp [hM_real.ne', hN_real.ne']
            ring
  have hgrid_le :
      theorem9ExponentialGridUpperSum M ≤ AdWordsInstance.msvvRatio :=
    theorem9ExponentialGridUpperSum_le_msvvRatio hM
  calc
    theorem9NormalizedRevenueUpperBound N
        ≤ 1 / (M : ℝ) + theorem9ExponentialGridUpperSum M +
            1 / (N : ℝ) :=
          hcap_le
    _ ≤ 1 / (M : ℝ) + AdWordsInstance.msvvRatio + 1 / (N : ℝ) := by
          linarith
    _ = AdWordsInstance.msvvRatio + 1 / (M : ℝ) + 1 / (N : ℝ) := by
          ring

/--
Delta-form finite harmonic comparison from the layer-count estimate. This is
the form consumed by Theorem 9 wrappers once the grid errors are chosen below
the requested additive slack.
-/
theorem theorem9NormalizedRevenueUpperBound_le_msvvRatio_add_delta_of_layerCountBound
    {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    (hlayer : theorem9HarmonicLayerCountBound N M)
    {δ : ℝ}
    (herrors : 1 / (M : ℝ) + 1 / (N : ℝ) ≤ δ) :
    theorem9NormalizedRevenueUpperBound N ≤
      AdWordsInstance.msvvRatio + δ := by
  have hfinite :=
    theorem9NormalizedRevenueUpperBound_le_msvvRatio_add_gridErrors
      hN hM hlayer
  linarith

/--
Cardinality reduction for the Theorem 9 layer-count estimate. It is enough to
show that every bidder crossing layer `(r + 1) / M` has tail index
`N - bidder - 1` at most the exponential threshold `N * exp (-(r + 1) / M)`.
-/
theorem theorem9HarmonicLayerCountBound_of_tailIndex_le
    {N M : ℕ} (hN : 0 < N)
    (htail :
      ∀ r ∈ Finset.range M, ∀ bidder ∈ theorem9HarmonicLayerBidders N M r,
        ((N - (bidder : ℕ) - 1 : ℕ) : ℝ) ≤
          (N : ℝ) * (Real.exp (-(1 / (M : ℝ)))) ^ (r + 1)) :
    theorem9HarmonicLayerCountBound N M := by
  intro r hr
  let s := theorem9HarmonicLayerBidders N M r
  let a : ℝ := (Real.exp (-(1 / (M : ℝ)))) ^ (r + 1)
  let B : ℝ := (N : ℝ) * a
  let tailIndex : Fin N → ℕ := fun bidder => N - (bidder : ℕ) - 1
  have hN_real : 0 < (N : ℝ) := by exact_mod_cast hN
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    exact pow_nonneg (Real.exp_pos _).le _
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg hN_real.le ha_nonneg
  have hmaps : Set.MapsTo tailIndex (s : Set (Fin N))
      (Finset.range (Nat.floor B + 1) : Set ℕ) := by
    intro bidder hbidder
    have htail_real : ((tailIndex bidder : ℕ) : ℝ) ≤ B := by
      dsimp [tailIndex, B, a]
      exact htail r hr bidder hbidder
    have htail_floor : tailIndex bidder ≤ Nat.floor B :=
      Nat.le_floor htail_real
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le htail_floor)
  have hinj : (s : Set (Fin N)).InjOn tailIndex := by
    intro bidder hbidder bidder' hbidder' htail_eq
    apply Fin.ext
    dsimp [tailIndex] at htail_eq
    omega
  have hcard_nat : s.card ≤ Nat.floor B + 1 := by
    simpa [s] using
      (Finset.card_le_card_of_injOn tailIndex hmaps hinj)
  have hcard_real : (s.card : ℝ) ≤ (Nat.floor B + 1 : ℕ) := by
    exact_mod_cast hcard_nat
  have hfloor_le : (Nat.floor B : ℝ) ≤ B :=
    Nat.floor_le hB_nonneg
  calc
    ((theorem9HarmonicLayerBidders N M r).card : ℝ) / (N : ℝ)
        = (s.card : ℝ) / (N : ℝ) := rfl
    _ ≤ ((Nat.floor B + 1 : ℕ) : ℝ) / (N : ℝ) := by
          exact div_le_div_of_nonneg_right hcard_real hN_real.le
    _ ≤ (B + 1) / (N : ℝ) := by
          have hfloor_add' :
              ((Nat.floor B + 1 : ℕ) : ℝ) ≤ B + 1 := by
            norm_num [Nat.cast_add, hfloor_le]
          exact div_le_div_of_nonneg_right hfloor_add' hN_real.le
    _ = (Real.exp (-(1 / (M : ℝ)))) ^ (r + 1) +
          1 / (N : ℝ) := by
          dsimp [B, a]
          field_simp [hN_real.ne']

/--
Analytic bridge for the Theorem 9 layer count. If the capped harmonic spend of
each bidder is bounded by the logarithmic tail ratio `log (N / tail)`, then
the exponential tail-index implication needed by
`theorem9HarmonicLayerCountBound_of_tailIndex_le` follows.
-/
theorem theorem9HarmonicLayerCountBound_of_logSpendCap
    {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    (hlog :
      ∀ bidder : Fin N,
        0 < N - (bidder : ℕ) - 1 →
          theorem9BidderSpendUpperBound N bidder ≤
            Real.log ((N : ℝ) / ((N - (bidder : ℕ) - 1 : ℕ) : ℝ))) :
    theorem9HarmonicLayerCountBound N M := by
  refine theorem9HarmonicLayerCountBound_of_tailIndex_le hN ?_
  intro r hr bidder hbidder
  let tail : ℕ := N - (bidder : ℕ) - 1
  let threshold : ℝ := (((r + 1 : ℕ) : ℝ) / (M : ℝ))
  have hN_real : 0 < (N : ℝ) := by exact_mod_cast hN
  have hM_real : 0 < (M : ℝ) := by exact_mod_cast hM
  have hpow_eq :
      (Real.exp (-(1 / (M : ℝ)))) ^ (r + 1) =
        Real.exp (-threshold) := by
    dsimp [threshold]
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp [hM_real.ne']
  by_cases htail_zero : tail = 0
  · rw [show ((N - (bidder : ℕ) - 1 : ℕ) : ℝ) = 0 by
        simp [tail, htail_zero]]
    exact mul_nonneg hN_real.le (pow_nonneg (Real.exp_pos _).le _)
  · have htail_pos_nat : 0 < tail := Nat.pos_of_ne_zero htail_zero
    have htail_pos : 0 < (tail : ℝ) := by exact_mod_cast htail_pos_nat
    have hratio_pos : 0 < (N : ℝ) / (tail : ℝ) :=
      div_pos hN_real htail_pos
    have hthreshold_le_spend :
        threshold ≤ theorem9BidderSpendUpperBound N bidder := by
      dsimp [threshold]
      exact (mem_theorem9HarmonicLayerBidders N M r bidder).mp hbidder
    have hthreshold_le_log :
        threshold ≤ Real.log ((N : ℝ) / (tail : ℝ)) := by
      exact hthreshold_le_spend.trans (by
        simpa [tail] using hlog bidder htail_pos_nat)
    have hexp_le :
        Real.exp threshold ≤ (N : ℝ) / (tail : ℝ) :=
      (Real.le_log_iff_exp_le hratio_pos).1 hthreshold_le_log
    have hmul :
        (tail : ℝ) * Real.exp threshold ≤ (N : ℝ) := by
      have hmul' :
          (tail : ℝ) * Real.exp threshold ≤
            (tail : ℝ) * ((N : ℝ) / (tail : ℝ)) :=
        mul_le_mul_of_nonneg_left hexp_le htail_pos.le
      rwa [mul_div_cancel₀ _ htail_pos.ne'] at hmul'
    have htail_exp :
        (tail : ℝ) ≤ (N : ℝ) * Real.exp (-threshold) := by
      rw [Real.exp_neg, ← div_eq_mul_inv]
      rw [le_div_iff₀ (Real.exp_pos threshold)]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
    rw [show ((N - (bidder : ℕ) - 1 : ℕ) : ℝ) = (tail : ℝ) by rfl]
    rw [hpow_eq]
    exact htail_exp

/--
The finite layer-count estimate follows from the now-formalized logarithmic
harmonic spend bound.
-/
theorem theorem9HarmonicLayerCountBound_of_pos
    {N M : ℕ} (hN : 0 < N) (hM : 0 < M) :
    theorem9HarmonicLayerCountBound N M := by
  exact theorem9HarmonicLayerCountBound_of_logSpendCap hN hM
    (fun bidder htail =>
      theorem9BidderSpendUpperBound_le_log_tail bidder htail)

/--
Diagonal layer-count estimate used by the asymptotic Theorem 9 comparison.
-/
theorem theorem9HarmonicLayerCountBound_diagonal
    {N : ℕ} (hN : 0 < N) :
    theorem9HarmonicLayerCountBound N N :=
  theorem9HarmonicLayerCountBound_of_pos hN hN

/--
The explicit grid error `2 / N` is eventually below every positive additive
slack. This is the only asymptotic bookkeeping needed after the finite
layer-count comparison is available on the diagonal `M = N`.
-/
theorem theorem9_gridErrors_eventually_le_delta :
    ∀ δ : ℝ, 0 < δ →
      ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
        0 < N ∧ 1 / (N : ℝ) + 1 / (N : ℝ) ≤ δ := by
  intro δ hδ
  have hhalf_pos : 0 < δ / 2 := by linarith
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (K := ℝ) hhalf_pos
  refine ⟨n + 1, ?_⟩
  intro N hN
  have hN_pos : 0 < N :=
    Nat.lt_of_lt_of_le (Nat.succ_pos n) hN
  have hn1_pos_real : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hN_pos_real : 0 < (N : ℝ) := by exact_mod_cast hN_pos
  have hn1_le_N_real : ((n + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hN
  have hone_div_le :
      1 / (N : ℝ) ≤ 1 / ((n + 1 : ℕ) : ℝ) :=
    one_div_le_one_div_of_le hn1_pos_real hn1_le_N_real
  have hn' : 1 / ((n + 1 : ℕ) : ℝ) < δ / 2 := by
    simpa [Nat.cast_add, Nat.cast_one] using hn
  have hN_inv_lt : 1 / (N : ℝ) < δ / 2 :=
    lt_of_le_of_lt hone_div_le hn'
  constructor
  · exact hN_pos
  · linarith

/--
Asymptotic harmonic comparison from finite layer-count bounds. Once the
layer-count estimate is proved for `M = N` in all sufficiently positive market
sizes, the paper's harmonic cap is eventually within any positive additive
error of `msvvRatio`.
-/
theorem theorem9_harmonic_eventually_le_msvvRatio_add_of_layerCountBound
    (hlayer : ∀ N : ℕ, 0 < N → theorem9HarmonicLayerCountBound N N) :
    ∀ δ : ℝ, 0 < δ →
      ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
        theorem9NormalizedRevenueUpperBound N ≤
          AdWordsInstance.msvvRatio + δ := by
  intro δ hδ
  obtain ⟨N0, hN0⟩ := theorem9_gridErrors_eventually_le_delta δ hδ
  refine ⟨N0, ?_⟩
  intro N hN
  obtain ⟨hN_pos, herrors⟩ := hN0 N hN
  exact
      theorem9NormalizedRevenueUpperBound_le_msvvRatio_add_delta_of_layerCountBound
      hN_pos hN_pos (hlayer N hN_pos) herrors

/--
Unconditional asymptotic Section 7 harmonic comparison:
the paper's finite harmonic cap is eventually within every positive additive
error of `msvvRatio`.
-/
theorem theorem9_harmonic_eventually_le_msvvRatio_add :
    ∀ δ : ℝ, 0 < δ →
      ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
        theorem9NormalizedRevenueUpperBound N ≤
          AdWordsInstance.msvvRatio + δ :=
  theorem9_harmonic_eventually_le_msvvRatio_add_of_layerCountBound
    (fun N hN => theorem9HarmonicLayerCountBound_diagonal hN)

theorem theorem9NormalizedRevenueUpperBound_nonneg (N : ℕ) :
    0 ≤ theorem9NormalizedRevenueUpperBound N := by
  unfold theorem9NormalizedRevenueUpperBound
  have hsum :
      0 ≤ ∑ bidder : Fin N, theorem9BidderSpendUpperBound N bidder :=
    Finset.sum_nonneg fun bidder _ =>
      theorem9BidderSpendUpperBound_nonneg N bidder
  have hden : 0 ≤ (N : ℝ) := by exact_mod_cast (Nat.zero_le N)
  exact div_nonneg hsum hden

theorem theorem9NormalizedRevenueUpperBound_le_one
    {N : ℕ} (hN : 0 < N) :
    theorem9NormalizedRevenueUpperBound N ≤ 1 := by
  unfold theorem9NormalizedRevenueUpperBound
  have hsum_le :
      (∑ bidder : Fin N, theorem9BidderSpendUpperBound N bidder) ≤
        ∑ _bidder : Fin N, (1 : ℝ) :=
    Finset.sum_le_sum fun bidder _ =>
      theorem9BidderSpendUpperBound_le_one N bidder
  have hsum_le_card :
      (∑ bidder : Fin N, theorem9BidderSpendUpperBound N bidder) ≤
        (N : ℝ) := by
    simpa using hsum_le
  have hN_real : 0 < (N : ℝ) := by exact_mod_cast hN
  rw [div_le_iff₀ hN_real]
  simpa using hsum_le_card

/--
Concrete Section 7 certificate specialized to the paper's uniform permutation
distribution. The remaining mathematical field is the paper's deterministic
average normalized-revenue bound for that distribution.
-/
structure BMatchingPermutationLowerBoundCertificate
    (N : ℕ) (Algorithm : Type*) where
  normalizedRevenue : Algorithm → Equiv.Perm (Fin N) → ℝ
  deterministicAverage_le :
    ∀ algorithm,
      pmfExp (uniformPermutationDistribution N)
          (fun permutation => normalizedRevenue algorithm permutation) ≤
        AdWordsInstance.msvvRatio

/--
More explicit Section 7 certificate: deterministic algorithms are first bounded
by the paper's finite harmonic spend-cap expression, and that expression is
then bounded by a requested finite ratio. For the paper theorem this ratio is
used as `msvvRatio + δ` before taking the large-market limit.
-/
structure BMatchingPermutationRevenueBoundCertificate
    (N : ℕ) (Algorithm : Type*) (ratio : ℝ) where
  normalizedRevenue : Algorithm → Equiv.Perm (Fin N) → ℝ
  deterministicAverage_le_revenueBound :
    ∀ algorithm,
      pmfExp (uniformPermutationDistribution N)
          (fun permutation => normalizedRevenue algorithm permutation) ≤
        theorem9NormalizedRevenueUpperBound N
  revenueBound_le_ratio :
    theorem9NormalizedRevenueUpperBound N ≤ ratio

/--
Round-allocation form of the Section 7 deterministic calculation. The field
`expectedRoundBidderAllocation_le` corresponds to the paper's
`E_pi[q_ij] <= 1 / (N - i + 1)` line, in zero-based indices.
-/
structure BMatchingRoundAllocationRevenueCertificate
    (N : ℕ) (Algorithm : Type*) (ratio : ℝ) where
  normalizedRevenue : Algorithm → Equiv.Perm (Fin N) → ℝ
  expectedRoundBidderAllocation : Algorithm → Fin N → Fin N → ℝ
  deterministicAverage_le_cappedExpectedSpend :
    ∀ algorithm,
      pmfExp (uniformPermutationDistribution N)
          (fun permutation => normalizedRevenue algorithm permutation) ≤
        (∑ bidder : Fin N,
          min 1
            (∑ round : Fin N,
              expectedRoundBidderAllocation algorithm round bidder)) / (N : ℝ)
  expectedRoundBidderAllocation_le :
    ∀ algorithm round bidder,
      expectedRoundBidderAllocation algorithm round bidder ≤
        if (round : ℕ) ≤ (bidder : ℕ) then
          1 / ((N - (round : ℕ) : ℕ) : ℝ)
        else
          0
  revenueBound_le_ratio :
    theorem9NormalizedRevenueUpperBound N ≤ ratio

/--
Pointwise allocation form of the Section 7 deterministic calculation. This
certificate starts from each deterministic algorithm's realized round/bidder
allocation on every permutation instance, derives the capped expected-spend
bound by finite expectation algebra, and leaves the paper's symmetry bound as
the explicit `expectedAllocation_le` field.
-/
structure BMatchingPointwiseAllocationRevenueCertificate
    (N : ℕ) (Algorithm : Type*) (ratio : ℝ) where
  normalizedRevenue : Algorithm → Equiv.Perm (Fin N) → ℝ
  allocation : Algorithm → Equiv.Perm (Fin N) → Fin N → Fin N → ℝ
  normalizedRevenue_le_cappedAllocationSpend :
    ∀ algorithm permutation,
      normalizedRevenue algorithm permutation ≤
        (∑ bidder : Fin N,
          min 1
            (∑ round : Fin N,
              allocation algorithm permutation round bidder)) /
          (N : ℝ)
  expectedAllocation_le :
    ∀ algorithm round bidder,
      pmfExp (uniformPermutationDistribution N)
          (fun permutation => allocation algorithm permutation round bidder) ≤
        if (round : ℕ) ≤ (bidder : ℕ) then
          1 / ((N - (round : ℕ) : ℕ) : ℝ)
        else
          0
  revenueBound_le_ratio :
    theorem9NormalizedRevenueUpperBound N ≤ ratio

/--
Symmetry/capacity form of the Section 7 deterministic calculation. Instead of
assuming the paper's expected allocation bound directly, this certificate
derives it from three more primitive claims:

* allocations to ineligible positions are zero;
* each round allocates at most one unit across eligible positions;
* under the random permutation distribution, all eligible positions in the same
  round have the same expected allocation.
-/
structure BMatchingSymmetricPointwiseAllocationRevenueCertificate
    (N : ℕ) (Algorithm : Type*) (ratio : ℝ) where
  normalizedRevenue : Algorithm → Equiv.Perm (Fin N) → ℝ
  allocation : Algorithm → Equiv.Perm (Fin N) → Fin N → Fin N → ℝ
  normalizedRevenue_le_cappedAllocationSpend :
    ∀ algorithm permutation,
      normalizedRevenue algorithm permutation ≤
        (∑ bidder : Fin N,
          min 1
            (∑ round : Fin N,
              allocation algorithm permutation round bidder)) /
          (N : ℝ)
  allocation_zero_of_ineligible :
    ∀ algorithm permutation (round bidder : Fin N),
      ¬ (round : ℕ) ≤ (bidder : ℕ) →
        allocation algorithm permutation round bidder = 0
  round_allocation_sum_le_one :
    ∀ algorithm permutation (round : Fin N),
      (∑ bidder ∈ theorem9EligibleBidders N round,
        allocation algorithm permutation round bidder) ≤ 1
  expectedAllocation_eq_of_eligible :
    ∀ algorithm (round bidder bidder' : Fin N),
      (round : ℕ) ≤ (bidder : ℕ) →
      (round : ℕ) ≤ (bidder' : ℕ) →
        pmfExp (uniformPermutationDistribution N)
            (fun permutation => allocation algorithm permutation round bidder) =
          pmfExp (uniformPermutationDistribution N)
            (fun permutation => allocation algorithm permutation round bidder')
  revenueBound_le_ratio :
    theorem9NormalizedRevenueUpperBound N ≤ ratio

/--
Relabeling form of the Section 7 symmetry calculation. It replaces the
expected-allocation equality field with a pointwise statement: for any two
eligible positions in a round, relabeling the uniformly random permutation
turns allocation to one position into allocation to the other. Uniform
permutation invariance then derives the expected equality automatically.
-/
structure BMatchingRelabelSymmetricPointwiseAllocationRevenueCertificate
    (N : ℕ) (Algorithm : Type*) (ratio : ℝ) where
  normalizedRevenue : Algorithm → Equiv.Perm (Fin N) → ℝ
  allocation : Algorithm → Equiv.Perm (Fin N) → Fin N → Fin N → ℝ
  normalizedRevenue_le_cappedAllocationSpend :
    ∀ algorithm permutation,
      normalizedRevenue algorithm permutation ≤
        (∑ bidder : Fin N,
          min 1
            (∑ round : Fin N,
              allocation algorithm permutation round bidder)) /
          (N : ℝ)
  allocation_zero_of_ineligible :
    ∀ algorithm permutation (round bidder : Fin N),
      ¬ (round : ℕ) ≤ (bidder : ℕ) →
        allocation algorithm permutation round bidder = 0
  round_allocation_sum_le_one :
    ∀ algorithm permutation (round : Fin N),
      (∑ bidder ∈ theorem9EligibleBidders N round,
        allocation algorithm permutation round bidder) ≤ 1
  relabelInput :
    Fin N → Fin N → Fin N → Equiv.Perm (Fin N) ≃ Equiv.Perm (Fin N)
  allocation_eq_of_relabel_eligible :
    ∀ algorithm (round bidder bidder' : Fin N),
      (round : ℕ) ≤ (bidder : ℕ) →
      (round : ℕ) ≤ (bidder' : ℕ) →
      ∀ permutation,
        allocation algorithm
            (relabelInput round bidder bidder' permutation)
            round bidder =
          allocation algorithm permutation round bidder'
  revenueBound_le_ratio :
    theorem9NormalizedRevenueUpperBound N ≤ ratio

/--
Observed-prefix form of the Section 7 online-information argument. The
allocation to a position is represented as an allocation to the actual bidder
label using only the eligible sets visible through the current round. The file
proves that this prefix factorization supplies the relabeling symmetry field.
-/
structure BMatchingObservedPrefixAllocationRevenueCertificate
    (N : ℕ) (Algorithm : Type*) (ratio : ℝ) where
  normalizedRevenue : Algorithm → Equiv.Perm (Fin N) → ℝ
  allocation : Algorithm → Equiv.Perm (Fin N) → Fin N → Fin N → ℝ
  prefixAllocation :
    Algorithm → (Fin N → Finset (Fin N)) → Fin N → Fin N → ℝ
  allocation_eq_prefix :
    ∀ algorithm permutation round bidder,
      allocation algorithm permutation round bidder =
        prefixAllocation algorithm
          (theorem9ObservedPrefix N permutation round)
          round (permutation bidder)
  normalizedRevenue_le_cappedAllocationSpend :
    ∀ algorithm permutation,
      normalizedRevenue algorithm permutation ≤
        (∑ bidder : Fin N,
          min 1
            (∑ round : Fin N,
              allocation algorithm permutation round bidder)) /
          (N : ℝ)
  allocation_zero_of_ineligible :
    ∀ algorithm permutation (round bidder : Fin N),
      ¬ (round : ℕ) ≤ (bidder : ℕ) →
        allocation algorithm permutation round bidder = 0
  round_allocation_sum_le_one :
    ∀ algorithm permutation (round : Fin N),
      (∑ bidder ∈ theorem9EligibleBidders N round,
        allocation algorithm permutation round bidder) ≤ 1
  revenueBound_le_ratio :
    theorem9NormalizedRevenueUpperBound N ≤ ratio

/--
Feasible observed-prefix allocation certificate. This is closer to a concrete
deterministic online algorithm: allocations are made to actual bidder labels as
a function of the visible prefix, are zero outside the currently visible
eligible set, and allocate at most one unit in each round.
-/
structure BMatchingFeasibleObservedPrefixAllocationRevenueCertificate
    (N : ℕ) (Algorithm : Type*) (ratio : ℝ) where
  normalizedRevenue : Algorithm → Equiv.Perm (Fin N) → ℝ
  prefixAllocation :
    Algorithm → (Fin N → Finset (Fin N)) → Fin N → Fin N → ℝ
  normalizedRevenue_le_cappedPrefixAllocationSpend :
    ∀ algorithm permutation,
      normalizedRevenue algorithm permutation ≤
        (∑ bidder : Fin N,
          min 1
            (∑ round : Fin N,
              prefixAllocation algorithm
                (theorem9ObservedPrefix N permutation round)
                round (permutation bidder))) /
          (N : ℝ)
  prefixAllocation_zero_of_not_visible :
    ∀ algorithm obs round bidder,
      bidder ∉ obs round →
        prefixAllocation algorithm obs round bidder = 0
  prefixAllocation_sum_le_one :
    ∀ algorithm obs round,
      (∑ bidder ∈ obs round,
        prefixAllocation algorithm obs round bidder) ≤ 1
  revenueBound_le_ratio :
    theorem9NormalizedRevenueUpperBound N ≤ ratio

/--
Family-level certificate for the asymptotic Section 7 lower bound. It packages
the deterministic round-allocation calculation for every market size. The
harmonic-cap comparison is proved in this file.
-/
structure BMatchingTheorem9FamilyCertificate
    (Algorithm : ℕ → Type*)
    [∀ N, Fintype (Algorithm N)] [∀ N, DecidableEq (Algorithm N)] where
  normalizedRevenue :
    (N : ℕ) → Algorithm N → Equiv.Perm (Fin N) → ℝ
  expectedRoundBidderAllocation :
    (N : ℕ) → Algorithm N → Fin N → Fin N → ℝ
  deterministicAverage_le_cappedExpectedSpend :
    ∀ N algorithm,
      pmfExp (uniformPermutationDistribution N)
          (fun permutation => normalizedRevenue N algorithm permutation) ≤
        (∑ bidder : Fin N,
          min 1
            (∑ round : Fin N,
              expectedRoundBidderAllocation N algorithm round bidder)) /
          (N : ℝ)
  expectedRoundBidderAllocation_le :
    ∀ N algorithm round bidder,
      expectedRoundBidderAllocation N algorithm round bidder ≤
        if (round : ℕ) ≤ (bidder : ℕ) then
          1 / ((N - (round : ℕ) : ℕ) : ℝ)
        else
          0

/--
Family-level pointwise-allocation version of the Section 7 lower-bound
certificate. This is closest to the paper's deterministic-algorithm analysis:
for every market size and permutation instance, the algorithm has realized
round/bidder allocation variables; the file derives the expected capped-spend
certificate from those variables.
-/
structure BMatchingTheorem9PointwiseFamilyCertificate
    (Algorithm : ℕ → Type*)
    [∀ N, Fintype (Algorithm N)] [∀ N, DecidableEq (Algorithm N)] where
  normalizedRevenue :
    (N : ℕ) → Algorithm N → Equiv.Perm (Fin N) → ℝ
  allocation :
    (N : ℕ) → Algorithm N → Equiv.Perm (Fin N) → Fin N → Fin N → ℝ
  normalizedRevenue_le_cappedAllocationSpend :
    ∀ N algorithm permutation,
      normalizedRevenue N algorithm permutation ≤
        (∑ bidder : Fin N,
          min 1
            (∑ round : Fin N,
              allocation N algorithm permutation round bidder)) /
          (N : ℝ)
  expectedAllocation_le :
    ∀ N algorithm round bidder,
      pmfExp (uniformPermutationDistribution N)
          (fun permutation => allocation N algorithm permutation round bidder) ≤
        if (round : ℕ) ≤ (bidder : ℕ) then
          1 / ((N - (round : ℕ) : ℕ) : ℝ)
        else
          0

/--
Family-level symmetry/capacity version of the Section 7 lower-bound
certificate. It packages the paper's online-information symmetry claim across
all market sizes; the finite expectation algebra then derives the pointwise
family certificate.
-/
structure BMatchingTheorem9SymmetricPointwiseFamilyCertificate
    (Algorithm : ℕ → Type*)
    [∀ N, Fintype (Algorithm N)] [∀ N, DecidableEq (Algorithm N)] where
  normalizedRevenue :
    (N : ℕ) → Algorithm N → Equiv.Perm (Fin N) → ℝ
  allocation :
    (N : ℕ) → Algorithm N → Equiv.Perm (Fin N) → Fin N → Fin N → ℝ
  normalizedRevenue_le_cappedAllocationSpend :
    ∀ N algorithm permutation,
      normalizedRevenue N algorithm permutation ≤
        (∑ bidder : Fin N,
          min 1
            (∑ round : Fin N,
              allocation N algorithm permutation round bidder)) /
          (N : ℝ)
  allocation_zero_of_ineligible :
    ∀ N algorithm permutation (round bidder : Fin N),
      ¬ (round : ℕ) ≤ (bidder : ℕ) →
        allocation N algorithm permutation round bidder = 0
  round_allocation_sum_le_one :
    ∀ N algorithm permutation (round : Fin N),
      (∑ bidder ∈ theorem9EligibleBidders N round,
        allocation N algorithm permutation round bidder) ≤ 1
  expectedAllocation_eq_of_eligible :
    ∀ N algorithm (round bidder bidder' : Fin N),
      (round : ℕ) ≤ (bidder : ℕ) →
      (round : ℕ) ≤ (bidder' : ℕ) →
        pmfExp (uniformPermutationDistribution N)
            (fun permutation => allocation N algorithm permutation round bidder) =
          pmfExp (uniformPermutationDistribution N)
            (fun permutation => allocation N algorithm permutation round bidder')

/--
Family-level relabeling version of the Section 7 lower-bound certificate. This
keeps the input relabeling equivalence and pointwise allocation identity
explicit; later observed-prefix certificates derive those fields from the
online-information model.
-/
structure BMatchingTheorem9RelabelSymmetricPointwiseFamilyCertificate
    (Algorithm : ℕ → Type*)
    [∀ N, Fintype (Algorithm N)] [∀ N, DecidableEq (Algorithm N)] where
  normalizedRevenue :
    (N : ℕ) → Algorithm N → Equiv.Perm (Fin N) → ℝ
  allocation :
    (N : ℕ) → Algorithm N → Equiv.Perm (Fin N) → Fin N → Fin N → ℝ
  normalizedRevenue_le_cappedAllocationSpend :
    ∀ N algorithm permutation,
      normalizedRevenue N algorithm permutation ≤
        (∑ bidder : Fin N,
          min 1
            (∑ round : Fin N,
              allocation N algorithm permutation round bidder)) /
          (N : ℝ)
  allocation_zero_of_ineligible :
    ∀ N algorithm permutation (round bidder : Fin N),
      ¬ (round : ℕ) ≤ (bidder : ℕ) →
        allocation N algorithm permutation round bidder = 0
  round_allocation_sum_le_one :
    ∀ N algorithm permutation (round : Fin N),
      (∑ bidder ∈ theorem9EligibleBidders N round,
        allocation N algorithm permutation round bidder) ≤ 1
  relabelInput :
    (N : ℕ) → Fin N → Fin N → Fin N →
      Equiv.Perm (Fin N) ≃ Equiv.Perm (Fin N)
  allocation_eq_of_relabel_eligible :
    ∀ N algorithm (round bidder bidder' : Fin N),
      (round : ℕ) ≤ (bidder : ℕ) →
      (round : ℕ) ≤ (bidder' : ℕ) →
      ∀ permutation,
        allocation N algorithm
            (relabelInput N round bidder bidder' permutation)
            round bidder =
          allocation N algorithm permutation round bidder'

/--
Family-level observed-prefix form of the Section 7 online-information
argument. This packages deterministic allocation functions that depend on a
permutation instance only through the hard instance prefix revealed so far.
-/
structure BMatchingTheorem9ObservedPrefixFamilyCertificate
    (Algorithm : ℕ → Type*)
    [∀ N, Fintype (Algorithm N)] [∀ N, DecidableEq (Algorithm N)] where
  normalizedRevenue :
    (N : ℕ) → Algorithm N → Equiv.Perm (Fin N) → ℝ
  allocation :
    (N : ℕ) → Algorithm N → Equiv.Perm (Fin N) → Fin N → Fin N → ℝ
  prefixAllocation :
    (N : ℕ) → Algorithm N → (Fin N → Finset (Fin N)) →
      Fin N → Fin N → ℝ
  allocation_eq_prefix :
    ∀ N algorithm permutation round bidder,
      allocation N algorithm permutation round bidder =
        prefixAllocation N algorithm
          (theorem9ObservedPrefix N permutation round)
          round (permutation bidder)
  normalizedRevenue_le_cappedAllocationSpend :
    ∀ N algorithm permutation,
      normalizedRevenue N algorithm permutation ≤
        (∑ bidder : Fin N,
          min 1
            (∑ round : Fin N,
              allocation N algorithm permutation round bidder)) /
          (N : ℝ)
  allocation_zero_of_ineligible :
    ∀ N algorithm permutation (round bidder : Fin N),
      ¬ (round : ℕ) ≤ (bidder : ℕ) →
        allocation N algorithm permutation round bidder = 0
  round_allocation_sum_le_one :
    ∀ N algorithm permutation (round : Fin N),
      (∑ bidder ∈ theorem9EligibleBidders N round,
        allocation N algorithm permutation round bidder) ≤ 1

/--
Family-level feasible observed-prefix allocation certificate. It packages
allocation rules that act on actual bidder labels from the visible prefix and
are directly feasible in every visible round.
-/
structure BMatchingTheorem9FeasibleObservedPrefixFamilyCertificate
    (Algorithm : ℕ → Type*)
    [∀ N, Fintype (Algorithm N)] [∀ N, DecidableEq (Algorithm N)] where
  normalizedRevenue :
    (N : ℕ) → Algorithm N → Equiv.Perm (Fin N) → ℝ
  prefixAllocation :
    (N : ℕ) → Algorithm N → (Fin N → Finset (Fin N)) →
      Fin N → Fin N → ℝ
  normalizedRevenue_le_cappedPrefixAllocationSpend :
    ∀ N algorithm permutation,
      normalizedRevenue N algorithm permutation ≤
        (∑ bidder : Fin N,
          min 1
            (∑ round : Fin N,
              prefixAllocation N algorithm
                (theorem9ObservedPrefix N permutation round)
                round (permutation bidder))) /
          (N : ℝ)
  prefixAllocation_zero_of_not_visible :
    ∀ N algorithm obs round bidder,
      bidder ∉ obs round →
        prefixAllocation N algorithm obs round bidder = 0
  prefixAllocation_sum_le_one :
    ∀ N algorithm obs round,
      (∑ bidder ∈ obs round,
        prefixAllocation N algorithm obs round bidder) ≤ 1

/--
Family of feasible prefix allocation rules for the Section 7 hard instance.
The normalized payoff is defined by the capped spend expression itself, so this
interface has no separate revenue-bound field.
-/
structure BMatchingTheorem9FeasiblePrefixRuleFamily
    (Algorithm : ℕ → Type*)
    [∀ N, Fintype (Algorithm N)] [∀ N, DecidableEq (Algorithm N)] where
  prefixAllocation :
    (N : ℕ) → Algorithm N → (Fin N → Finset (Fin N)) →
      Fin N → Fin N → ℝ
  prefixAllocation_zero_of_not_visible :
    ∀ N algorithm obs round bidder,
      bidder ∉ obs round →
        prefixAllocation N algorithm obs round bidder = 0
  prefixAllocation_sum_le_one :
    ∀ N algorithm obs round,
      (∑ bidder ∈ obs round,
        prefixAllocation N algorithm obs round bidder) ≤ 1

/-- A deterministic integral algorithm chooses at most one actual bidder from the visible prefix. -/
abbrev BMatchingIntegralPrefixChoice (N : ℕ) :=
  (Fin N → Finset (Fin N)) → Fin N → Option (Fin N)

/-- Feasibility for an integral prefix choice rule: chosen bidders must be visible. -/
def BMatchingIntegralPrefixChoice.Feasible
    {N : ℕ} (choice : BMatchingIntegralPrefixChoice N) : Prop :=
  ∀ obs round bidder, choice obs round = some bidder → bidder ∈ obs round

/--
Classical instances for the concrete finite integral-prefix choice types used in the
AdWords lower-bound bridge.
-/
noncomputable instance (N : ℕ) : DecidablePred (BMatchingIntegralPrefixChoice.Feasible (N := N)) := by
  classical
  exact Classical.decPred _

instance (N : ℕ) : Fintype (BMatchingIntegralPrefixChoice N) := by
  infer_instance

instance (N : ℕ) : DecidableEq (BMatchingIntegralPrefixChoice N) := by
  infer_instance

/-- Concrete deterministic integral algorithms for the Section 7 hard instance. -/
abbrev BMatchingIntegralPrefixAlgorithm (N : ℕ) :=
  { choice : BMatchingIntegralPrefixChoice N //
    BMatchingIntegralPrefixChoice.Feasible choice }

noncomputable instance (N : ℕ) : Fintype (BMatchingIntegralPrefixAlgorithm N) := by
  infer_instance

noncomputable instance (N : ℕ) : DecidableEq (BMatchingIntegralPrefixAlgorithm N) := by
  infer_instance

namespace BMatchingIntegralPrefixAlgorithm

/-- The `0/1` allocation induced by an integral prefix choice rule. -/
noncomputable def prefixAllocation {N : ℕ}
    (algorithm : BMatchingIntegralPrefixAlgorithm N)
    (obs : Fin N → Finset (Fin N)) (round bidder : Fin N) : ℝ :=
  if algorithm.1 obs round = some bidder then 1 else 0

theorem prefixAllocation_zero_of_not_visible {N : ℕ}
    (algorithm : BMatchingIntegralPrefixAlgorithm N)
    (obs : Fin N → Finset (Fin N)) (round bidder : Fin N)
    (hnot : bidder ∉ obs round) :
    prefixAllocation algorithm obs round bidder = 0 := by
  unfold prefixAllocation
  by_cases hchoice : algorithm.1 obs round = some bidder
  · exact False.elim (hnot (algorithm.2 obs round bidder hchoice))
  · simp [hchoice]

theorem prefixAllocation_sum_le_one {N : ℕ}
    (algorithm : BMatchingIntegralPrefixAlgorithm N)
    (obs : Fin N → Finset (Fin N)) (round : Fin N) :
    (∑ bidder ∈ obs round,
      prefixAllocation algorithm obs round bidder) ≤ 1 := by
  unfold prefixAllocation
  cases hchoice : algorithm.1 obs round with
  | none =>
      simp
  | some chosen =>
      have hchosen : chosen ∈ obs round :=
        algorithm.2 obs round chosen hchoice
      have hsum :
          (∑ bidder ∈ obs round,
            (if some chosen = some bidder then (1 : ℝ) else 0)) = 1 := by
        simpa [hchosen] using
          (Finset.sum_ite_eq' (obs round) chosen (fun _ => (1 : ℝ)))
      exact le_of_eq hsum

end BMatchingIntegralPrefixAlgorithm

/--
Family-level round-allocation certificate with the harmonic side represented
by the paper's finite layer-count estimate instead of an opaque eventual
assumption.
-/
structure BMatchingTheorem9LayerCountFamilyCertificate
    (Algorithm : ℕ → Type*)
    [∀ N, Fintype (Algorithm N)] [∀ N, DecidableEq (Algorithm N)] where
  normalizedRevenue :
    (N : ℕ) → Algorithm N → Equiv.Perm (Fin N) → ℝ
  expectedRoundBidderAllocation :
    (N : ℕ) → Algorithm N → Fin N → Fin N → ℝ
  deterministicAverage_le_cappedExpectedSpend :
    ∀ N algorithm,
      pmfExp (uniformPermutationDistribution N)
          (fun permutation => normalizedRevenue N algorithm permutation) ≤
        (∑ bidder : Fin N,
          min 1
            (∑ round : Fin N,
              expectedRoundBidderAllocation N algorithm round bidder)) /
          (N : ℝ)
  expectedRoundBidderAllocation_le :
    ∀ N algorithm round bidder,
      expectedRoundBidderAllocation N algorithm round bidder ≤
        if (round : ℕ) ≤ (bidder : ℕ) then
          1 / ((N - (round : ℕ) : ℕ) : ℝ)
        else
          0
  layer_count_bound :
    ∀ N : ℕ, 0 < N → theorem9HarmonicLayerCountBound N N

/--
Family-level pointwise-allocation certificate with the harmonic side supplied
by finite layer-count bounds.
-/
structure BMatchingTheorem9PointwiseLayerCountFamilyCertificate
    (Algorithm : ℕ → Type*)
    [∀ N, Fintype (Algorithm N)] [∀ N, DecidableEq (Algorithm N)] where
  normalizedRevenue :
    (N : ℕ) → Algorithm N → Equiv.Perm (Fin N) → ℝ
  allocation :
    (N : ℕ) → Algorithm N → Equiv.Perm (Fin N) → Fin N → Fin N → ℝ
  normalizedRevenue_le_cappedAllocationSpend :
    ∀ N algorithm permutation,
      normalizedRevenue N algorithm permutation ≤
        (∑ bidder : Fin N,
          min 1
            (∑ round : Fin N,
              allocation N algorithm permutation round bidder)) /
          (N : ℝ)
  expectedAllocation_le :
    ∀ N algorithm round bidder,
      pmfExp (uniformPermutationDistribution N)
          (fun permutation => allocation N algorithm permutation round bidder) ≤
        if (round : ℕ) ≤ (bidder : ℕ) then
          1 / ((N - (round : ℕ) : ℕ) : ℝ)
        else
          0
  layer_count_bound :
    ∀ N : ℕ, 0 < N → theorem9HarmonicLayerCountBound N N

/--
Family-level symmetry/capacity certificate with the harmonic side supplied by
finite layer-count bounds.
-/
structure BMatchingTheorem9SymmetricPointwiseLayerCountFamilyCertificate
    (Algorithm : ℕ → Type*)
    [∀ N, Fintype (Algorithm N)] [∀ N, DecidableEq (Algorithm N)] where
  normalizedRevenue :
    (N : ℕ) → Algorithm N → Equiv.Perm (Fin N) → ℝ
  allocation :
    (N : ℕ) → Algorithm N → Equiv.Perm (Fin N) → Fin N → Fin N → ℝ
  normalizedRevenue_le_cappedAllocationSpend :
    ∀ N algorithm permutation,
      normalizedRevenue N algorithm permutation ≤
        (∑ bidder : Fin N,
          min 1
            (∑ round : Fin N,
              allocation N algorithm permutation round bidder)) /
          (N : ℝ)
  allocation_zero_of_ineligible :
    ∀ N algorithm permutation (round bidder : Fin N),
      ¬ (round : ℕ) ≤ (bidder : ℕ) →
        allocation N algorithm permutation round bidder = 0
  round_allocation_sum_le_one :
    ∀ N algorithm permutation (round : Fin N),
      (∑ bidder ∈ theorem9EligibleBidders N round,
        allocation N algorithm permutation round bidder) ≤ 1
  expectedAllocation_eq_of_eligible :
    ∀ N algorithm (round bidder bidder' : Fin N),
      (round : ℕ) ≤ (bidder : ℕ) →
      (round : ℕ) ≤ (bidder' : ℕ) →
        pmfExp (uniformPermutationDistribution N)
            (fun permutation => allocation N algorithm permutation round bidder) =
          pmfExp (uniformPermutationDistribution N)
            (fun permutation => allocation N algorithm permutation round bidder')
  layer_count_bound :
    ∀ N : ℕ, 0 < N → theorem9HarmonicLayerCountBound N N

namespace BMatchingPermutationLowerBoundCertificate

variable {N : ℕ} {Algorithm : Type*}

/-- Convert the paper-specific permutation certificate into the generic Yao certificate. -/
noncomputable def toYaoCertificate
    (C : BMatchingPermutationLowerBoundCertificate N Algorithm) :
    BMatchingYaoLowerBoundCertificate Algorithm (Equiv.Perm (Fin N)) where
  distribution := uniformPermutationDistribution N
  normalizedRevenue := C.normalizedRevenue
  deterministicAverage_le := C.deterministicAverage_le

theorem no_randomized_algorithm_beats_msvvRatio
    [Fintype Algorithm] [DecidableEq Algorithm]
    (C : BMatchingPermutationLowerBoundCertificate N Algorithm)
    (randomizedAlgorithm : PMF Algorithm) :
    ¬ ∀ permutation,
      AdWordsInstance.msvvRatio <
        pmfExp randomizedAlgorithm
          (fun algorithm => C.normalizedRevenue algorithm permutation) := by
  exact
    bMatching_no_randomized_algorithm_beats_msvvRatio_of_certificate
      C.toYaoCertificate randomizedAlgorithm

end BMatchingPermutationLowerBoundCertificate

namespace BMatchingPermutationRevenueBoundCertificate

variable {N : ℕ} {Algorithm : Type*} {ratio : ℝ}

/--
Convert the explicit finite revenue-bound certificate into the permutation
lower-bound certificate used by Yao's lemma.
-/
noncomputable def toPermutationLowerBoundCertificate
    (C : BMatchingPermutationRevenueBoundCertificate N Algorithm ratio) :
    RandomizedLowerBoundCertificate Algorithm (Equiv.Perm (Fin N)) ratio where
  normalizedRevenue := C.normalizedRevenue
  distribution := uniformPermutationDistribution N
  deterministicAverage_le := by
    intro algorithm
    exact (C.deterministicAverage_le_revenueBound algorithm).trans
      C.revenueBound_le_ratio

theorem no_randomized_algorithm_beats_ratio
    [Fintype Algorithm] [DecidableEq Algorithm]
    (C : BMatchingPermutationRevenueBoundCertificate N Algorithm ratio)
    (randomizedAlgorithm : PMF Algorithm) :
    ¬ ∀ permutation,
      ratio <
        pmfExp randomizedAlgorithm
          (fun algorithm => C.normalizedRevenue algorithm permutation) := by
  exact
    C.toPermutationLowerBoundCertificate.no_strictly_better_randomized_algorithm
      randomizedAlgorithm

end BMatchingPermutationRevenueBoundCertificate

namespace BMatchingPointwiseAllocationRevenueCertificate

variable {N : ℕ} {Algorithm : Type*} {ratio : ℝ}

/--
Convert realized per-permutation allocations into the expected round-allocation
certificate. The proof is pure finite-expectation algebra: monotonicity,
linearity over finite sums, and the bound
`E[min 1 X] <= min 1 (E[X])`.
-/
noncomputable def toRoundAllocationRevenueCertificate
    (C : BMatchingPointwiseAllocationRevenueCertificate N Algorithm ratio) :
    BMatchingRoundAllocationRevenueCertificate N Algorithm ratio where
  normalizedRevenue := C.normalizedRevenue
  expectedRoundBidderAllocation := fun algorithm round bidder =>
    pmfExp (uniformPermutationDistribution N)
      (fun permutation => C.allocation algorithm permutation round bidder)
  deterministicAverage_le_cappedExpectedSpend := by
    intro algorithm
    let μ := uniformPermutationDistribution N
    let cappedSpend := fun permutation =>
      ∑ bidder : Fin N,
        min 1
          (∑ round : Fin N,
            C.allocation algorithm permutation round bidder)
    have hpoint :
        pmfExp μ (fun permutation => C.normalizedRevenue algorithm permutation) ≤
          pmfExp μ (fun permutation => cappedSpend permutation / (N : ℝ)) :=
      pmfExp_le_pmfExp_of_forall_le μ
        (fun permutation => C.normalizedRevenue algorithm permutation)
        (fun permutation => cappedSpend permutation / (N : ℝ))
        (C.normalizedRevenue_le_cappedAllocationSpend algorithm)
    have hdiv :
        pmfExp μ (fun permutation => cappedSpend permutation / (N : ℝ)) =
          pmfExp μ cappedSpend / (N : ℝ) := by
      simpa [div_eq_mul_inv] using
        (pmfExp_mul_const μ cappedSpend ((N : ℝ)⁻¹))
    have hsumexp :
        pmfExp μ cappedSpend =
          ∑ bidder : Fin N,
            pmfExp μ
              (fun permutation =>
                min 1
                  (∑ round : Fin N,
                    C.allocation algorithm permutation round bidder)) := by
      simpa [cappedSpend] using
        (pmfExp_finset_sum μ (Finset.univ : Finset (Fin N))
          (fun bidder permutation =>
            min 1
              (∑ round : Fin N,
                C.allocation algorithm permutation round bidder)))
    have hbidder :
        ∀ bidder : Fin N,
          pmfExp μ
              (fun permutation =>
                min 1
                  (∑ round : Fin N,
                    C.allocation algorithm permutation round bidder)) ≤
            min 1
              (∑ round : Fin N,
                pmfExp μ
                  (fun permutation =>
                    C.allocation algorithm permutation round bidder)) := by
      intro bidder
      calc
        pmfExp μ
            (fun permutation =>
              min 1
                (∑ round : Fin N,
                  C.allocation algorithm permutation round bidder))
            ≤
          min 1
            (pmfExp μ
              (fun permutation =>
                ∑ round : Fin N,
                  C.allocation algorithm permutation round bidder)) :=
            pmfExp_min_one_le_min_one_pmfExp μ
              (fun permutation =>
                ∑ round : Fin N,
                  C.allocation algorithm permutation round bidder)
        _ =
          min 1
            (∑ round : Fin N,
              pmfExp μ
                (fun permutation =>
                  C.allocation algorithm permutation round bidder)) := by
            simp [pmfExp_finset_sum]
    have hsum :
        pmfExp μ cappedSpend ≤
          ∑ bidder : Fin N,
            min 1
              (∑ round : Fin N,
                pmfExp μ
                  (fun permutation =>
                    C.allocation algorithm permutation round bidder)) := by
      rw [hsumexp]
      exact Finset.sum_le_sum fun bidder _ => hbidder bidder
    have hden : 0 ≤ (N : ℝ) := by exact_mod_cast (Nat.zero_le N)
    have hcap :
        pmfExp μ (fun permutation => cappedSpend permutation / (N : ℝ)) ≤
          (∑ bidder : Fin N,
            min 1
              (∑ round : Fin N,
                pmfExp μ
                  (fun permutation =>
                    C.allocation algorithm permutation round bidder))) /
            (N : ℝ) := by
      rw [hdiv]
      exact div_le_div_of_nonneg_right hsum hden
    exact hpoint.trans hcap
  expectedRoundBidderAllocation_le := C.expectedAllocation_le
  revenueBound_le_ratio := C.revenueBound_le_ratio

end BMatchingPointwiseAllocationRevenueCertificate

namespace BMatchingRelabelSymmetricPointwiseAllocationRevenueCertificate

variable {N : ℕ} {Algorithm : Type*} {ratio : ℝ}

/--
Pointwise relabeling under the uniform permutation distribution implies the
expected-allocation symmetry certificate.
-/
noncomputable def toSymmetricPointwiseAllocationRevenueCertificate
    (C : BMatchingRelabelSymmetricPointwiseAllocationRevenueCertificate
      N Algorithm ratio) :
    BMatchingSymmetricPointwiseAllocationRevenueCertificate
      N Algorithm ratio where
  normalizedRevenue := C.normalizedRevenue
  allocation := C.allocation
  normalizedRevenue_le_cappedAllocationSpend :=
    C.normalizedRevenue_le_cappedAllocationSpend
  allocation_zero_of_ineligible := C.allocation_zero_of_ineligible
  round_allocation_sum_le_one := C.round_allocation_sum_le_one
  expectedAllocation_eq_of_eligible := by
    intro algorithm round bidder bidder' hbidder hbidder'
    exact
      uniformPermutationExpectation_eq_of_relabel
        (C.relabelInput round bidder bidder')
        (fun permutation =>
          C.allocation_eq_of_relabel_eligible
            algorithm round bidder bidder' hbidder hbidder' permutation)
  revenueBound_le_ratio := C.revenueBound_le_ratio

end BMatchingRelabelSymmetricPointwiseAllocationRevenueCertificate

namespace BMatchingObservedPrefixAllocationRevenueCertificate

variable {N : ℕ} {Algorithm : Type*} {ratio : ℝ}

/--
Observed-prefix dependence implies the pointwise relabeling certificate: a
swap inside the current suffix leaves the observed prefix unchanged, and the
position's actual bidder label is swapped accordingly.
-/
noncomputable def toRelabelSymmetricPointwiseAllocationRevenueCertificate
    (C : BMatchingObservedPrefixAllocationRevenueCertificate
      N Algorithm ratio) :
    BMatchingRelabelSymmetricPointwiseAllocationRevenueCertificate
      N Algorithm ratio where
  normalizedRevenue := C.normalizedRevenue
  allocation := C.allocation
  normalizedRevenue_le_cappedAllocationSpend :=
    C.normalizedRevenue_le_cappedAllocationSpend
  allocation_zero_of_ineligible := C.allocation_zero_of_ineligible
  round_allocation_sum_le_one := C.round_allocation_sum_le_one
  relabelInput := fun _ bidder bidder' =>
    Equiv.mulRight (Equiv.swap bidder bidder')
  allocation_eq_of_relabel_eligible := by
    intro algorithm round bidder bidder' hbidder hbidder' permutation
    let swap : Equiv.Perm (Fin N) := Equiv.swap bidder bidder'
    calc
      C.allocation algorithm ((Equiv.mulRight swap) permutation) round bidder =
          C.prefixAllocation algorithm
            (theorem9ObservedPrefix N
              ((Equiv.mulRight swap) permutation) round)
            round (((Equiv.mulRight swap) permutation) bidder) := by
            exact C.allocation_eq_prefix algorithm
              ((Equiv.mulRight swap) permutation) round bidder
      _ =
          C.prefixAllocation algorithm
            (theorem9ObservedPrefix N permutation round)
            round (permutation bidder') := by
            have hprefix' :
                theorem9ObservedPrefix N
                    (permutation * Equiv.swap bidder bidder') round =
                  theorem9ObservedPrefix N permutation round :=
              theorem9ObservedPrefix_mul_swap_eq
                (N := N) (round := round) (bidder := bidder)
                (bidder' := bidder') hbidder hbidder' permutation
            simpa [swap, Equiv.coe_mulRight, Equiv.Perm.mul_apply] using
              congrArg
                (fun pref =>
                  C.prefixAllocation algorithm pref round
                    (permutation bidder')) hprefix'
      _ = C.allocation algorithm permutation round bidder' := by
            exact (C.allocation_eq_prefix algorithm permutation round bidder').symm
  revenueBound_le_ratio := C.revenueBound_le_ratio

end BMatchingObservedPrefixAllocationRevenueCertificate

namespace BMatchingFeasibleObservedPrefixAllocationRevenueCertificate

variable {N : ℕ} {Algorithm : Type*} {ratio : ℝ}

/--
Convert a feasible actual-bidder prefix allocation rule into the
observed-prefix position-allocation certificate.
-/
noncomputable def toObservedPrefixAllocationRevenueCertificate
    (C : BMatchingFeasibleObservedPrefixAllocationRevenueCertificate
      N Algorithm ratio) :
    BMatchingObservedPrefixAllocationRevenueCertificate
      N Algorithm ratio where
  normalizedRevenue := C.normalizedRevenue
  allocation := fun algorithm permutation round bidder =>
    C.prefixAllocation algorithm
      (theorem9ObservedPrefix N permutation round)
      round (permutation bidder)
  prefixAllocation := C.prefixAllocation
  allocation_eq_prefix := by
    intro algorithm permutation round bidder
    rfl
  normalizedRevenue_le_cappedAllocationSpend :=
    C.normalizedRevenue_le_cappedPrefixAllocationSpend
  allocation_zero_of_ineligible := by
    intro algorithm permutation round bidder hnot
    exact
      C.prefixAllocation_zero_of_not_visible algorithm
        (theorem9ObservedPrefix N permutation round) round
        (permutation bidder)
        (by
          simp [theorem9ObservedPrefix,
            theorem9ActualEligibleBidders_not_mem_of_not_eligible hnot])
  round_allocation_sum_le_one := by
    intro algorithm permutation round
    let obs := theorem9ObservedPrefix N permutation round
    have hcap := C.prefixAllocation_sum_le_one algorithm obs round
    have hcurrent :
        obs round = theorem9ActualEligibleBidders N permutation round := by
      simp [obs, theorem9ObservedPrefix]
    have hcapActual :
        (∑ bidder ∈ theorem9ActualEligibleBidders N permutation round,
          C.prefixAllocation algorithm obs round bidder) ≤ 1 := by
      simpa [hcurrent] using hcap
    have hsum :=
      theorem9ActualEligibleBidders_sum_eq permutation round
        (fun bidder => C.prefixAllocation algorithm obs round bidder)
    calc
      (∑ bidder ∈ theorem9EligibleBidders N round,
        C.prefixAllocation algorithm obs round (permutation bidder))
          =
        (∑ bidder ∈ theorem9ActualEligibleBidders N permutation round,
          C.prefixAllocation algorithm obs round bidder) := by
          exact hsum.symm
      _ ≤ 1 := hcapActual
  revenueBound_le_ratio := C.revenueBound_le_ratio

end BMatchingFeasibleObservedPrefixAllocationRevenueCertificate

namespace BMatchingSymmetricPointwiseAllocationRevenueCertificate

variable {N : ℕ} {Algorithm : Type*} {ratio : ℝ}

/--
Capacity plus uniform-position symmetry implies the pointwise allocation
certificate's expected allocation field.
-/
noncomputable def toPointwiseAllocationRevenueCertificate
    (C : BMatchingSymmetricPointwiseAllocationRevenueCertificate
      N Algorithm ratio) :
    BMatchingPointwiseAllocationRevenueCertificate N Algorithm ratio where
  normalizedRevenue := C.normalizedRevenue
  allocation := C.allocation
  normalizedRevenue_le_cappedAllocationSpend :=
    C.normalizedRevenue_le_cappedAllocationSpend
  expectedAllocation_le := by
    intro algorithm round bidder
    let μ := uniformPermutationDistribution N
    by_cases helig : (round : ℕ) ≤ (bidder : ℕ)
    · have htotal :
          (∑ bidder' ∈ theorem9EligibleBidders N round,
            pmfExp μ
              (fun permutation =>
                C.allocation algorithm permutation round bidder')) ≤ 1 := by
        have hpoint :
            pmfExp μ
                (fun permutation =>
                  ∑ bidder' ∈ theorem9EligibleBidders N round,
                    C.allocation algorithm permutation round bidder') ≤
              1 :=
          pmfExp_le_of_forall_le μ
            (fun permutation =>
              ∑ bidder' ∈ theorem9EligibleBidders N round,
                C.allocation algorithm permutation round bidder')
            1
            (fun permutation =>
              C.round_allocation_sum_le_one algorithm permutation round)
        simpa [pmfExp_finset_sum] using hpoint
      have hsame :
          ∀ bidder' ∈ theorem9EligibleBidders N round,
            pmfExp μ
              (fun permutation =>
                C.allocation algorithm permutation round bidder') =
              pmfExp μ
                (fun permutation =>
                  C.allocation algorithm permutation round bidder) := by
        intro bidder' hbidder'
        exact
          C.expectedAllocation_eq_of_eligible algorithm round bidder' bidder
            ((mem_theorem9EligibleBidders N round bidder').mp hbidder')
            helig
      have hmul :
          ((theorem9EligibleBidders N round).card : ℝ) *
              pmfExp μ
                (fun permutation =>
                  C.allocation algorithm permutation round bidder) ≤
            1 := by
        calc
          ((theorem9EligibleBidders N round).card : ℝ) *
              pmfExp μ
                (fun permutation =>
                  C.allocation algorithm permutation round bidder)
              =
            ∑ bidder' ∈ theorem9EligibleBidders N round,
              pmfExp μ
                (fun permutation =>
                  C.allocation algorithm permutation round bidder) := by
              simp [nsmul_eq_mul]
          _ =
            ∑ bidder' ∈ theorem9EligibleBidders N round,
              pmfExp μ
                (fun permutation =>
                  C.allocation algorithm permutation round bidder') := by
              refine Finset.sum_congr rfl ?_
              intro bidder' hbidder'
              exact (hsame bidder' hbidder').symm
          _ ≤ 1 := htotal
      have hcard_pos :
          0 < ((theorem9EligibleBidders N round).card : ℝ) := by
        rw [theorem9EligibleBidders_card]
        exact_mod_cast (Nat.sub_pos_of_lt round.isLt)
      have hle_card :
          pmfExp μ
              (fun permutation =>
                C.allocation algorithm permutation round bidder) ≤
            1 / ((theorem9EligibleBidders N round).card : ℝ) := by
        rw [le_div_iff₀ hcard_pos]
        simpa [mul_comm] using hmul
      simpa [helig, theorem9EligibleBidders_card] using hle_card
    · have hzero :
          (fun permutation =>
            C.allocation algorithm permutation round bidder) =
          (fun _ => 0) := by
        funext permutation
        exact C.allocation_zero_of_ineligible algorithm permutation round bidder
          helig
      simp [helig, hzero]
  revenueBound_le_ratio := C.revenueBound_le_ratio

end BMatchingSymmetricPointwiseAllocationRevenueCertificate

namespace BMatchingRoundAllocationRevenueCertificate

variable {N : ℕ} {Algorithm : Type*} {ratio : ℝ}

/--
The round-allocation inequalities imply the paper's harmonic revenue-bound
certificate.
-/
noncomputable def toRevenueBoundCertificate
    (C : BMatchingRoundAllocationRevenueCertificate N Algorithm ratio) :
    BMatchingPermutationRevenueBoundCertificate N Algorithm ratio where
  normalizedRevenue := C.normalizedRevenue
  deterministicAverage_le_revenueBound := by
    intro algorithm
    have hbidder :
        ∀ bidder : Fin N,
          min 1
              (∑ round : Fin N,
                C.expectedRoundBidderAllocation algorithm round bidder) ≤
            theorem9BidderSpendUpperBound N bidder := by
      intro bidder
      unfold theorem9BidderSpendUpperBound
      exact min_le_min_left 1
        (Finset.sum_le_sum fun round _ =>
          C.expectedRoundBidderAllocation_le algorithm round bidder)
    have hsum :
        (∑ bidder : Fin N,
          min 1
            (∑ round : Fin N,
              C.expectedRoundBidderAllocation algorithm round bidder)) ≤
        ∑ bidder : Fin N, theorem9BidderSpendUpperBound N bidder :=
      Finset.sum_le_sum fun bidder _ => hbidder bidder
    have hden : 0 ≤ (N : ℝ) := by exact_mod_cast (Nat.zero_le N)
    exact (C.deterministicAverage_le_cappedExpectedSpend algorithm).trans
      (div_le_div_of_nonneg_right hsum hden)
  revenueBound_le_ratio := C.revenueBound_le_ratio

theorem no_randomized_algorithm_beats_ratio
    [Fintype Algorithm] [DecidableEq Algorithm]
    (C : BMatchingRoundAllocationRevenueCertificate N Algorithm ratio)
    (randomizedAlgorithm : PMF Algorithm) :
    ¬ ∀ permutation,
      ratio <
        pmfExp randomizedAlgorithm
          (fun algorithm => C.normalizedRevenue algorithm permutation) := by
  exact
    C.toRevenueBoundCertificate.no_randomized_algorithm_beats_ratio
      randomizedAlgorithm

end BMatchingRoundAllocationRevenueCertificate

namespace BMatchingPointwiseAllocationRevenueCertificate

variable {N : ℕ} {Algorithm : Type*} {ratio : ℝ}

theorem no_randomized_algorithm_beats_ratio
    [Fintype Algorithm] [DecidableEq Algorithm]
    (C : BMatchingPointwiseAllocationRevenueCertificate N Algorithm ratio)
    (randomizedAlgorithm : PMF Algorithm) :
    ¬ ∀ permutation,
      ratio <
        pmfExp randomizedAlgorithm
          (fun algorithm => C.normalizedRevenue algorithm permutation) := by
  exact
    C.toRoundAllocationRevenueCertificate.no_randomized_algorithm_beats_ratio
      randomizedAlgorithm

end BMatchingPointwiseAllocationRevenueCertificate

namespace BMatchingSymmetricPointwiseAllocationRevenueCertificate

variable {N : ℕ} {Algorithm : Type*} {ratio : ℝ}

theorem no_randomized_algorithm_beats_ratio
    [Fintype Algorithm] [DecidableEq Algorithm]
    (C : BMatchingSymmetricPointwiseAllocationRevenueCertificate
      N Algorithm ratio)
    (randomizedAlgorithm : PMF Algorithm) :
    ¬ ∀ permutation,
      ratio <
        pmfExp randomizedAlgorithm
          (fun algorithm => C.normalizedRevenue algorithm permutation) := by
  exact
    C.toPointwiseAllocationRevenueCertificate.no_randomized_algorithm_beats_ratio
      randomizedAlgorithm

end BMatchingSymmetricPointwiseAllocationRevenueCertificate

namespace BMatchingRelabelSymmetricPointwiseAllocationRevenueCertificate

variable {N : ℕ} {Algorithm : Type*} {ratio : ℝ}

theorem no_randomized_algorithm_beats_ratio
    [Fintype Algorithm] [DecidableEq Algorithm]
    (C : BMatchingRelabelSymmetricPointwiseAllocationRevenueCertificate
      N Algorithm ratio)
    (randomizedAlgorithm : PMF Algorithm) :
    ¬ ∀ permutation,
      ratio <
        pmfExp randomizedAlgorithm
          (fun algorithm => C.normalizedRevenue algorithm permutation) := by
  exact
    C.toSymmetricPointwiseAllocationRevenueCertificate
      |>.no_randomized_algorithm_beats_ratio randomizedAlgorithm

end BMatchingRelabelSymmetricPointwiseAllocationRevenueCertificate

namespace BMatchingObservedPrefixAllocationRevenueCertificate

variable {N : ℕ} {Algorithm : Type*} {ratio : ℝ}

theorem no_randomized_algorithm_beats_ratio
    [Fintype Algorithm] [DecidableEq Algorithm]
    (C : BMatchingObservedPrefixAllocationRevenueCertificate
      N Algorithm ratio)
    (randomizedAlgorithm : PMF Algorithm) :
    ¬ ∀ permutation,
      ratio <
        pmfExp randomizedAlgorithm
          (fun algorithm => C.normalizedRevenue algorithm permutation) := by
  exact
    C.toRelabelSymmetricPointwiseAllocationRevenueCertificate
      |>.no_randomized_algorithm_beats_ratio randomizedAlgorithm

end BMatchingObservedPrefixAllocationRevenueCertificate

namespace BMatchingFeasibleObservedPrefixAllocationRevenueCertificate

variable {N : ℕ} {Algorithm : Type*} {ratio : ℝ}

theorem no_randomized_algorithm_beats_ratio
    [Fintype Algorithm] [DecidableEq Algorithm]
    (C : BMatchingFeasibleObservedPrefixAllocationRevenueCertificate
      N Algorithm ratio)
    (randomizedAlgorithm : PMF Algorithm) :
    ¬ ∀ permutation,
      ratio <
        pmfExp randomizedAlgorithm
          (fun algorithm => C.normalizedRevenue algorithm permutation) := by
  exact
    C.toObservedPrefixAllocationRevenueCertificate
      |>.no_randomized_algorithm_beats_ratio randomizedAlgorithm

end BMatchingFeasibleObservedPrefixAllocationRevenueCertificate

/--
Asymptotic Section 7 wrapper. If the round-allocation calculation is available
for every market size and the explicit harmonic cap is eventually within every
positive additive error of `msvvRatio`, then no randomized algorithm family can
beat `msvvRatio + δ` on every large permutation instance.
-/
theorem theorem9_eventually_no_randomized_algorithm_beats_msvvRatio_add_delta
    {Algorithm : ℕ → Type*}
    [∀ N, Fintype (Algorithm N)] [∀ N, DecidableEq (Algorithm N)]
    (normalizedRevenue :
      (N : ℕ) → Algorithm N → Equiv.Perm (Fin N) → ℝ)
    (expectedRoundBidderAllocation :
      (N : ℕ) → Algorithm N → Fin N → Fin N → ℝ)
    (haverage :
      ∀ N algorithm,
        pmfExp (uniformPermutationDistribution N)
            (fun permutation => normalizedRevenue N algorithm permutation) ≤
          (∑ bidder : Fin N,
            min 1
              (∑ round : Fin N,
                expectedRoundBidderAllocation N algorithm round bidder)) /
            (N : ℝ))
    (hexpected_le :
      ∀ N algorithm round bidder,
        expectedRoundBidderAllocation N algorithm round bidder ≤
          if (round : ℕ) ≤ (bidder : ℕ) then
            1 / ((N - (round : ℕ) : ℕ) : ℝ)
          else
            0)
    (hharmonic :
      ∀ δ : ℝ, 0 < δ →
        ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
          theorem9NormalizedRevenueUpperBound N ≤
            AdWordsInstance.msvvRatio + δ) :
    ∀ δ : ℝ, 0 < δ →
      ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
        ∀ randomizedAlgorithm : PMF (Algorithm N),
          ¬ ∀ permutation,
            AdWordsInstance.msvvRatio + δ <
              pmfExp randomizedAlgorithm
                (fun algorithm => normalizedRevenue N algorithm permutation) := by
  intro δ hδ
  obtain ⟨N0, hN0⟩ := hharmonic δ hδ
  refine ⟨N0, ?_⟩
  intro N hN randomizedAlgorithm
  let C : BMatchingRoundAllocationRevenueCertificate
      N (Algorithm N) (AdWordsInstance.msvvRatio + δ) := {
    normalizedRevenue := normalizedRevenue N
    expectedRoundBidderAllocation := expectedRoundBidderAllocation N
    deterministicAverage_le_cappedExpectedSpend := haverage N
    expectedRoundBidderAllocation_le := hexpected_le N
    revenueBound_le_ratio := hN0 N hN
  }
  exact C.no_randomized_algorithm_beats_ratio randomizedAlgorithm

namespace BMatchingTheorem9FamilyCertificate

variable {Algorithm : ℕ → Type*}
variable [∀ N, Fintype (Algorithm N)] [∀ N, DecidableEq (Algorithm N)]

/--
Family-level Theorem 9 endpoint from the packaged lower-bound certificate.
-/
theorem eventually_no_randomized_algorithm_beats_msvvRatio_add_delta
    (C : BMatchingTheorem9FamilyCertificate Algorithm) :
    ∀ δ : ℝ, 0 < δ →
      ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
        ∀ randomizedAlgorithm : PMF (Algorithm N),
          ¬ ∀ permutation,
            AdWordsInstance.msvvRatio + δ <
              pmfExp randomizedAlgorithm
                (fun algorithm => C.normalizedRevenue N algorithm permutation) := by
  exact
    theorem9_eventually_no_randomized_algorithm_beats_msvvRatio_add_delta
      C.normalizedRevenue C.expectedRoundBidderAllocation
      C.deterministicAverage_le_cappedExpectedSpend
      C.expectedRoundBidderAllocation_le
      theorem9_harmonic_eventually_le_msvvRatio_add

end BMatchingTheorem9FamilyCertificate

namespace BMatchingTheorem9PointwiseFamilyCertificate

variable {Algorithm : ℕ → Type*}
variable [∀ N, Fintype (Algorithm N)] [∀ N, DecidableEq (Algorithm N)]

/--
Family-level Theorem 9 endpoint from realized pointwise allocation variables.
-/
  theorem eventually_no_randomized_algorithm_beats_msvvRatio_add_delta
    (C : BMatchingTheorem9PointwiseFamilyCertificate Algorithm) :
    ∀ δ : ℝ, 0 < δ →
      ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
        ∀ randomizedAlgorithm : PMF (Algorithm N),
          ¬ ∀ permutation,
            AdWordsInstance.msvvRatio + δ <
              pmfExp randomizedAlgorithm
                (fun algorithm => C.normalizedRevenue N algorithm permutation) := by
  intro δ hδ
  obtain ⟨N0, hN0⟩ := theorem9_harmonic_eventually_le_msvvRatio_add δ hδ
  refine ⟨N0, ?_⟩
  intro N hN randomizedAlgorithm
  let Cfinite :
      BMatchingPointwiseAllocationRevenueCertificate
        N (Algorithm N) (AdWordsInstance.msvvRatio + δ) := {
    normalizedRevenue := C.normalizedRevenue N
    allocation := C.allocation N
    normalizedRevenue_le_cappedAllocationSpend :=
      C.normalizedRevenue_le_cappedAllocationSpend N
    expectedAllocation_le := C.expectedAllocation_le N
    revenueBound_le_ratio := hN0 N hN
  }
  exact Cfinite.no_randomized_algorithm_beats_ratio randomizedAlgorithm

end BMatchingTheorem9PointwiseFamilyCertificate

namespace BMatchingTheorem9SymmetricPointwiseFamilyCertificate

variable {Algorithm : ℕ → Type*}
variable [∀ N, Fintype (Algorithm N)] [∀ N, DecidableEq (Algorithm N)]

/--
Family-level Theorem 9 endpoint from round capacity and symmetry of eligible
positions under the random permutation distribution.
-/
  theorem eventually_no_randomized_algorithm_beats_msvvRatio_add_delta
    (C : BMatchingTheorem9SymmetricPointwiseFamilyCertificate Algorithm) :
    ∀ δ : ℝ, 0 < δ →
      ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
        ∀ randomizedAlgorithm : PMF (Algorithm N),
          ¬ ∀ permutation,
            AdWordsInstance.msvvRatio + δ <
              pmfExp randomizedAlgorithm
                (fun algorithm => C.normalizedRevenue N algorithm permutation) := by
  intro δ hδ
  obtain ⟨N0, hN0⟩ := theorem9_harmonic_eventually_le_msvvRatio_add δ hδ
  refine ⟨N0, ?_⟩
  intro N hN randomizedAlgorithm
  let Cfinite :
      BMatchingSymmetricPointwiseAllocationRevenueCertificate
        N (Algorithm N) (AdWordsInstance.msvvRatio + δ) := {
    normalizedRevenue := C.normalizedRevenue N
    allocation := C.allocation N
    normalizedRevenue_le_cappedAllocationSpend :=
      C.normalizedRevenue_le_cappedAllocationSpend N
    allocation_zero_of_ineligible :=
      C.allocation_zero_of_ineligible N
    round_allocation_sum_le_one :=
      C.round_allocation_sum_le_one N
    expectedAllocation_eq_of_eligible :=
      C.expectedAllocation_eq_of_eligible N
    revenueBound_le_ratio := hN0 N hN
  }
  exact Cfinite.no_randomized_algorithm_beats_ratio randomizedAlgorithm

end BMatchingTheorem9SymmetricPointwiseFamilyCertificate

namespace BMatchingTheorem9RelabelSymmetricPointwiseFamilyCertificate

variable {Algorithm : ℕ → Type*}
variable [∀ N, Fintype (Algorithm N)] [∀ N, DecidableEq (Algorithm N)]

/--
Family-level Theorem 9 endpoint from pointwise input-relabeling symmetry.
-/
theorem eventually_no_randomized_algorithm_beats_msvvRatio_add_delta
    (C : BMatchingTheorem9RelabelSymmetricPointwiseFamilyCertificate
      Algorithm) :
    ∀ δ : ℝ, 0 < δ →
      ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
        ∀ randomizedAlgorithm : PMF (Algorithm N),
          ¬ ∀ permutation,
            AdWordsInstance.msvvRatio + δ <
              pmfExp randomizedAlgorithm
                (fun algorithm => C.normalizedRevenue N algorithm permutation) := by
  let Csym :
      BMatchingTheorem9SymmetricPointwiseFamilyCertificate Algorithm := {
    normalizedRevenue := C.normalizedRevenue
    allocation := C.allocation
    normalizedRevenue_le_cappedAllocationSpend :=
      C.normalizedRevenue_le_cappedAllocationSpend
    allocation_zero_of_ineligible := C.allocation_zero_of_ineligible
    round_allocation_sum_le_one := C.round_allocation_sum_le_one
    expectedAllocation_eq_of_eligible := by
      intro N algorithm round bidder bidder' hbidder hbidder'
      exact
        uniformPermutationExpectation_eq_of_relabel
          (C.relabelInput N round bidder bidder')
          (fun permutation =>
            C.allocation_eq_of_relabel_eligible
              N algorithm round bidder bidder' hbidder hbidder'
              permutation)
  }
  exact Csym.eventually_no_randomized_algorithm_beats_msvvRatio_add_delta

end BMatchingTheorem9RelabelSymmetricPointwiseFamilyCertificate

namespace BMatchingTheorem9ObservedPrefixFamilyCertificate

variable {Algorithm : ℕ → Type*}
variable [∀ N, Fintype (Algorithm N)] [∀ N, DecidableEq (Algorithm N)]

/--
Family-level Theorem 9 endpoint from the observed-prefix online-information
model.
-/
theorem eventually_no_randomized_algorithm_beats_msvvRatio_add_delta
    (C : BMatchingTheorem9ObservedPrefixFamilyCertificate Algorithm) :
    ∀ δ : ℝ, 0 < δ →
      ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
        ∀ randomizedAlgorithm : PMF (Algorithm N),
          ¬ ∀ permutation,
            AdWordsInstance.msvvRatio + δ <
              pmfExp randomizedAlgorithm
                (fun algorithm => C.normalizedRevenue N algorithm permutation) := by
  let Crelabel :
      BMatchingTheorem9RelabelSymmetricPointwiseFamilyCertificate
        Algorithm := {
    normalizedRevenue := C.normalizedRevenue
    allocation := C.allocation
    normalizedRevenue_le_cappedAllocationSpend :=
      C.normalizedRevenue_le_cappedAllocationSpend
    allocation_zero_of_ineligible := C.allocation_zero_of_ineligible
    round_allocation_sum_le_one := C.round_allocation_sum_le_one
    relabelInput := fun N _ bidder bidder' =>
      Equiv.mulRight (Equiv.swap bidder bidder')
    allocation_eq_of_relabel_eligible := by
      intro N algorithm round bidder bidder' hbidder hbidder' permutation
      let swap : Equiv.Perm (Fin N) := Equiv.swap bidder bidder'
      calc
        C.allocation N algorithm ((Equiv.mulRight swap) permutation)
            round bidder =
            C.prefixAllocation N algorithm
              (theorem9ObservedPrefix N
                ((Equiv.mulRight swap) permutation) round)
              round (((Equiv.mulRight swap) permutation) bidder) := by
              exact C.allocation_eq_prefix N algorithm
                ((Equiv.mulRight swap) permutation) round bidder
        _ =
            C.prefixAllocation N algorithm
              (theorem9ObservedPrefix N permutation round)
              round (permutation bidder') := by
              have hprefix' :
                  theorem9ObservedPrefix N
                      (permutation * Equiv.swap bidder bidder') round =
                    theorem9ObservedPrefix N permutation round :=
                theorem9ObservedPrefix_mul_swap_eq
                  (N := N) (round := round) (bidder := bidder)
                  (bidder' := bidder') hbidder hbidder' permutation
              simpa [swap, Equiv.coe_mulRight, Equiv.Perm.mul_apply] using
                congrArg
                  (fun pref =>
                    C.prefixAllocation N algorithm pref round
                      (permutation bidder')) hprefix'
        _ = C.allocation N algorithm permutation round bidder' := by
              exact (C.allocation_eq_prefix N algorithm permutation
                round bidder').symm
  }
  exact Crelabel.eventually_no_randomized_algorithm_beats_msvvRatio_add_delta

end BMatchingTheorem9ObservedPrefixFamilyCertificate

namespace BMatchingTheorem9FeasibleObservedPrefixFamilyCertificate

variable {Algorithm : ℕ → Type*}
variable [∀ N, Fintype (Algorithm N)] [∀ N, DecidableEq (Algorithm N)]

/--
Family-level Theorem 9 endpoint from feasible actual-bidder allocation rules
over the observed prefix.
-/
theorem eventually_no_randomized_algorithm_beats_msvvRatio_add_delta
    (C : BMatchingTheorem9FeasibleObservedPrefixFamilyCertificate
      Algorithm) :
    ∀ δ : ℝ, 0 < δ →
      ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
        ∀ randomizedAlgorithm : PMF (Algorithm N),
          ¬ ∀ permutation,
            AdWordsInstance.msvvRatio + δ <
              pmfExp randomizedAlgorithm
                (fun algorithm => C.normalizedRevenue N algorithm permutation) := by
  let Cprefix :
      BMatchingTheorem9ObservedPrefixFamilyCertificate Algorithm := {
    normalizedRevenue := C.normalizedRevenue
    allocation := fun N algorithm permutation round bidder =>
      C.prefixAllocation N algorithm
        (theorem9ObservedPrefix N permutation round)
        round (permutation bidder)
    prefixAllocation := C.prefixAllocation
    allocation_eq_prefix := by
      intro N algorithm permutation round bidder
      rfl
    normalizedRevenue_le_cappedAllocationSpend :=
      C.normalizedRevenue_le_cappedPrefixAllocationSpend
    allocation_zero_of_ineligible := by
      intro N algorithm permutation round bidder hnot
      exact
        C.prefixAllocation_zero_of_not_visible N algorithm
          (theorem9ObservedPrefix N permutation round) round
          (permutation bidder)
          (by
            simp [theorem9ObservedPrefix,
              theorem9ActualEligibleBidders_not_mem_of_not_eligible hnot])
    round_allocation_sum_le_one := by
      intro N algorithm permutation round
      let obs := theorem9ObservedPrefix N permutation round
      have hcap := C.prefixAllocation_sum_le_one N algorithm obs round
      have hcurrent :
          obs round = theorem9ActualEligibleBidders N permutation round := by
        simp [obs, theorem9ObservedPrefix]
      have hcapActual :
          (∑ bidder ∈ theorem9ActualEligibleBidders N permutation round,
            C.prefixAllocation N algorithm obs round bidder) ≤ 1 := by
        simpa [hcurrent] using hcap
      have hsum :=
        theorem9ActualEligibleBidders_sum_eq permutation round
          (fun bidder => C.prefixAllocation N algorithm obs round bidder)
      calc
        (∑ bidder ∈ theorem9EligibleBidders N round,
          C.prefixAllocation N algorithm obs round (permutation bidder))
            =
          (∑ bidder ∈ theorem9ActualEligibleBidders N permutation round,
            C.prefixAllocation N algorithm obs round bidder) := by
            exact hsum.symm
        _ ≤ 1 := hcapActual
  }
  exact Cprefix.eventually_no_randomized_algorithm_beats_msvvRatio_add_delta

end BMatchingTheorem9FeasibleObservedPrefixFamilyCertificate

namespace BMatchingTheorem9FeasiblePrefixRuleFamily

variable {Algorithm : ℕ → Type*}
variable [∀ N, Fintype (Algorithm N)] [∀ N, DecidableEq (Algorithm N)]

/-- Capped normalized revenue induced by a feasible observed-prefix rule. -/
noncomputable def normalizedRevenue
    (C : BMatchingTheorem9FeasiblePrefixRuleFamily Algorithm)
    (N : ℕ) (algorithm : Algorithm N)
    (permutation : Equiv.Perm (Fin N)) : ℝ :=
  (∑ bidder : Fin N,
    min 1
      (∑ round : Fin N,
        C.prefixAllocation N algorithm
          (theorem9ObservedPrefix N permutation round)
          round (permutation bidder))) /
    (N : ℝ)

/--
Family-level Theorem 9 endpoint for feasible prefix allocation rules, with the
payoff defined as the paper's capped normalized spend expression.
-/
theorem eventually_no_randomized_algorithm_beats_msvvRatio_add_delta
    (C : BMatchingTheorem9FeasiblePrefixRuleFamily Algorithm) :
    ∀ δ : ℝ, 0 < δ →
      ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
        ∀ randomizedAlgorithm : PMF (Algorithm N),
          ¬ ∀ permutation,
            AdWordsInstance.msvvRatio + δ <
              pmfExp randomizedAlgorithm
                (fun algorithm => C.normalizedRevenue N algorithm permutation) := by
  let Cfeasible :
      BMatchingTheorem9FeasibleObservedPrefixFamilyCertificate
        Algorithm := {
    normalizedRevenue := C.normalizedRevenue
    prefixAllocation := C.prefixAllocation
    normalizedRevenue_le_cappedPrefixAllocationSpend := by
      intro N algorithm permutation
      exact le_rfl
    prefixAllocation_zero_of_not_visible :=
      C.prefixAllocation_zero_of_not_visible
    prefixAllocation_sum_le_one := C.prefixAllocation_sum_le_one
  }
  exact Cfeasible.eventually_no_randomized_algorithm_beats_msvvRatio_add_delta

end BMatchingTheorem9FeasiblePrefixRuleFamily

/--
Finite families of integral prefix choice algorithms. The algorithm type may be
any finite type; each algorithm supplies a deterministic choice rule that
selects at most one visible actual bidder per round.
-/
structure BMatchingTheorem9IntegralPrefixChoiceFamily
    (Algorithm : ℕ → Type*)
    [∀ N, Fintype (Algorithm N)] [∀ N, DecidableEq (Algorithm N)] where
  choice :
    (N : ℕ) → Algorithm N → BMatchingIntegralPrefixChoice N
  choice_feasible :
    ∀ N algorithm, BMatchingIntegralPrefixChoice.Feasible (choice N algorithm)

namespace BMatchingTheorem9IntegralPrefixChoiceFamily

variable {Algorithm : ℕ → Type*}
variable [∀ N, Fintype (Algorithm N)] [∀ N, DecidableEq (Algorithm N)]

/-- Convert an integral prefix choice family to the feasible prefix-rule interface. -/
noncomputable def toFeasiblePrefixRuleFamily
    (C : BMatchingTheorem9IntegralPrefixChoiceFamily Algorithm) :
    BMatchingTheorem9FeasiblePrefixRuleFamily Algorithm where
  prefixAllocation := fun N algorithm obs round bidder =>
    if C.choice N algorithm obs round = some bidder then (1 : ℝ) else 0
  prefixAllocation_zero_of_not_visible := by
    intro N algorithm obs round bidder hnot
    by_cases hchoice : C.choice N algorithm obs round = some bidder
    · exact False.elim (hnot (C.choice_feasible N algorithm obs round bidder hchoice))
    · simp [hchoice]
  prefixAllocation_sum_le_one := by
    intro N algorithm obs round
    cases hchoice : C.choice N algorithm obs round with
    | none =>
        simp
    | some chosen =>
        have hchosen : chosen ∈ obs round :=
          C.choice_feasible N algorithm obs round chosen hchoice
        have hsum :
            (∑ bidder ∈ obs round,
              (if some chosen = some bidder then (1 : ℝ) else 0)) = 1 := by
          simpa [hchosen] using
            (Finset.sum_ite_eq' (obs round) chosen (fun _ => (1 : ℝ)))
        exact le_of_eq hsum

/-- Capped normalized revenue for an integral prefix choice family. -/
noncomputable def normalizedRevenue
    (C : BMatchingTheorem9IntegralPrefixChoiceFamily Algorithm)
    (N : ℕ) (algorithm : Algorithm N)
    (permutation : Equiv.Perm (Fin N)) : ℝ :=
  C.toFeasiblePrefixRuleFamily.normalizedRevenue N algorithm permutation

/--
Theorem 9 endpoint for finite randomized distributions over integral prefix
choice algorithms.
-/
theorem eventually_no_randomized_algorithm_beats_msvvRatio_add_delta
    (C : BMatchingTheorem9IntegralPrefixChoiceFamily Algorithm) :
    ∀ δ : ℝ, 0 < δ →
      ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
        ∀ randomizedAlgorithm : PMF (Algorithm N),
          ¬ ∀ permutation,
            AdWordsInstance.msvvRatio + δ <
              pmfExp randomizedAlgorithm
                (fun algorithm => C.normalizedRevenue N algorithm permutation) := by
  exact
    C.toFeasiblePrefixRuleFamily
      |>.eventually_no_randomized_algorithm_beats_msvvRatio_add_delta

/--
If a richer integral-choice model has realized normalized revenue bounded pointwise
by the induced capped-prefix payoff, then the same asymptotic lower-bound
statement applies to realized revenue.
-/
theorem eventually_no_randomized_algorithm_beats_msvvRatio_add_delta_of_realized_revenue
    (C : BMatchingTheorem9IntegralPrefixChoiceFamily Algorithm)
    (normalizedRevenue :
      (N : ℕ) → Algorithm N → Equiv.Perm (Fin N) → ℝ)
    (hrealized_le_capped :
      ∀ N algorithm permutation,
        normalizedRevenue N algorithm permutation ≤
          C.normalizedRevenue N algorithm permutation) :
    ∀ δ : ℝ, 0 < δ →
      ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
        ∀ randomizedAlgorithm : PMF (Algorithm N),
          ¬ ∀ permutation,
            AdWordsInstance.msvvRatio + δ <
              pmfExp randomizedAlgorithm
                (fun algorithm => normalizedRevenue N algorithm permutation) := by
  intro δ hδ
  obtain
      ⟨N0, hN0⟩ :=
    C.eventually_no_randomized_algorithm_beats_msvvRatio_add_delta δ hδ
  refine ⟨N0, ?_⟩
  intro N hN randomizedAlgorithm hforall
  have hboundedPayoff :
      ¬ ∀ permutation,
        AdWordsInstance.msvvRatio + δ <
          pmfExp randomizedAlgorithm
            (fun algorithm => C.normalizedRevenue N algorithm permutation) :=
    hN0 N hN randomizedAlgorithm
  exact hboundedPayoff (fun permutation =>
    lt_of_lt_of_le
      (hforall permutation)
      (pmfExp_le_pmfExp_of_forall_le randomizedAlgorithm
        (fun algorithm => normalizedRevenue N algorithm permutation)
        (fun algorithm => C.normalizedRevenue N algorithm permutation)
        (fun algorithm => hrealized_le_capped N algorithm permutation)))

end BMatchingTheorem9IntegralPrefixChoiceFamily

namespace BMatchingTheorem9LayerCountFamilyCertificate

variable {Algorithm : ℕ → Type*}
variable [∀ N, Fintype (Algorithm N)] [∀ N, DecidableEq (Algorithm N)]

/--
Family-level Theorem 9 endpoint from round-allocation inequalities and the
finite layer-count harmonic estimate.
-/
theorem eventually_no_randomized_algorithm_beats_msvvRatio_add_delta
    (C : BMatchingTheorem9LayerCountFamilyCertificate Algorithm) :
    ∀ δ : ℝ, 0 < δ →
      ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
        ∀ randomizedAlgorithm : PMF (Algorithm N),
          ¬ ∀ permutation,
            AdWordsInstance.msvvRatio + δ <
              pmfExp randomizedAlgorithm
                (fun algorithm => C.normalizedRevenue N algorithm permutation) := by
  let Ceventual : BMatchingTheorem9FamilyCertificate Algorithm := {
    normalizedRevenue := C.normalizedRevenue
    expectedRoundBidderAllocation := C.expectedRoundBidderAllocation
    deterministicAverage_le_cappedExpectedSpend :=
      C.deterministicAverage_le_cappedExpectedSpend
    expectedRoundBidderAllocation_le := C.expectedRoundBidderAllocation_le
  }
  exact Ceventual.eventually_no_randomized_algorithm_beats_msvvRatio_add_delta

end BMatchingTheorem9LayerCountFamilyCertificate

namespace BMatchingTheorem9PointwiseLayerCountFamilyCertificate

variable {Algorithm : ℕ → Type*}
variable [∀ N, Fintype (Algorithm N)] [∀ N, DecidableEq (Algorithm N)]

/--
Family-level Theorem 9 endpoint from pointwise allocations and the finite
layer-count harmonic estimate.
-/
theorem eventually_no_randomized_algorithm_beats_msvvRatio_add_delta
    (C : BMatchingTheorem9PointwiseLayerCountFamilyCertificate Algorithm) :
    ∀ δ : ℝ, 0 < δ →
      ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
        ∀ randomizedAlgorithm : PMF (Algorithm N),
          ¬ ∀ permutation,
            AdWordsInstance.msvvRatio + δ <
              pmfExp randomizedAlgorithm
                (fun algorithm => C.normalizedRevenue N algorithm permutation) := by
  let Ceventual :
      BMatchingTheorem9PointwiseFamilyCertificate Algorithm := {
    normalizedRevenue := C.normalizedRevenue
    allocation := C.allocation
    normalizedRevenue_le_cappedAllocationSpend :=
      C.normalizedRevenue_le_cappedAllocationSpend
    expectedAllocation_le := C.expectedAllocation_le
  }
  exact Ceventual.eventually_no_randomized_algorithm_beats_msvvRatio_add_delta

end BMatchingTheorem9PointwiseLayerCountFamilyCertificate

namespace BMatchingTheorem9SymmetricPointwiseLayerCountFamilyCertificate

variable {Algorithm : ℕ → Type*}
variable [∀ N, Fintype (Algorithm N)] [∀ N, DecidableEq (Algorithm N)]

/--
Family-level Theorem 9 endpoint from symmetry/capacity allocations and the
finite layer-count harmonic estimate.
-/
theorem eventually_no_randomized_algorithm_beats_msvvRatio_add_delta
    (C : BMatchingTheorem9SymmetricPointwiseLayerCountFamilyCertificate
      Algorithm) :
    ∀ δ : ℝ, 0 < δ →
      ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
        ∀ randomizedAlgorithm : PMF (Algorithm N),
          ¬ ∀ permutation,
            AdWordsInstance.msvvRatio + δ <
              pmfExp randomizedAlgorithm
                (fun algorithm => C.normalizedRevenue N algorithm permutation) := by
  let Ceventual :
      BMatchingTheorem9SymmetricPointwiseFamilyCertificate Algorithm := {
    normalizedRevenue := C.normalizedRevenue
    allocation := C.allocation
    normalizedRevenue_le_cappedAllocationSpend :=
      C.normalizedRevenue_le_cappedAllocationSpend
    allocation_zero_of_ineligible := C.allocation_zero_of_ineligible
    round_allocation_sum_le_one := C.round_allocation_sum_le_one
    expectedAllocation_eq_of_eligible := C.expectedAllocation_eq_of_eligible
  }
  exact Ceventual.eventually_no_randomized_algorithm_beats_msvvRatio_add_delta

end BMatchingTheorem9SymmetricPointwiseLayerCountFamilyCertificate

end Online
end AppliedModelingLib
