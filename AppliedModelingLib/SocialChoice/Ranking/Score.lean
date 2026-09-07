import AppliedModelingLib.Foundations.Probability.RandomUtility
import AppliedModelingLib.SocialChoice.Ranking.Basic
import AppliedModelingLib.SocialChoice.Ranking.Sequential
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.Linarith

/-!
# Score-Induced Three-Candidate Rankings

Reusable finite ranking maps induced by three real scores, ordered descending
by score and with deterministic lower-index tie-breaking.

This module is deliberately probability-free. Continuous RUM files can prove
measurability or no-tie facts around these maps in their own measure layer.
-/

namespace AppliedModelingLib
namespace SocialChoice
namespace Ranking

/-! ## Generic score-ordered rankings -/

/--
A ranking weakly orders candidates by a score function when every earlier
ranked candidate has weakly higher score than every later ranked candidate.
-/
def RankingWeaklyOrdersScores {n : ℕ}
    (π : Ranking n) (score : Candidate n → ℝ) : Prop :=
  ∀ {i j : Candidate n}, rankOf π i ≤ rankOf π j → score j ≤ score i

/--
The canonical ranking induced by a finite score vector, ordered by weakly
decreasing score and using `Tuple.sort`'s deterministic tie-breaking.
-/
noncomputable def rankByScore {n : ℕ} (score : Candidate n → ℝ) : Ranking n :=
  Tuple.sort (fun i : Candidate n => -score i)

theorem rankByScore_eq_of_pairwise_lt_iff_of_noTies {n : ℕ}
    {score score' : Candidate n → ℝ}
    (hnoTie : ∀ i j : Candidate n, i ≠ j → score i ≠ score j)
    (hlt_iff : ∀ i j : Candidate n, score i < score j ↔ score' i < score' j) :
    rankByScore score' = rankByScore score := by
  classical
  let π : Ranking n := rankByScore score
  have hπ_sort :
      π = Tuple.sort (fun c : Candidate n => -score' c) := by
    refine (Tuple.eq_sort_iff
      (f := fun c : Candidate n => -score' c) (σ := π)).mpr ?_
    constructor
    · intro i j hij
      by_cases hij_eq : i = j
      · subst j
        simp
      · have hπ_ne : π i ≠ π j := fun h => hij_eq (π.injective h)
        have hbase_ne : score (π i) ≠ score (π j) := hnoTie (π i) (π j) hπ_ne
        have hbase_neg_le :
            -score (π i) ≤ -score (π j) := by
          simpa [π, rankByScore, Function.comp_def] using
            (Tuple.monotone_sort (fun c : Candidate n => -score c) hij)
        have hbase_le : score (π j) ≤ score (π i) := by
          linarith
        have hbase_lt : score (π j) < score (π i) := by
          exact lt_of_le_of_ne hbase_le hbase_ne.symm
        have hprime_lt : score' (π j) < score' (π i) :=
          (hlt_iff (π j) (π i)).mp hbase_lt
        change -score' (π i) ≤ -score' (π j)
        linarith
    · intro i j hij heq
      have hij_ne : i ≠ j := ne_of_lt hij
      have hπ_ne : π i ≠ π j := fun h => hij_ne (π.injective h)
      have hbase_ne : score (π i) ≠ score (π j) := hnoTie (π i) (π j) hπ_ne
      have hbase_neg_le :
          -score (π i) ≤ -score (π j) := by
        simpa [π, rankByScore, Function.comp_def] using
          (Tuple.monotone_sort (fun c : Candidate n => -score c) hij.le)
      have hbase_le : score (π j) ≤ score (π i) := by
        linarith
      have hbase_lt : score (π j) < score (π i) := by
        exact lt_of_le_of_ne hbase_le hbase_ne.symm
      have hprime_lt : score' (π j) < score' (π i) :=
        (hlt_iff (π j) (π i)).mp hbase_lt
      change -score' (π i) = -score' (π j) at heq
      exfalso
      linarith
  simpa [π, rankByScore] using hπ_sort.symm

/--
Score-induced rankings are locally constant when score coordinates are
continuous and the score vector has no ties at the base parameter.
-/
theorem eventually_rankByScore_eq_of_continuousAt_of_noTies {n : ℕ}
    {score : ℝ → Candidate n → ℝ} {x : ℝ}
    (hcont : ∀ c : Candidate n, ContinuousAt (fun θ : ℝ => score θ c) x)
    (hnoTie : ∀ i j : Candidate n, i ≠ j → score x i ≠ score x j) :
    ∀ᶠ θ in nhds x, rankByScore (score θ) = rankByScore (score x) := by
  classical
  have hpair :
      ∀ i j : Candidate n,
        ∀ᶠ θ in nhds x, score x i < score x j ↔ score θ i < score θ j := by
    intro i j
    by_cases hij : i = j
    · subst j
      exact Filter.Eventually.of_forall (fun θ => by simp)
    · by_cases hlt : score x i < score x j
      · have hdiff_pos : 0 < score x j - score x i := by linarith
        have hdiff_cont :
            ContinuousAt (fun θ : ℝ => score θ j - score θ i) x :=
          (hcont j).sub (hcont i)
        have hev :
            ∀ᶠ θ in nhds x, 0 < score θ j - score θ i :=
          hdiff_cont.eventually (isOpen_Ioi.mem_nhds hdiff_pos)
        filter_upwards [hev] with θ hθ
        constructor
        · intro _h
          linarith
        · intro _h
          exact hlt
      · have hle : score x j ≤ score x i := le_of_not_gt hlt
        have hne : score x j ≠ score x i := by
          exact (hnoTie i j hij).symm
        have hgt : score x j < score x i := lt_of_le_of_ne hle hne
        have hdiff_pos : 0 < score x i - score x j := by linarith
        have hdiff_cont :
            ContinuousAt (fun θ : ℝ => score θ i - score θ j) x :=
          (hcont i).sub (hcont j)
        have hev :
            ∀ᶠ θ in nhds x, 0 < score θ i - score θ j :=
          hdiff_cont.eventually (isOpen_Ioi.mem_nhds hdiff_pos)
        filter_upwards [hev] with θ hθ
        constructor
        · intro hxlt
          exact (hlt hxlt).elim
        · intro hθlt
          linarith
  have hall :
      ∀ᶠ θ in nhds x,
        ∀ i j : Candidate n, score x i < score x j ↔ score θ i < score θ j := by
    simpa only [Filter.eventually_all] using hpair
  filter_upwards [hall] with θ hθ
  exact
    rankByScore_eq_of_pairwise_lt_iff_of_noTies
      (score := score x) (score' := score θ) hnoTie hθ

theorem rankByScore_weaklyOrdersScores {n : ℕ} (score : Candidate n → ℝ) :
    RankingWeaklyOrdersScores (rankByScore score) score := by
  intro i j hrank
  have hmono := Tuple.monotone_sort (fun i : Candidate n => -score i)
  have hneg :
      -score i ≤ -score j := by
    simpa [rankByScore, rankOf, Function.comp_def] using hmono hrank
  linarith

/--
If a score-induced ranking inverts a pair, then the first candidate's score is
weakly below the second candidate's score.
-/
theorem score_le_of_invertedPair_rankByScore {n : ℕ}
    {center : Ranking n} {score : Candidate n → ℝ}
    {ab : Candidate n × Candidate n}
    (hinv : invertedPair center (rankByScore score) ab) :
    score ab.1 ≤ score ab.2 :=
  rankByScore_weaklyOrdersScores score (le_of_lt hinv.2)

/--
If one candidate has strictly larger score than every other candidate, then it
is the best element of the full candidate set under `rankByScore`.
-/
theorem bestInSet_rankByScore_univ_eq_of_strict_top {n : ℕ}
    {score : Candidate n → ℝ} {c : Candidate n}
    (htop : ∀ d : Candidate n, d ≠ c → score d < score c) :
    bestInSet (rankByScore score) Finset.univ = c := by
  let b : Candidate n := bestInSet (rankByScore score) Finset.univ
  have huniv : (Finset.univ : Finset (Candidate n)).Nonempty :=
    ⟨c, Finset.mem_univ c⟩
  have hc_le : score c ≤ score b :=
    rankByScore_weaklyOrdersScores score
      (rankOf_bestInSet_le (rankByScore score) huniv (Finset.mem_univ c))
  by_contra hbc
  have hb_lt : score b < score c := htop b hbc
  linarith

theorem RankingWeaklyOrdersScores.score_le_bestInSet {n : ℕ}
    {π : Ranking n} {score : Candidate n → ℝ}
    (hπ : RankingWeaklyOrdersScores π score)
    {remaining : Finset (Candidate n)} (hremaining : remaining.Nonempty)
    {i : Candidate n} (hi : i ∈ remaining) :
    score i ≤ score (bestInSet π remaining) :=
  hπ (rankOf_bestInSet_le π hremaining hi)

/--
Finite-candidate best-in-set monotonicity under additive RUM score contraction.

If one ranking orders raw scores and the other orders the corresponding
contracted scores on the same remaining set, then the best remaining candidate
under the contracted ranking has weakly higher true value than the best
remaining candidate under the raw ranking.
-/
theorem value_bestInSet_le_of_rumContractScore_ordered_rankings {n : ℕ}
    {t : ℝ} {value raw : Candidate n → ℝ}
    {rawRanking contractRanking : Ranking n}
    {remaining : Finset (Candidate n)}
    (ht0 : 0 ≤ t) (htlt1 : t < 1)
    (hremaining : remaining.Nonempty)
    (hraw :
      RankingWeaklyOrdersScores rawRanking raw)
    (hcontract :
      RankingWeaklyOrdersScores contractRanking
        (fun i => AppliedModelingLib.Probability.rumContractScore t (value i) (raw i))) :
    value (bestInSet rawRanking remaining) ≤
      value (bestInSet contractRanking remaining) :=
  AppliedModelingLib.Probability.rumContractScore_value_le_of_raw_max_on_and_contract_max_on
    (t := t) (value := value) (raw := raw)
    (feasible := fun i => i ∈ remaining)
    ht0 htlt1
    (bestInSet_mem rawRanking hremaining)
    (bestInSet_mem contractRanking hremaining)
    (fun i hi => hraw.score_le_bestInSet hremaining hi)
    (fun i hi => hcontract.score_le_bestInSet hremaining hi)

/--
Concrete finite-candidate RUM contraction monotonicity for rankings obtained by
sorting score vectors.
-/
theorem value_bestInSet_le_of_rankByScore_rumContractScore {n : ℕ}
    {t : ℝ} {value raw : Candidate n → ℝ}
    {remaining : Finset (Candidate n)}
    (ht0 : 0 ≤ t) (htlt1 : t < 1)
    (hremaining : remaining.Nonempty) :
    value (bestInSet (rankByScore raw) remaining) ≤
      value (bestInSet
        (rankByScore
          (fun i => AppliedModelingLib.Probability.rumContractScore t (value i) (raw i)))
        remaining) :=
  value_bestInSet_le_of_rumContractScore_ordered_rankings
    ht0 htlt1 hremaining
    (rankByScore_weaklyOrdersScores raw)
    (rankByScore_weaklyOrdersScores
      (fun i => AppliedModelingLib.Probability.rumContractScore t (value i) (raw i)))

/--
Deterministic strict full-set improvement under a top switch: if the raw score
ranking selects a lower-valued candidate and the contracted score ranking
selects a higher-valued candidate, then full-set best value strictly improves.
-/
theorem value_bestInSet_rankByScore_contract_strict_of_top_switch {n : ℕ}
    {t : ℝ} {value raw : Candidate n → ℝ}
    {low high : Candidate n}
    (hvalue : value low < value high)
    (hrawTop : ∀ d : Candidate n, d ≠ low → raw d < raw low)
    (hcontractTop :
      ∀ d : Candidate n, d ≠ high →
        AppliedModelingLib.Probability.rumContractScore t (value d) (raw d) <
          AppliedModelingLib.Probability.rumContractScore t (value high) (raw high)) :
    value (bestInSet (rankByScore raw) Finset.univ) <
      value (bestInSet
        (rankByScore
          (fun i => AppliedModelingLib.Probability.rumContractScore t (value i) (raw i)))
        Finset.univ) := by
  rw [bestInSet_rankByScore_univ_eq_of_strict_top hrawTop]
  rw [bestInSet_rankByScore_univ_eq_of_strict_top hcontractTop]
  exact hvalue

/-! ## Three-score order predicates -/

/-- Candidate `0` is weakly first among three realized scores. -/
def rum3TopFirstByScores (s1 s2 s3 : ℝ) : Prop :=
  s2 ≤ s1 ∧ s3 ≤ s1

/-- Candidate `1` strictly beats candidate `0` and weakly beats candidate `2`. -/
def rum3MiddleBeatsTopByScores (s1 s2 s3 : ℝ) : Prop :=
  s1 < s2 ∧ s3 ≤ s2

/-- Candidate `2` is weakly first among three realized scores. -/
def rum3BottomFirstByScores (s1 s2 s3 : ℝ) : Prop :=
  s1 ≤ s3 ∧ s2 ≤ s3

/-- Three realized scores have no pairwise ties. -/
def rum3NoTiesByScores (s1 s2 s3 : ℝ) : Prop :=
  s1 ≠ s2 ∧ s1 ≠ s3 ∧ s2 ≠ s3

/-! ## Concrete three-candidate rankings -/

/-- The concrete ranking `[0, 1, 2]`. -/
def rum3Ranking012 : Ranking 1 :=
  Equiv.refl (Candidate 1)

/-- The concrete ranking `[0, 2, 1]`. -/
def rum3Ranking021 : Ranking 1 :=
  Equiv.swap (1 : Candidate 1) (2 : Candidate 1)

/-- The concrete ranking `[1, 0, 2]`. -/
def rum3Ranking102 : Ranking 1 :=
  Equiv.swap (0 : Candidate 1) (1 : Candidate 1)

/-- The concrete ranking `[1, 2, 0]`. -/
def rum3Ranking120 : Ranking 1 :=
  (Equiv.swap (1 : Candidate 1) (2 : Candidate 1)).trans
    (Equiv.swap (0 : Candidate 1) (1 : Candidate 1))

/-- The concrete ranking `[2, 0, 1]`. -/
def rum3Ranking201 : Ranking 1 :=
  (Equiv.swap (0 : Candidate 1) (2 : Candidate 1)).trans
    (Equiv.swap (0 : Candidate 1) (1 : Candidate 1))

/-- The concrete ranking `[2, 1, 0]`. -/
def rum3Ranking210 : Ranking 1 :=
  Equiv.swap (0 : Candidate 1) (2 : Candidate 1)

@[simp] theorem rum3Ranking012_apply_zero :
    rum3Ranking012 (0 : Candidate 1) = (0 : Candidate 1) := rfl

@[simp] theorem rum3Ranking012_apply_one :
    rum3Ranking012 (1 : Candidate 1) = (1 : Candidate 1) := rfl

@[simp] theorem rum3Ranking012_apply_two :
    rum3Ranking012 (2 : Candidate 1) = (2 : Candidate 1) := rfl

@[simp] theorem rum3Ranking021_apply_zero :
    rum3Ranking021 (0 : Candidate 1) = (0 : Candidate 1) := by
  decide

@[simp] theorem rum3Ranking021_apply_one :
    rum3Ranking021 (1 : Candidate 1) = (2 : Candidate 1) := by
  decide

@[simp] theorem rum3Ranking021_apply_two :
    rum3Ranking021 (2 : Candidate 1) = (1 : Candidate 1) := by
  decide

@[simp] theorem rum3Ranking102_apply_zero :
    rum3Ranking102 (0 : Candidate 1) = (1 : Candidate 1) := by
  decide

@[simp] theorem rum3Ranking102_apply_one :
    rum3Ranking102 (1 : Candidate 1) = (0 : Candidate 1) := by
  decide

@[simp] theorem rum3Ranking102_apply_two :
    rum3Ranking102 (2 : Candidate 1) = (2 : Candidate 1) := by
  decide

@[simp] theorem rum3Ranking120_apply_zero :
    rum3Ranking120 (0 : Candidate 1) = (1 : Candidate 1) := by
  decide

@[simp] theorem rum3Ranking120_apply_one :
    rum3Ranking120 (1 : Candidate 1) = (2 : Candidate 1) := by
  decide

@[simp] theorem rum3Ranking120_apply_two :
    rum3Ranking120 (2 : Candidate 1) = (0 : Candidate 1) := by
  decide

@[simp] theorem rum3Ranking201_apply_zero :
    rum3Ranking201 (0 : Candidate 1) = (2 : Candidate 1) := by
  decide

@[simp] theorem rum3Ranking201_apply_one :
    rum3Ranking201 (1 : Candidate 1) = (0 : Candidate 1) := by
  decide

@[simp] theorem rum3Ranking201_apply_two :
    rum3Ranking201 (2 : Candidate 1) = (1 : Candidate 1) := by
  decide

@[simp] theorem rum3Ranking210_apply_zero :
    rum3Ranking210 (0 : Candidate 1) = (2 : Candidate 1) := by
  decide

@[simp] theorem rum3Ranking210_apply_one :
    rum3Ranking210 (1 : Candidate 1) = (1 : Candidate 1) := by
  decide

@[simp] theorem rum3Ranking210_apply_two :
    rum3Ranking210 (2 : Candidate 1) = (0 : Candidate 1) := by
  decide

/-! ## Ranking by score -/

/--
Ranking induced by three realized scores, ordered descending by score and
breaking ties in favor of the lower-indexed candidate.
-/
noncomputable def rum3RankByScores (s1 s2 s3 : ℝ) : Ranking 1 :=
  if h0 : s2 ≤ s1 ∧ s3 ≤ s1 then
    if s3 ≤ s2 then rum3Ranking012 else rum3Ranking021
  else if h1 : s1 < s2 ∧ s3 ≤ s2 then
    if s3 ≤ s1 then rum3Ranking102 else rum3Ranking120
  else
    if s2 ≤ s1 then rum3Ranking201 else rum3Ranking210

/-- Ranking map induced by three score-coordinate functions. -/
noncomputable def rum3RankByScoreFns {Ω : Type*}
    (r1 r2 r3 : Ω → ℝ) : Ω → Ranking 1 :=
  fun ω => rum3RankByScores (r1 ω) (r2 ω) (r3 ω)

theorem rum3RankByScores_eq012_of_adjacent_order
    {s1 s2 s3 : ℝ} (h21 : s2 ≤ s1) (h32 : s3 ≤ s2) :
    rum3RankByScores s1 s2 s3 = rum3Ranking012 := by
  have h31 : s3 ≤ s1 := le_trans h32 h21
  simp [rum3RankByScores, h21, h31, h32]

/-- If candidate 2 beats candidate 1 and candidate 1 beats candidate 3, the
score ranking is exactly `[1,0,2]`. -/
theorem rum3RankByScores_eq102_of_order
    {s1 s2 s3 : ℝ} (h12 : s1 < s2) (h31 : s3 ≤ s1) :
    rum3RankByScores s1 s2 s3 = rum3Ranking102 := by
  have hnot0 : ¬ (s2 ≤ s1 ∧ s3 ≤ s1) := by
    intro h
    exact (not_lt_of_ge h.1) h12
  have h1 : s1 < s2 ∧ s3 ≤ s2 := ⟨h12, le_trans h31 (le_of_lt h12)⟩
  simp [rum3RankByScores, h1, h31]

/-- Multiplying all three scores by a positive constant preserves the induced ranking. -/
theorem rum3RankByScores_pos_mul
    {c s1 s2 s3 : ℝ} (hc : 0 < c) :
    rum3RankByScores (c * s1) (c * s2) (c * s3) =
      rum3RankByScores s1 s2 s3 := by
  simp [rum3RankByScores, mul_le_mul_iff_right₀ hc,
    mul_lt_mul_iff_right₀ hc]

theorem rum3RankByScores_ne012_imp_adjacent_inversion
    {s1 s2 s3 : ℝ}
    (h : rum3RankByScores s1 s2 s3 ≠ rum3Ranking012) :
    s1 < s2 ∨ s2 < s3 := by
  by_contra hnot
  push Not at hnot
  exact h (rum3RankByScores_eq012_of_adjacent_order hnot.1 hnot.2)

theorem rum3RankByScoreFns_ne012_imp_adjacent_inversion
    {Ω : Type*} {r1 r2 r3 : Ω → ℝ} {ω : Ω}
    (h : rum3RankByScoreFns r1 r2 r3 ω ≠ rum3Ranking012) :
    r1 ω < r2 ω ∨ r2 ω < r3 ω :=
  rum3RankByScores_ne012_imp_adjacent_inversion h

@[simp] theorem firstChoice_rum3RankByScores (s1 s2 s3 : ℝ) :
    firstChoice (rum3RankByScores s1 s2 s3) =
      if s2 ≤ s1 ∧ s3 ≤ s1 then (0 : Candidate 1)
      else if s1 < s2 ∧ s3 ≤ s2 then (1 : Candidate 1)
      else (2 : Candidate 1) := by
  unfold rum3RankByScores firstChoice
  split_ifs <;> simp

@[simp] theorem secondChoice_rum3RankByScores (s1 s2 s3 : ℝ) :
    secondChoice (rum3RankByScores s1 s2 s3) =
      if s2 ≤ s1 ∧ s3 ≤ s1 then
        if s3 ≤ s2 then (1 : Candidate 1) else (2 : Candidate 1)
      else if s1 < s2 ∧ s3 ≤ s2 then
        if s3 ≤ s1 then (0 : Candidate 1) else (2 : Candidate 1)
      else
        if s2 ≤ s1 then (0 : Candidate 1) else (1 : Candidate 1) := by
  unfold rum3RankByScores secondChoice
  split_ifs <;> simp

@[simp] theorem rum3RankByScores_apply_zero (s1 s2 s3 : ℝ) :
    rum3RankByScores s1 s2 s3 (0 : Candidate 1) =
      if s2 ≤ s1 ∧ s3 ≤ s1 then (0 : Candidate 1)
      else if s1 < s2 ∧ s3 ≤ s2 then (1 : Candidate 1)
      else (2 : Candidate 1) := by
  simpa [firstChoice] using firstChoice_rum3RankByScores s1 s2 s3

@[simp] theorem rum3RankByScores_apply_one (s1 s2 s3 : ℝ) :
    rum3RankByScores s1 s2 s3 (1 : Candidate 1) =
      if s2 ≤ s1 ∧ s3 ≤ s1 then
        if s3 ≤ s2 then (1 : Candidate 1) else (2 : Candidate 1)
      else if s1 < s2 ∧ s3 ≤ s2 then
        if s3 ≤ s1 then (0 : Candidate 1) else (2 : Candidate 1)
      else
        if s2 ≤ s1 then (0 : Candidate 1) else (1 : Candidate 1) := by
  simpa [secondChoice] using secondChoice_rum3RankByScores s1 s2 s3

@[simp] theorem bestRemainingAfter_rum3RankByScores_remove0
    (s1 s2 s3 : ℝ) :
    bestRemainingAfter (rum3RankByScores s1 s2 s3) (0 : Candidate 1) =
      if s3 ≤ s2 then (1 : Candidate 1) else (2 : Candidate 1) := by
  change
    (if firstChoice (rum3RankByScores s1 s2 s3) = (0 : Candidate 1) then
      secondChoice (rum3RankByScores s1 s2 s3)
    else firstChoice (rum3RankByScores s1 s2 s3)) =
      if s3 ≤ s2 then (1 : Candidate 1) else (2 : Candidate 1)
  by_cases h32 : s3 ≤ s2
  · by_cases h0 : s2 ≤ s1 ∧ s3 ≤ s1
    · simp [h0, h32]
    · by_cases h1 : s1 < s2 ∧ s3 ≤ s2
      · simp [h0, h1]
      · exfalso
        by_cases h21 : s2 ≤ s1
        · exact h0 ⟨h21, le_trans h32 h21⟩
        · exact h1 ⟨lt_of_not_ge h21, h32⟩
  · by_cases h0 : s2 ≤ s1 ∧ s3 ≤ s1
    · simp [h0, h32]
    · by_cases h1 : s1 < s2 ∧ s3 ≤ s2
      · exact False.elim (h32 h1.2)
      · by_cases h21 : s2 ≤ s1
        · have h31 : ¬ s3 ≤ s1 := by
            intro h31
            exact h0 ⟨h21, h31⟩
          simp [h32, h31]
        · simp [h21, h32]

@[simp] theorem bestRemainingAfter_rum3RankByScores_remove1
    (s1 s2 s3 : ℝ) :
    bestRemainingAfter (rum3RankByScores s1 s2 s3) (1 : Candidate 1) =
      if s3 ≤ s1 then (0 : Candidate 1) else (2 : Candidate 1) := by
  change
    (if firstChoice (rum3RankByScores s1 s2 s3) = (1 : Candidate 1) then
      secondChoice (rum3RankByScores s1 s2 s3)
    else firstChoice (rum3RankByScores s1 s2 s3)) =
      if s3 ≤ s1 then (0 : Candidate 1) else (2 : Candidate 1)
  by_cases h31 : s3 ≤ s1
  · by_cases h0 : s2 ≤ s1 ∧ s3 ≤ s1
    · simp [h0]
    · by_cases h1 : s1 < s2 ∧ s3 ≤ s2
      · simp [h1, h31]
      · by_cases h21 : s2 ≤ s1
        · exact False.elim (h0 ⟨h21, h31⟩)
        · exact False.elim
            (h1 ⟨lt_of_not_ge h21,
              le_trans h31 (le_of_lt (lt_of_not_ge h21))⟩)
  · by_cases h0 : s2 ≤ s1 ∧ s3 ≤ s1
    · exact False.elim (h31 h0.2)
    · by_cases h1 : s1 < s2 ∧ s3 ≤ s2
      · simp [h1, h31]
      · by_cases h21 : s2 ≤ s1 <;>
          simp [h1, h21, h31]

@[simp] theorem bestRemainingAfter_rum3RankByScores_remove2
    (s1 s2 s3 : ℝ) :
    bestRemainingAfter (rum3RankByScores s1 s2 s3) (2 : Candidate 1) =
      if s2 ≤ s1 then (0 : Candidate 1) else (1 : Candidate 1) := by
  change
    (if firstChoice (rum3RankByScores s1 s2 s3) = (2 : Candidate 1) then
      secondChoice (rum3RankByScores s1 s2 s3)
    else firstChoice (rum3RankByScores s1 s2 s3)) =
      if s2 ≤ s1 then (0 : Candidate 1) else (1 : Candidate 1)
  by_cases h21 : s2 ≤ s1
  · by_cases h0 : s2 ≤ s1 ∧ s3 ≤ s1
    · simp [h0]
    · by_cases h1 : s1 < s2 ∧ s3 ≤ s2
      · exact False.elim (not_lt_of_ge h21 h1.1)
      · have h31 : ¬ s3 ≤ s1 := by
          intro h31
          exact h0 ⟨h21, h31⟩
        simp [h1, h21, h31]
  · by_cases h0 : s2 ≤ s1 ∧ s3 ≤ s1
    · exact False.elim (h21 h0.1)
    · by_cases h1 : s1 < s2 ∧ s3 ≤ s2
      · simp [h1, h21]
      · by_cases h31 : s3 ≤ s1
        · have h1' : s1 < s2 ∧ s3 ≤ s2 :=
            ⟨lt_of_not_ge h21, le_trans h31 (le_of_lt (lt_of_not_ge h21))⟩
          exact False.elim (h1 h1')
        · simp [h1, h21]

theorem rum3RankByScores_firstChoice_of_top_scores
    {s1 s2 s3 : ℝ}
    (h : rum3TopFirstByScores s1 s2 s3) :
    firstChoice (rum3RankByScores s1 s2 s3) = (0 : Candidate 1) := by
  rcases h with ⟨h21, h31⟩
  rw [firstChoice_rum3RankByScores]
  simp [h21, h31]

theorem rum3RankByScores_top_scores_of_firstChoice
    {s1 s2 s3 : ℝ}
    (h : firstChoice (rum3RankByScores s1 s2 s3) = (0 : Candidate 1)) :
    rum3TopFirstByScores s1 s2 s3 := by
  rw [firstChoice_rum3RankByScores] at h
  by_cases h0 : s2 ≤ s1 ∧ s3 ≤ s1
  · simpa [rum3TopFirstByScores] using h0
  · by_cases h1 : s1 < s2 ∧ s3 ≤ s2
    · simp [h0, h1] at h
    · simp [h0, h1] at h

theorem rum3RankByScores_bottom_scores_of_firstChoice
    {s1 s2 s3 : ℝ}
    (h : firstChoice (rum3RankByScores s1 s2 s3) = (2 : Candidate 1)) :
    rum3BottomFirstByScores s1 s2 s3 := by
  rw [firstChoice_rum3RankByScores] at h
  by_cases h0 : s2 ≤ s1 ∧ s3 ≤ s1
  · simp [h0] at h
  · by_cases h1 : s1 < s2 ∧ s3 ≤ s2
    · simp [h0, h1] at h
    · constructor
      · by_contra hnot
        have h31 : s3 < s1 := lt_of_not_ge hnot
        by_cases h21 : s2 ≤ s1
        · exact h0 ⟨h21, le_of_lt h31⟩
        · have h12 : s1 < s2 := lt_of_not_ge h21
          exact h1 ⟨h12, le_trans (le_of_lt h31) (le_of_lt h12)⟩
      · by_contra hnot
        have h32 : s3 < s2 := lt_of_not_ge hnot
        by_cases h12 : s1 < s2
        · exact h1 ⟨h12, le_of_lt h32⟩
        · exact h0 ⟨le_of_not_gt h12,
            le_trans (le_of_lt h32) (le_of_not_gt h12)⟩

theorem rum3RankByScores_firstChoice_of_bottom_scores_of_noTies
    {s1 s2 s3 : ℝ}
    (hnt : rum3NoTiesByScores s1 s2 s3)
    (h : rum3BottomFirstByScores s1 s2 s3) :
    firstChoice (rum3RankByScores s1 s2 s3) = (2 : Candidate 1) := by
  rcases hnt with ⟨hne12, hne13, hne23⟩
  rcases h with ⟨h13, h23⟩
  have h31 : ¬ s3 ≤ s1 := by
    intro h31
    exact hne13 (le_antisymm h13 h31)
  have h32 : ¬ s3 ≤ s2 := by
    intro h32
    exact hne23 (le_antisymm h23 h32)
  rw [firstChoice_rum3RankByScores]
  have h0 : ¬(s2 ≤ s1 ∧ s3 ≤ s1) := by
    intro h0
    exact h31 h0.2
  have h1 : ¬(s1 < s2 ∧ s3 ≤ s2) := by
    intro h1
    exact h32 h1.2
  simp [h0, h1]

theorem rum3RankByScores_firstChoice_of_strict_bottom_scores
    {s1 s2 s3 : ℝ}
    (h13 : s1 < s3) (h23 : s2 < s3) :
    firstChoice (rum3RankByScores s1 s2 s3) = (2 : Candidate 1) := by
  rw [firstChoice_rum3RankByScores]
  have h0 : ¬(s2 ≤ s1 ∧ s3 ≤ s1) := by
    intro h0
    linarith
  have h1 : ¬(s1 < s2 ∧ s3 ≤ s2) := by
    intro h1
    linarith
  simp [h0, h1]

theorem rum3RankByScores_strict_bottom_scores_of_firstChoice
    {s1 s2 s3 : ℝ}
    (h : firstChoice (rum3RankByScores s1 s2 s3) = (2 : Candidate 1)) :
    s1 < s3 ∧ s2 < s3 := by
  rw [firstChoice_rum3RankByScores] at h
  by_cases h0 : s2 ≤ s1 ∧ s3 ≤ s1
  · simp [h0] at h
  · by_cases h1 : s1 < s2 ∧ s3 ≤ s2
    · simp [h0, h1] at h
    · constructor
      · by_contra hnot
        have h31 : s3 ≤ s1 := le_of_not_gt hnot
        by_cases h21 : s2 ≤ s1
        · exact h0 ⟨h21, h31⟩
        · have h12 : s1 < s2 := lt_of_not_ge h21
          exact h1 ⟨h12, le_trans h31 (le_of_lt h12)⟩
      · by_contra hnot
        have h32 : s3 ≤ s2 := le_of_not_gt hnot
        by_cases h12 : s1 < s2
        · exact h1 ⟨h12, h32⟩
        · exact h0 ⟨le_of_not_gt h12, le_trans h32 (le_of_not_gt h12)⟩

theorem rum3RankByScores_middle_scores_of_firstChoice
    {s1 s2 s3 : ℝ}
    (h : firstChoice (rum3RankByScores s1 s2 s3) = (1 : Candidate 1)) :
    rum3MiddleBeatsTopByScores s1 s2 s3 := by
  rw [firstChoice_rum3RankByScores] at h
  by_cases h0 : s2 ≤ s1 ∧ s3 ≤ s1
  · simp [h0] at h
  · by_cases h1 : s1 < s2 ∧ s3 ≤ s2
    · simpa [rum3MiddleBeatsTopByScores] using h1
    · simp [h0, h1] at h

theorem rum3RankByScores_remove0_eq1_imp_score23
    {s1 s2 s3 : ℝ}
    (h :
      bestRemainingAfter (rum3RankByScores s1 s2 s3) (0 : Candidate 1) =
        (1 : Candidate 1)) :
    s3 ≤ s2 := by
  by_contra h32
  simp [h32] at h

theorem rum3RankByScores_remove1_ne0_imp_score13
    {s1 s2 s3 : ℝ}
    (h :
      ¬ bestRemainingAfter (rum3RankByScores s1 s2 s3) (1 : Candidate 1) =
        (0 : Candidate 1)) :
    s1 < s3 := by
  by_contra h31
  exact h (by simp [le_of_not_gt h31])

theorem rum3RankByScores_remove1_eq0_of_score31
    {s1 s2 s3 : ℝ} (h31 : s3 ≤ s1) :
    bestRemainingAfter (rum3RankByScores s1 s2 s3) (1 : Candidate 1) =
      (0 : Candidate 1) := by
  simp [h31]

theorem rum3RankByScores_remove0_ne1_of_score23_lt
    {s1 s2 s3 : ℝ} (h23 : s2 < s3) :
    ¬ bestRemainingAfter (rum3RankByScores s1 s2 s3) (0 : Candidate 1) =
      (1 : Candidate 1) := by
  have h32 : ¬ s3 ≤ s2 := not_le_of_gt h23
  simp [h32]

theorem rum3RankByScores_remove0_eq2_imp_score23_lt
    {s1 s2 s3 : ℝ}
    (h :
      bestRemainingAfter (rum3RankByScores s1 s2 s3) (0 : Candidate 1) =
        (2 : Candidate 1)) :
    s2 < s3 := by
  by_contra h23
  have h32 : s3 ≤ s2 := le_of_not_gt h23
  simp [h32] at h

theorem rum3RankByScores_remove0_eq1_of_score32
    {s1 s2 s3 : ℝ} (h32 : s3 ≤ s2) :
    bestRemainingAfter (rum3RankByScores s1 s2 s3) (0 : Candidate 1) =
      (1 : Candidate 1) := by
  simp [h32]

theorem rum3RankByScores_remove2_eq1_imp_score12_lt
    {s1 s2 s3 : ℝ}
    (h :
      bestRemainingAfter (rum3RankByScores s1 s2 s3) (2 : Candidate 1) =
        (1 : Candidate 1)) :
    s1 < s2 := by
  by_contra h12
  have h21 : s2 ≤ s1 := le_of_not_gt h12
  simp [h21] at h

theorem rum3RankByScores_remove2_eq0_of_score21
    {s1 s2 s3 : ℝ} (h21 : s2 ≤ s1) :
    bestRemainingAfter (rum3RankByScores s1 s2 s3) (2 : Candidate 1) =
      (0 : Candidate 1) := by
  simp [h21]

end Ranking
end SocialChoice
end AppliedModelingLib
