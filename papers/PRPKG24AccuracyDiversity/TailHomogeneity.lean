import PRPKG24AccuracyDiversity.Representation
import PRPKG24AccuracyDiversity.TopKOracle
import PRPKG24AccuracyDiversity.Uniform
import PRPKG24AccuracyDiversity.Bernoulli
import PRPKG24AccuracyDiversity.BernoulliExchange
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open scoped BigOperators

namespace PRPKG24AccuracyDiversity

/--
Certificate for the auxiliary heterogeneous-Bernoulli asymptotic interface.

This is not a source-numbered paper theorem in arXiv:2307.15142v1. The earlier
unconditional target was too strong for heterogeneous success probabilities:
different Bernoulli tail bases should generally bias the limiting allocation.
Keep the endpoint as an explicit certificate until the exact source Theorem 3
log-share statement is formalized.
-/
structure HeterogeneousBernoulliUniformHomogeneityCertificate
    {T : ℕ} [NeZero T] (B : BernoulliSatisfactionModel T) : Prop where
  successProb_pos : ∀ t, 0 < B.successProb t
  successProb_lt_one : ∀ t, B.successProb t < 1
  likelihood_pos : ∀ t, 0 < B.likelihood t
  asymptotic_uniform :
    ConsumptionModel.AsymptoticHomogeneityTarget
      (fun _ => B.toConsumptionModel) (uniformProfile T) AppliedModelingLib.Math.ExactInvRate

/--
Auxiliary heterogeneous-Bernoulli asymptotic bridge from an explicit certificate.
-/
theorem heterogeneous_bernoulli_asymptotic_uniform_homogeneity
    {T : ℕ} [NeZero T] (B : BernoulliSatisfactionModel T)
    (hcert : HeterogeneousBernoulliUniformHomogeneityCertificate B) :
    ConsumptionModel.AsymptoticHomogeneityTarget
      (fun _ => B.toConsumptionModel) (uniformProfile T) AppliedModelingLib.Math.ExactInvRate := hcert.asymptotic_uniform

/--
The source Theorem 3 log-share weight for a Bernoulli type.

For success probability `q_t`, the paper's limiting representation is
proportional to `1 / log (1 / (1 - q_t))`.
-/
noncomputable def theorem3LogShareWeight {T : ℕ}
    (B : BernoulliSatisfactionModel T) (t : ItemType T) : ℝ := (Real.log ((1 - B.successProb t)⁻¹))⁻¹

/-- The positive logarithmic scale whose inverse is the Theorem 3 target weight. -/
noncomputable def theorem3LogScale {T : ℕ}
    (B : BernoulliSatisfactionModel T) (t : ItemType T) : ℝ := Real.log ((1 - B.successProb t)⁻¹)

/--
The source Theorem 3 target profile. The `gamma` field is unused here; the
paper's varying-success-probability theorem is a representation limit rather
than a likelihood-power homogeneity claim.
-/
noncomputable def theorem3LogShareProfile {T : ℕ}
    (B : BernoulliSatisfactionModel T) : GammaHomogeneityProfile T where
  gamma := 0
  targetWeight := theorem3LogShareWeight B

theorem theorem3LogShareWeight_pos {T : ℕ}
    (B : BernoulliSatisfactionModel T)
    (hprob_pos : ∀ t, 0 < B.successProb t)
    (hprob_lt_one : ∀ t, B.successProb t < 1)
    (t : ItemType T) :
    0 < theorem3LogShareWeight B t := by
  unfold theorem3LogShareWeight
  have hbase_pos : 0 < 1 - B.successProb t := by linarith [hprob_lt_one t]
  have hbase_lt_one : 1 - B.successProb t < 1 := by linarith [hprob_pos t]
  have hinv_gt_one : 1 < (1 - B.successProb t)⁻¹ :=
    (one_lt_inv₀ hbase_pos).2 hbase_lt_one
  exact inv_pos.mpr (Real.log_pos hinv_gt_one)

theorem theorem3LogScale_pos {T : ℕ}
    (B : BernoulliSatisfactionModel T)
    (hprob_pos : ∀ t, 0 < B.successProb t)
    (hprob_lt_one : ∀ t, B.successProb t < 1)
    (t : ItemType T) :
    0 < theorem3LogScale B t := by
  unfold theorem3LogScale
  have hbase_pos : 0 < 1 - B.successProb t := by linarith [hprob_lt_one t]
  have hbase_lt_one : 1 - B.successProb t < 1 := by linarith [hprob_pos t]
  have hinv_gt_one : 1 < (1 - B.successProb t)⁻¹ :=
    (one_lt_inv₀ hbase_pos).2 hbase_lt_one
  exact Real.log_pos hinv_gt_one

theorem theorem3LogShareWeight_eq_inv_logScale {T : ℕ}
    (B : BernoulliSatisfactionModel T) (t : ItemType T) :
    theorem3LogShareWeight B t = (theorem3LogScale B t)⁻¹ := by
  rfl

theorem count_div_theorem3LogShareWeight_eq_count_mul_logScale {T : ℕ}
    (B : BernoulliSatisfactionModel T)
    (hprob_pos : ∀ t, 0 < B.successProb t)
    (hprob_lt_one : ∀ t, B.successProb t < 1)
    (a : CountAllocation T) (t : ItemType T) :
    (a.count t : ℝ) / theorem3LogShareWeight B t =
      (a.count t : ℝ) * theorem3LogScale B t := by
  rw [theorem3LogShareWeight_eq_inv_logScale]
  field_simp [(ne_of_gt (theorem3LogScale_pos B hprob_pos hprob_lt_one t))]

/-- The finite log-likelihood offset appearing in the Theorem 3 Bernoulli FOC. -/
noncomputable def theorem3LogOffset {T : ℕ}
    (B : BernoulliSatisfactionModel T) (i j : ItemType T) : ℝ :=
  Real.log (B.likelihood i * B.successProb i) -
    Real.log (B.likelihood j * B.successProb j) +
    theorem3LogScale B i

/-- A finite bound for all pairwise log-likelihood offsets in Theorem 3. -/
noncomputable def theorem3LogOffsetBound {T : ℕ} [NeZero T]
    (B : BernoulliSatisfactionModel T) : ℝ :=
  AppliedModelingLib.finiteMax
    (fun p : ItemType T × ItemType T => theorem3LogOffset B p.1 p.2)

theorem theorem3LogOffset_le_bound {T : ℕ} [NeZero T]
    (B : BernoulliSatisfactionModel T) (i j : ItemType T) :
    theorem3LogOffset B i j ≤ theorem3LogOffsetBound B := by
  unfold theorem3LogOffsetBound
  exact AppliedModelingLib.le_finiteMax
    (fun p : ItemType T × ItemType T => theorem3LogOffset B p.1 p.2) (i, j)

theorem theorem3LogOffsetBound_pos {T : ℕ} [NeZero T]
    (B : BernoulliSatisfactionModel T)
    (hprob_pos : ∀ t, 0 < B.successProb t)
    (hprob_lt_one : ∀ t, B.successProb t < 1) :
    0 < theorem3LogOffsetBound B := by
  let t : ItemType T := ⟨0, Nat.pos_of_ne_zero (NeZero.ne T)⟩
  have hle : theorem3LogOffset B t t ≤ theorem3LogOffsetBound B :=
    theorem3LogOffset_le_bound B t t
  have hoff : theorem3LogOffset B t t = theorem3LogScale B t := by
    unfold theorem3LogOffset
    ring
  exact lt_of_lt_of_le
    (theorem3LogScale_pos B hprob_pos hprob_lt_one t)
    (by simpa [hoff] using hle)

/-- The minimum Theorem 3 target weight across the finite type set. -/
noncomputable def theorem3LogShareWeightMin {T : ℕ} [NeZero T]
    (B : BernoulliSatisfactionModel T) : ℝ := AppliedModelingLib.finiteMin (theorem3LogShareWeight B)

theorem theorem3LogShareWeightMin_pos {T : ℕ} [NeZero T]
    (B : BernoulliSatisfactionModel T)
    (hprob_pos : ∀ t, 0 < B.successProb t)
    (hprob_lt_one : ∀ t, B.successProb t < 1) :
    0 < theorem3LogShareWeightMin B := by
  unfold theorem3LogShareWeightMin
  exact AppliedModelingLib.finiteMin_pos (theorem3LogShareWeight B)
    (theorem3LogShareWeight_pos B hprob_pos hprob_lt_one)

theorem theorem3LogShareWeightMin_le {T : ℕ} [NeZero T]
    (B : BernoulliSatisfactionModel T) (t : ItemType T) :
    theorem3LogShareWeightMin B ≤ theorem3LogShareWeight B t := by
  unfold theorem3LogShareWeightMin
  exact AppliedModelingLib.finiteMin_le (theorem3LogShareWeight B) t

/-- Generic small-`N` scaled-count bound from the finite positive weight floor. -/
noncomputable def theorem3SmallNScaledBound {T : ℕ} [NeZero T]
    (B : BernoulliSatisfactionModel T) (threshold : ℕ) : ℝ := 2 * ((threshold : ℝ) / theorem3LogShareWeightMin B)

theorem theorem3SmallNScaledBound_nonneg {T : ℕ} [NeZero T]
    (B : BernoulliSatisfactionModel T) (threshold : ℕ)
    (hprob_pos : ∀ t, 0 < B.successProb t)
    (hprob_lt_one : ∀ t, B.successProb t < 1) :
    0 ≤ theorem3SmallNScaledBound B threshold := by
  unfold theorem3SmallNScaledBound
  have hmin_pos := theorem3LogShareWeightMin_pos B hprob_pos hprob_lt_one
  exact mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
    (div_nonneg (Nat.cast_nonneg threshold) (le_of_lt hmin_pos))

theorem theorem3_scaled_count_pairwise_abs_le_of_total_lt
    {T : ℕ} [NeZero T] (B : BernoulliSatisfactionModel T)
    (hprob_pos : ∀ t, 0 < B.successProb t)
    (hprob_lt_one : ∀ t, B.successProb t < 1)
    (a : CountAllocation T) {N threshold : ℕ}
    (htotal : AppliedModelingLib.Allocation.total a = N)
    (hNlt : N < threshold) :
    ∀ i j,
      |(a.count i : ℝ) / theorem3LogShareWeight B i -
        (a.count j : ℝ) / theorem3LogShareWeight B j| ≤
        theorem3SmallNScaledBound B threshold := by
  intro i j
  have hmin_pos := theorem3LogShareWeightMin_pos B hprob_pos hprob_lt_one
  simpa [theorem3SmallNScaledBound] using
    AppliedModelingLib.Allocation.pairwise_scaled_abs_le_of_total_lt
      (a := a) (weight := theorem3LogShareWeight B)
      (N := N) (threshold := threshold)
      (weightFloor := theorem3LogShareWeightMin B)
      htotal hNlt hmin_pos (fun t => theorem3LogShareWeightMin_le B t) i j

/--
If the total count is larger than `T * K`, at least one type has count larger
than `K`.
-/
theorem exists_count_gt_of_card_mul_lt_total
    {T : ℕ} [NeZero T] (a : CountAllocation T) {K : ℕ}
    (hgt : T * K < AppliedModelingLib.Allocation.total a) :
    ∃ t : ItemType T, K < a.count t := by
  have hgt' :
      Fintype.card (ItemType T) * K < AppliedModelingLib.Allocation.total a := by
    simpa [Fintype.card_fin] using hgt
  exact AppliedModelingLib.Allocation.exists_count_gt_of_card_mul_lt_total a hgt'

theorem theorem3LogShareProfile_normalizer_pos {T : ℕ} [NeZero T]
    (B : BernoulliSatisfactionModel T)
    (hprob_pos : ∀ t, 0 < B.successProb t)
    (hprob_lt_one : ∀ t, B.successProb t < 1) :
    0 < (theorem3LogShareProfile B).normalizer := by
  unfold theorem3LogShareProfile GammaHomogeneityProfile.normalizer
  exact Finset.sum_pos
    (fun t _ => theorem3LogShareWeight_pos B hprob_pos hprob_lt_one t)
    Finset.univ_nonempty

theorem theorem3LogShareProfile_normalizer_ne_zero {T : ℕ} [NeZero T]
    (B : BernoulliSatisfactionModel T)
    (hprob_pos : ∀ t, 0 < B.successProb t)
    (hprob_lt_one : ∀ t, B.successProb t < 1) :
    (theorem3LogShareProfile B).normalizer ≠ 0 := ne_of_gt (theorem3LogShareProfile_normalizer_pos B hprob_pos hprob_lt_one)

theorem theorem3LogShareProfile_targetShare_eq {T : ℕ} [NeZero T]
    (B : BernoulliSatisfactionModel T)
    (hprob_pos : ∀ t, 0 < B.successProb t)
    (hprob_lt_one : ∀ t, B.successProb t < 1)
    (t : ItemType T) :
    (theorem3LogShareProfile B).targetShare t =
      theorem3LogShareWeight B t /
        ∑ i : ItemType T, theorem3LogShareWeight B i :=
   GammaHomogeneityProfile.targetShare_eq_div_of_normalizer_ne_zero
    (G := theorem3LogShareProfile B) (t := t)
    (theorem3LogShareProfile_normalizer_ne_zero B hprob_pos hprob_lt_one)

theorem theorem3LogShareWeight_lt_of_successProb_gt {T : ℕ}
    (B : BernoulliSatisfactionModel T)
    (hprob_pos : ∀ t, 0 < B.successProb t)
    (hprob_lt_one : ∀ t, B.successProb t < 1)
    {i j : ItemType T}
    (hij : B.successProb i < B.successProb j) :
    theorem3LogShareWeight B j < theorem3LogShareWeight B i := by
  unfold theorem3LogShareWeight
  have hbase_i_pos : 0 < 1 - B.successProb i := by linarith [hprob_lt_one i]
  have hbase_j_pos : 0 < 1 - B.successProb j := by linarith [hprob_lt_one j]
  have hbase_j_lt_i : 1 - B.successProb j < 1 - B.successProb i := by linarith
  have hinv_lt : (1 - B.successProb i)⁻¹ < (1 - B.successProb j)⁻¹ :=
    (inv_lt_inv₀ hbase_i_pos hbase_j_pos).2 hbase_j_lt_i
  have hinv_i_gt_one : 1 < (1 - B.successProb i)⁻¹ :=
    (one_lt_inv₀ hbase_i_pos).2 (by linarith [hprob_pos i])
  have hinv_j_gt_one : 1 < (1 - B.successProb j)⁻¹ :=
    (one_lt_inv₀ hbase_j_pos).2 (by linarith [hprob_pos j])
  have hlog_i_pos : 0 < Real.log ((1 - B.successProb i)⁻¹) :=
    Real.log_pos hinv_i_gt_one
  have hlog_j_pos : 0 < Real.log ((1 - B.successProb j)⁻¹) :=
    Real.log_pos hinv_j_gt_one
  have hlog_lt :
      Real.log ((1 - B.successProb i)⁻¹) <
        Real.log ((1 - B.successProb j)⁻¹) :=
    Real.log_lt_log (inv_pos.mpr hbase_i_pos) hinv_lt
  exact (inv_lt_inv₀ hlog_j_pos hlog_i_pos).2 hlog_lt

/-- The all-consumed Bernoulli objective from Theorem 3's `S_{n,n}` statement. -/
noncomputable def bernoulliAllConsumedModel {T : ℕ}
    (B : BernoulliSatisfactionModel T) : ConsumptionModel T := ConsumptionModel.linearized B.likelihood B.successProb

/-- Allocation putting all `N` recommendations on one type. -/
def allOnTypeAllocation {T : ℕ} (N : ℕ) (best : ItemType T) :
    CountAllocation T :=
  AppliedModelingLib.Allocation.allOnTypeAllocation N best

@[simp] theorem allOnTypeAllocation_self {T : ℕ}
    (N : ℕ) (best : ItemType T) :
    (allOnTypeAllocation N best).count best = N := by
  simp [allOnTypeAllocation]

theorem allOnTypeAllocation_of_ne {T : ℕ}
    (N : ℕ) {best t : ItemType T} (hne : t ≠ best) :
    (allOnTypeAllocation N best).count t = 0 := by
  simpa [allOnTypeAllocation] using
    AppliedModelingLib.Allocation.allOnTypeAllocation_of_ne (κ := ItemType T) N (best := best)
      (k := t) hne

theorem allOnTypeAllocation_total {T : ℕ}
    (N : ℕ) (best : ItemType T) :
    AppliedModelingLib.Allocation.total (allOnTypeAllocation N best) = N := by
  simp [allOnTypeAllocation]

theorem linearized_objective_eq_sum_count_mul_score {T : ℕ}
    (likelihood perItemValue : ItemType T → ℝ) (a : CountAllocation T) :
    (ConsumptionModel.linearized likelihood perItemValue).objective a =
      ∑ t : ItemType T, (a.count t : ℝ) * (likelihood t * perItemValue t) := by
  simpa [ConsumptionModel.objective, ConsumptionModel.linearized,
    ConsumptionModel.linearValueOfCount] using
    AppliedModelingLib.Allocation.objective_linearValueOfCount_eq_sum_count_mul_score
      likelihood perItemValue a

/--
For a linear all-consumed objective, putting all mass on a maximizing type is
optimal.
-/
theorem allOnTypeAllocation_linearized_isOptimalAtTotal {T : ℕ}
    (likelihood perItemValue : ItemType T → ℝ) (N : ℕ) (best : ItemType T)
    (hbest :
      ∀ t, likelihood t * perItemValue t ≤ likelihood best * perItemValue best) :
    (ConsumptionModel.linearized likelihood perItemValue).IsOptimalAtTotal
      N (allOnTypeAllocation N best) := by
  simpa [ConsumptionModel.IsOptimalAtTotal, ConsumptionModel.FeasibleAtTotal,
    ConsumptionModel.objective, ConsumptionModel.linearized,
    ConsumptionModel.linearValueOfCount, allOnTypeAllocation] using
    AppliedModelingLib.Allocation.allOnTypeAllocation_isOptimalAtTotal_linearValueOfCount
      likelihood perItemValue N best hbest

/--
For a linear all-consumed objective, a type whose per-item score is strictly
below another type's score receives zero count in every optimum.
-/
theorem linearized_optimal_count_eq_zero_of_strict_score_lt
    {T : ℕ} {likelihood perItemValue : ItemType T → ℝ}
    {N : ℕ} {a : CountAllocation T} {t best : ItemType T}
    (hopt :
      (ConsumptionModel.linearized likelihood perItemValue).IsOptimalAtTotal
        N a)
    (hstrict :
      likelihood t * perItemValue t <
        likelihood best * perItemValue best) :
    a.count t = 0 := by
  exact
    AppliedModelingLib.Allocation.count_eq_zero_of_isOptimalAtTotal_linearValueOfCount_of_strict_score_lt
      (weight := likelihood) (perUnitValue := perItemValue) (N := N) (a := a)
      (k := t) (best := best)
      (by
        simpa [ConsumptionModel.IsOptimalAtTotal, ConsumptionModel.FeasibleAtTotal,
          ConsumptionModel.objective, ConsumptionModel.linearized,
          ConsumptionModel.linearValueOfCount] using hopt)
      hstrict

/--
Theorem 3's all-consumed side: an argmax of `p_t q_t` supports an optimal
allocation using only that type.
-/
theorem bernoulli_all_consumed_argmax_isOptimalAtTotal
    {T : ℕ} (B : BernoulliSatisfactionModel T) (N : ℕ) (best : ItemType T)
    (hbest :
      ∀ t, B.likelihood t * B.successProb t ≤
        B.likelihood best * B.successProb best) :
    (bernoulliAllConsumedModel B).IsOptimalAtTotal
      N (allOnTypeAllocation N best) :=
   allOnTypeAllocation_linearized_isOptimalAtTotal
    B.likelihood B.successProb N best hbest

/--
Certificate for source Theorem 3's varying-success-probability log-share limit.

The remaining proof obligation is the paper's finite rounding seam: every
positive-size optimum is within a constant count error of the log-share target.
`AsymptoticHomogeneityTarget.of_uniform_count_abs_error` converts this to the
paper-style exact `C / N` asymptotic target.
-/
structure VaryingBernoulliLogShareCertificate
    {T : ℕ} [NeZero T] (B : BernoulliSatisfactionModel T) where
  successProb_pos : ∀ t, 0 < B.successProb t
  successProb_lt_one : ∀ t, B.successProb t < 1
  likelihood_pos : ∀ t, 0 < B.likelihood t
  count_bound : ℝ
  count_bound_pos : 0 < count_bound
  count_close :
    ∀ N (a : CountAllocation T), 0 < N →
      B.toConsumptionModel.IsOptimalAtTotal N a →
      ∀ t,
        |(a.count t : ℝ) -
          (N : ℝ) * (theorem3LogShareProfile B).targetShare t| ≤ count_bound

/--
Intermediate Theorem 3 certificate: optimal scaled counts are pairwise bounded.

Here the scaling is by the paper's target weight
`1 / log (1 / (1 - q_t))`.  The averaging lemma in `Representation.lean`
turns this pairwise finite statement into the count-closeness certificate above.
-/
structure VaryingBernoulliPairwiseScaledCertificate
    {T : ℕ} [NeZero T] (B : BernoulliSatisfactionModel T) where
  successProb_pos : ∀ t, 0 < B.successProb t
  successProb_lt_one : ∀ t, B.successProb t < 1
  likelihood_pos : ∀ t, 0 < B.likelihood t
  scaled_bound : ℝ
  scaled_bound_pos : 0 < scaled_bound
  pairwise_scaled :
    ∀ N (a : CountAllocation T), 0 < N →
      B.toConsumptionModel.IsOptimalAtTotal N a →
      ∀ i j,
        |(a.count i : ℝ) / theorem3LogShareWeight B i -
          (a.count j : ℝ) / theorem3LogShareWeight B j| ≤ scaled_bound

/--
Interior optimizer certificate for the Theorem 3 Bernoulli proof seam.

The Bernoulli FOC proves the log-scaled pairwise bound once every optimal
allocation gives each type at least one item.  The paper proof only needs this
eventually, with finite small-`N` handling; this certificate records the
stronger all-positive-size version as a precise intermediate target.
-/
structure VaryingBernoulliPositiveCountCertificate
    {T : ℕ} [NeZero T] (B : BernoulliSatisfactionModel T) where
  successProb_pos : ∀ t, 0 < B.successProb t
  successProb_lt_one : ∀ t, B.successProb t < 1
  likelihood_pos : ∀ t, 0 < B.likelihood t
  positive_counts :
    ∀ N (a : CountAllocation T), 0 < N →
      B.toConsumptionModel.IsOptimalAtTotal N a →
      ∀ t, 0 < a.count t

/--
Eventual interior optimizer certificate for the Theorem 3 Bernoulli proof seam.

This matches the asymptotic shape needed by the paper more closely than
`VaryingBernoulliPositiveCountCertificate`: after a finite threshold, optimal
allocations must put positive count on every type.  A generic finite-prefix
bound handles smaller `N`.
-/
structure VaryingBernoulliEventualPositiveCountCertificate
    {T : ℕ} [NeZero T] (B : BernoulliSatisfactionModel T) where
  successProb_pos : ∀ t, 0 < B.successProb t
  successProb_lt_one : ∀ t, B.successProb t < 1
  likelihood_pos : ∀ t, 0 < B.likelihood t
  interior_threshold : ℕ
  positive_counts_eventually :
    ∀ N (a : CountAllocation T), 0 < N → interior_threshold ≤ N →
      B.toConsumptionModel.IsOptimalAtTotal N a →
      ∀ t, 0 < a.count t

/--
Large-count marginal dominance certificate for Theorem 3 eventual interior.

The analytic tail step still to be closed is to prove such a `count_threshold`
from `0 < q_t < 1`: after enough recommendations of any source type, its last
Bernoulli marginal is below the first marginal of every destination type.
-/
structure VaryingBernoulliLargeCountDominanceCertificate
    {T : ℕ} [NeZero T] (B : BernoulliSatisfactionModel T) where
  successProb_pos : ∀ t, 0 < B.successProb t
  successProb_lt_one : ∀ t, B.successProb t < 1
  likelihood_pos : ∀ t, 0 < B.likelihood t
  count_threshold : ℕ
  backward_lt_first :
    ∀ src dst q, count_threshold < q →
      B.likelihood src * B.successProb src *
          (1 - B.successProb src) ^ (q - 1) <
        B.likelihood dst * B.successProb dst

/--
For a fixed source/destination pair, Bernoulli tail decay eventually makes the
source's last-item marginal smaller than the destination's first-item marginal.
-/
theorem bernoulli_pair_large_count_dominance_exists
    {T : ℕ} (B : BernoulliSatisfactionModel T)
    (src dst : ItemType T)
    (hprob_pos_src : 0 < B.successProb src)
    (hprob_lt_one_src : B.successProb src < 1)
    (hlike_pos_src : 0 < B.likelihood src)
    (hlike_pos_dst : 0 < B.likelihood dst)
    (hprob_pos_dst : 0 < B.successProb dst) :
    ∃ K : ℕ, ∀ q, K < q →
      B.likelihood src * B.successProb src *
          (1 - B.successProb src) ^ (q - 1) <
        B.likelihood dst * B.successProb dst := by
  let A : ℝ := B.likelihood src * B.successProb src
  let D : ℝ := B.likelihood dst * B.successProb dst
  have hA_pos : 0 < A := by
    dsimp [A]
    exact mul_pos hlike_pos_src hprob_pos_src
  have hD_pos : 0 < D := by
    dsimp [D]
    exact mul_pos hlike_pos_dst hprob_pos_dst
  have hbase_pos : 0 < 1 - B.successProb src := by
    linarith
  have hbase_lt_one : 1 - B.successProb src < 1 := by
    linarith
  have hratio_pos : 0 < D / A := div_pos hD_pos hA_pos
  obtain ⟨K, hK⟩ :=
    exists_pow_lt_of_lt_one (x := D / A) (y := 1 - B.successProb src)
      hratio_pos hbase_lt_one
  refine ⟨K, ?_⟩
  intro q hKq
  have hK_le_pred : K ≤ q - 1 := Nat.le_sub_one_of_lt hKq
  have hpow_le :
      (1 - B.successProb src) ^ (q - 1) ≤
        (1 - B.successProb src) ^ K :=
    pow_le_pow_of_le_one hbase_pos.le hbase_lt_one.le hK_le_pred
  have hmul_le :
      A * (1 - B.successProb src) ^ (q - 1) ≤
        A * (1 - B.successProb src) ^ K :=
    mul_le_mul_of_nonneg_left hpow_le (le_of_lt hA_pos)
  have hmul_lt : A * (1 - B.successProb src) ^ (q - 1) < A * (D / A) :=
    lt_of_le_of_lt hmul_le (mul_lt_mul_of_pos_left hK hA_pos)
  have hcancel : A * (D / A) = D := by
    field_simp [ne_of_gt hA_pos]
  simpa [A, D, mul_assoc, hcancel] using hmul_lt

/--
Primitive positive Bernoulli parameters supply the large-count dominance
certificate by taking the finite maximum of the pairwise tail thresholds.
-/
noncomputable def varying_bernoulli_large_count_dominance_certificate_of_primitive
    {T : ℕ} [NeZero T] (B : BernoulliSatisfactionModel T)
    (hprob_pos : ∀ t, 0 < B.successProb t)
    (hprob_lt_one : ∀ t, B.successProb t < 1)
    (hlike_pos : ∀ t, 0 < B.likelihood t) :
    VaryingBernoulliLargeCountDominanceCertificate B := by
  classical
  let pairThreshold : ItemType T × ItemType T → ℕ := fun p =>
    Classical.choose
      (bernoulli_pair_large_count_dominance_exists B p.1 p.2
        (hprob_pos p.1) (hprob_lt_one p.1) (hlike_pos p.1)
        (hlike_pos p.2) (hprob_pos p.2))
  let K : ℕ :=
    (Finset.univ : Finset (ItemType T × ItemType T)).sup pairThreshold
  refine
    { successProb_pos := hprob_pos
      successProb_lt_one := hprob_lt_one
      likelihood_pos := hlike_pos
      count_threshold := K
      backward_lt_first := ?_ }
  intro src dst q hKq
  have hp_le_K : pairThreshold (src, dst) ≤ K := by
    dsimp [K]
    exact Finset.le_sup (by simp : (src, dst) ∈
      (Finset.univ : Finset (ItemType T × ItemType T)))
  have hpq : pairThreshold (src, dst) < q := Nat.lt_of_le_of_lt hp_le_K hKq
  exact
    (Classical.choose_spec
      (bernoulli_pair_large_count_dominance_exists B src dst
        (hprob_pos src) (hprob_lt_one src) (hlike_pos src)
        (hlike_pos dst) (hprob_pos dst))) q hpq

/--
Pairwise large-count marginal dominance implies eventual positive counts for
all finite optima.
-/
noncomputable def
    varying_bernoulli_eventual_positive_count_certificate_of_large_count_dominance
    {T : ℕ} [NeZero T] (B : BernoulliSatisfactionModel T)
    (hcert : VaryingBernoulliLargeCountDominanceCertificate B) :
    VaryingBernoulliEventualPositiveCountCertificate B where
  successProb_pos := hcert.successProb_pos
  successProb_lt_one := hcert.successProb_lt_one
  likelihood_pos := hcert.likelihood_pos
  interior_threshold := T * hcert.count_threshold + 1
  positive_counts_eventually := by
    intro N a _hN hlarge hopt dst
    by_contra hnot_pos
    have hdst_zero : a.count dst = 0 := Nat.eq_zero_of_not_pos hnot_pos
    have htotal_gt : T * hcert.count_threshold < AppliedModelingLib.Allocation.total a := by
      rw [hopt.1]
      exact Nat.lt_of_succ_le hlarge
    obtain ⟨src, hsrc_gt⟩ :=
      exists_count_gt_of_card_mul_lt_total a htotal_gt
    have hcan : AppliedModelingLib.Allocation.CanMoveOne a src :=
      Nat.lt_of_le_of_lt (Nat.zero_le hcert.count_threshold) hsrc_gt
    have hne : src ≠ dst := by
      intro hsd
      subst dst
      rw [hdst_zero] at hsrc_gt
      exact Nat.not_lt_zero _ hsrc_gt
    have hfoc :=
      BernoulliSatisfactionModel.forwardMarginal_le_backwardMarginal_of_optimum
        B N hopt hne hcan
    have hfirst_le :
        B.likelihood dst * B.successProb dst ≤
          B.likelihood src * B.successProb src *
            (1 - B.successProb src) ^ (a.count src - 1) := by
      simpa [hdst_zero] using hfoc
    have hstrict :=
      hcert.backward_lt_first src dst (a.count src) hsrc_gt
    exact (not_lt_of_ge hfirst_le) hstrict

/--
Pairwise bounded scaled counts supply the finite count-closeness certificate for
Theorem 3.
-/
noncomputable def varying_bernoulli_log_share_certificate_of_pairwise_scaled
    {T : ℕ} [NeZero T] (B : BernoulliSatisfactionModel T)
    (hcert : VaryingBernoulliPairwiseScaledCertificate B) :
    VaryingBernoulliLogShareCertificate B where
  successProb_pos := hcert.successProb_pos
  successProb_lt_one := hcert.successProb_lt_one
  likelihood_pos := hcert.likelihood_pos
  count_bound := hcert.scaled_bound * (theorem3LogShareProfile B).normalizer
  count_bound_pos :=
    mul_pos hcert.scaled_bound_pos
      (theorem3LogShareProfile_normalizer_pos B
        hcert.successProb_pos hcert.successProb_lt_one)
  count_close := by
    intro N a hN hopt t
    have hNsum : (∑ i : ItemType T, (a.count i : ℝ)) = (N : ℝ) := by
      rw [← Nat.cast_sum]
      exact_mod_cast hopt.1
    have hweight_pos : ∀ i, 0 < theorem3LogShareWeight B i :=
      theorem3LogShareWeight_pos B hcert.successProb_pos hcert.successProb_lt_one
    have hscaled :=
      GammaHomogeneityProfile.count_abs_sub_weighted_average_le_of_pairwise_scaled_bounded
        a (theorem3LogShareWeight B) hNsum hweight_pos
        (le_of_lt hcert.scaled_bound_pos) (hcert.pairwise_scaled N a hN hopt) t
    have htarget :
        (N : ℝ) * (theorem3LogShareProfile B).targetShare t =
          theorem3LogShareWeight B t *
            ((N : ℝ) / ∑ i : ItemType T, theorem3LogShareWeight B i) := by
      rw [theorem3LogShareProfile_targetShare_eq B
        hcert.successProb_pos hcert.successProb_lt_one t]
      ring
    have hweight_le_norm :
        theorem3LogShareWeight B t ≤ (theorem3LogShareProfile B).normalizer := by
      unfold theorem3LogShareProfile GammaHomogeneityProfile.normalizer
      exact Finset.single_le_sum
        (fun i _ => le_of_lt (hweight_pos i)) (Finset.mem_univ t)
    calc
      |(a.count t : ℝ) - (N : ℝ) * (theorem3LogShareProfile B).targetShare t|
          = |(a.count t : ℝ) -
              theorem3LogShareWeight B t *
                ((N : ℝ) / ∑ i : ItemType T, theorem3LogShareWeight B i)| := by
            rw [htarget]
      _ ≤ hcert.scaled_bound * theorem3LogShareWeight B t := hscaled
      _ ≤ hcert.scaled_bound * (theorem3LogShareProfile B).normalizer :=
            mul_le_mul_of_nonneg_left hweight_le_norm
              (le_of_lt hcert.scaled_bound_pos)

/-- Source Theorem 3 target with the explicit finite-rate certificate exposed. -/
theorem varying_bernoulli_log_share_exact_rate_of_certificate
    {T : ℕ} [NeZero T] (B : BernoulliSatisfactionModel T)
    (hcert : VaryingBernoulliLogShareCertificate B) :
    ConsumptionModel.AsymptoticHomogeneityTarget
      (fun _ => B.toConsumptionModel) (theorem3LogShareProfile B)
      AppliedModelingLib.Math.ExactInvRate :=
  ConsumptionModel.AsymptoticHomogeneityTarget.of_uniform_count_abs_error
    hcert.count_bound_pos hcert.count_close

/-- Source Theorem 3 target as a plain asymptotic representation statement. -/
theorem varying_bernoulli_log_share_asymptotic_of_certificate
    {T : ℕ} [NeZero T] (B : BernoulliSatisfactionModel T)
    (hcert : VaryingBernoulliLogShareCertificate B) :
    ConsumptionModel.AsymptoticHomogeneity
      (fun _ => B.toConsumptionModel) (theorem3LogShareProfile B) :=
  ConsumptionModel.AsymptoticHomogeneityTarget.of_exactInvRate
    (varying_bernoulli_log_share_exact_rate_of_certificate B hcert)

/--
The core finite lemma for the heterogeneous-Bernoulli auxiliary interface:
If marginals are `L * p * (1-p)^q`, then the optimal counts stay within a
constant distance of each other.
-/
theorem bernoulli_optimum_pairwise_difference_bounded
    {T : ℕ} (B : BernoulliSatisfactionModel T) (N : ℕ)
    {a : CountAllocation T}
    (hopt : B.toConsumptionModel.IsOptimalAtTotal N a)
    (hprob_pos : ∀ t, 0 < B.successProb t)
    (hprob_lt_one : ∀ t, B.successProb t < 1)
    (hlike_pos : ∀ t, 0 < B.likelihood t) :
    ∀ t₁ t₂,
      0 < a.count t₁ →
      (a.count t₁ : ℝ) - 1 ≤
        (Real.log (B.likelihood t₂ * B.successProb t₂) -
         Real.log (B.likelihood t₁ * B.successProb t₁) +
         (a.count t₂ : ℝ) * Real.log (1 - B.successProb t₂)) /
        Real.log (1 - B.successProb t₁) := by
  intro t₁ t₂ ha1
  by_cases hne : t₁ = t₂
  · subst t₂
    have hbase1 : 0 < 1 - B.successProb t₁ := by linarith [hprob_lt_one t₁]
    have hprob1 : 1 - B.successProb t₁ < 1 := by linarith [hprob_pos t₁]
    have hlog_neg : Real.log (1 - B.successProb t₁) < 0 := Real.log_neg hbase1 hprob1
    have h1 : Real.log (B.likelihood t₁ * B.successProb t₁) - Real.log (B.likelihood t₁ * B.successProb t₁) = 0 := sub_self _
    rw [h1, zero_add]
    have h2 : ((a.count t₁ : ℝ) * Real.log (1 - B.successProb t₁)) / Real.log (1 - B.successProb t₁) = (a.count t₁ : ℝ) :=
      mul_div_cancel_right₀ (↑(a.count t₁)) hlog_neg.ne
    rw [h2]
    linarith
  · have hcan : AppliedModelingLib.Allocation.CanMoveOne a t₁ := ha1
    have hfoc := BernoulliSatisfactionModel.forwardMarginal_le_backwardMarginal_of_optimum B N hopt hne hcan
    have h_lp1_pos : 0 < B.likelihood t₁ * B.successProb t₁ := mul_pos (hlike_pos t₁) (hprob_pos t₁)
    have h_lp2_pos : 0 < B.likelihood t₂ * B.successProb t₂ := mul_pos (hlike_pos t₂) (hprob_pos t₂)
    have h_base1 : 0 < 1 - B.successProb t₁ := by linarith [hprob_lt_one t₁]
    have h_base2 : 0 < 1 - B.successProb t₂ := by linarith [hprob_lt_one t₂]
    have h_prob1 : 1 - B.successProb t₁ < 1 := by linarith [hprob_pos t₁]
    have h_log1_neg : Real.log (1 - B.successProb t₁) < 0 := Real.log_neg h_base1 h_prob1
    -- log(L2*p2*(1-p2)^q2) <= log(L1*p1*(1-p1)^(q1-1))
    have hlog_le : Real.log (B.likelihood t₂ * B.successProb t₂ * (1 - B.successProb t₂) ^ (a.count t₂)) ≤
                   Real.log (B.likelihood t₁ * B.successProb t₁ * (1 - B.successProb t₁) ^ (a.count t₁ - 1)) := by
      apply Real.log_le_log
      · positivity
      · exact hfoc
    rw [Real.log_mul h_lp2_pos.ne.symm (pow_pos h_base2 _).ne.symm] at hlog_le
    rw [Real.log_mul h_lp1_pos.ne.symm (pow_pos h_base1 _).ne.symm] at hlog_le
    rw [Real.log_pow, Real.log_pow] at hlog_le
    rw [Nat.cast_sub ha1] at hlog_le
    push_cast at hlog_le
    -- log(L2*p2) + q2 * log(1-p2) <= log(L1*p1) + (q1-1) * log(1-p1)
    have h_rearrange : (a.count t₁ : ℝ) - 1 ≤
        (Real.log (B.likelihood t₂ * B.successProb t₂) - Real.log (B.likelihood t₁ * B.successProb t₁) + (a.count t₂ : ℝ) * Real.log (1 - B.successProb t₂)) /
        Real.log (1 - B.successProb t₁) := by
      rw [le_div_iff_of_neg h_log1_neg]
      linarith
    exact h_rearrange

/--
Bernoulli first-order condition in the logarithmic scale used by source
Theorem 3. This is the finite inequality behind the paper's relaxed-optimum
calculation.
-/
theorem bernoulli_optimum_log_scaled_count_pairwise_upper
    {T : ℕ} (B : BernoulliSatisfactionModel T) (N : ℕ)
    {a : CountAllocation T}
    (hopt : B.toConsumptionModel.IsOptimalAtTotal N a)
    (hprob_pos : ∀ t, 0 < B.successProb t)
    (hprob_lt_one : ∀ t, B.successProb t < 1)
    (hlike_pos : ∀ t, 0 < B.likelihood t) :
    ∀ src dst,
      0 < a.count src →
      (a.count src : ℝ) * theorem3LogScale B src -
        (a.count dst : ℝ) * theorem3LogScale B dst ≤
        Real.log (B.likelihood src * B.successProb src) -
          Real.log (B.likelihood dst * B.successProb dst) +
          theorem3LogScale B src := by
  intro src dst hsrc_pos
  by_cases hne : src = dst
  · subst dst
    have hscale_pos := theorem3LogScale_pos B hprob_pos hprob_lt_one src
    linarith
  · have hcan : AppliedModelingLib.Allocation.CanMoveOne a src := hsrc_pos
    have hfoc :=
      BernoulliSatisfactionModel.forwardMarginal_le_backwardMarginal_of_optimum
        B N hopt hne hcan
    have h_lp_src_pos : 0 < B.likelihood src * B.successProb src :=
      mul_pos (hlike_pos src) (hprob_pos src)
    have h_lp_dst_pos : 0 < B.likelihood dst * B.successProb dst :=
      mul_pos (hlike_pos dst) (hprob_pos dst)
    have h_base_src : 0 < 1 - B.successProb src := by linarith [hprob_lt_one src]
    have h_base_dst : 0 < 1 - B.successProb dst := by linarith [hprob_lt_one dst]
    have hlog_le :
        Real.log
            (B.likelihood dst * B.successProb dst *
              (1 - B.successProb dst) ^ (a.count dst)) ≤
          Real.log
            (B.likelihood src * B.successProb src *
              (1 - B.successProb src) ^ (a.count src - 1)) := by
      apply Real.log_le_log
      · positivity
      · exact hfoc
    rw [Real.log_mul h_lp_dst_pos.ne.symm (pow_pos h_base_dst _).ne.symm] at hlog_le
    rw [Real.log_mul h_lp_src_pos.ne.symm (pow_pos h_base_src _).ne.symm] at hlog_le
    rw [Real.log_pow, Real.log_pow] at hlog_le
    rw [Nat.cast_sub hsrc_pos] at hlog_le
    push_cast at hlog_le
    have hlog_src :
        Real.log (1 - B.successProb src) = -theorem3LogScale B src := by
      unfold theorem3LogScale
      rw [Real.log_inv]
      ring
    have hlog_dst :
        Real.log (1 - B.successProb dst) = -theorem3LogScale B dst := by
      unfold theorem3LogScale
      rw [Real.log_inv]
      ring
    rw [hlog_src, hlog_dst] at hlog_le
    linarith

/--
If every type has positive count, the logarithmic scaled counts are pairwise
bounded by any constant dominating the finite log-likelihood offsets.
-/
theorem bernoulli_optimum_log_scaled_count_pairwise_abs_le_of_positive_counts
    {T : ℕ} (B : BernoulliSatisfactionModel T) (N : ℕ)
    {a : CountAllocation T} {C : ℝ}
    (hopt : B.toConsumptionModel.IsOptimalAtTotal N a)
    (hprob_pos : ∀ t, 0 < B.successProb t)
    (hprob_lt_one : ∀ t, B.successProb t < 1)
    (hlike_pos : ∀ t, 0 < B.likelihood t)
    (hcount_pos : ∀ t, 0 < a.count t)
    (hC :
      ∀ i j,
        Real.log (B.likelihood i * B.successProb i) -
          Real.log (B.likelihood j * B.successProb j) +
          theorem3LogScale B i ≤ C) :
    ∀ i j,
      |(a.count i : ℝ) * theorem3LogScale B i -
        (a.count j : ℝ) * theorem3LogScale B j| ≤ C := by
  intro i j
  have hij :=
    bernoulli_optimum_log_scaled_count_pairwise_upper
      B N hopt hprob_pos hprob_lt_one hlike_pos i j (hcount_pos i)
  have hji :=
    bernoulli_optimum_log_scaled_count_pairwise_upper
      B N hopt hprob_pos hprob_lt_one hlike_pos j i (hcount_pos j)
  rw [abs_le]
  constructor
  · have hjiC := hC j i
    linarith
  · exact le_trans hij (hC i j)

/--
Positive-count optimizers convert the Bernoulli FOC into the pairwise scaled
certificate for Theorem 3.
-/
noncomputable def varying_bernoulli_pairwise_scaled_certificate_of_positive_counts
    {T : ℕ} [NeZero T] (B : BernoulliSatisfactionModel T)
    (hcert : VaryingBernoulliPositiveCountCertificate B) :
    VaryingBernoulliPairwiseScaledCertificate B where
  successProb_pos := hcert.successProb_pos
  successProb_lt_one := hcert.successProb_lt_one
  likelihood_pos := hcert.likelihood_pos
  scaled_bound := theorem3LogOffsetBound B
  scaled_bound_pos :=
    theorem3LogOffsetBound_pos B hcert.successProb_pos hcert.successProb_lt_one
  pairwise_scaled := by
    intro N a hN hopt i j
    have hmul :=
      bernoulli_optimum_log_scaled_count_pairwise_abs_le_of_positive_counts
        B N hopt hcert.successProb_pos hcert.successProb_lt_one
        hcert.likelihood_pos
        (hcert.positive_counts N a hN hopt)
        (by
          intro i j
          simpa [theorem3LogOffset] using
            theorem3LogOffset_le_bound (B := B) i j) i j
    simpa [
      count_div_theorem3LogShareWeight_eq_count_mul_logScale
        B hcert.successProb_pos hcert.successProb_lt_one a i,
      count_div_theorem3LogShareWeight_eq_count_mul_logScale
        B hcert.successProb_pos hcert.successProb_lt_one a j
    ] using hmul

/--
Theorem 3 source target from the positive-count FOC seam.

This packages the closed algebraic part: interior optimal allocations imply
the paper's log-share asymptotic target.  Proving the paper's remaining
eventual-interior/small-`N` step can later weaken the certificate.
-/
theorem varying_bernoulli_log_share_asymptotic_of_positive_count_certificate
    {T : ℕ} [NeZero T] (B : BernoulliSatisfactionModel T)
    (hcert : VaryingBernoulliPositiveCountCertificate B) :
    ConsumptionModel.AsymptoticHomogeneity
      (fun _ => B.toConsumptionModel) (theorem3LogShareProfile B) :=
  varying_bernoulli_log_share_asymptotic_of_certificate B
    (varying_bernoulli_log_share_certificate_of_pairwise_scaled B
      (varying_bernoulli_pairwise_scaled_certificate_of_positive_counts B hcert))

/--
Eventual positive-count optimizers convert the Bernoulli FOC into the pairwise
scaled certificate, with a generic finite-prefix bound for `N` below the
interior threshold.
-/
noncomputable def varying_bernoulli_pairwise_scaled_certificate_of_eventual_positive_counts
    {T : ℕ} [NeZero T] (B : BernoulliSatisfactionModel T)
    (hcert : VaryingBernoulliEventualPositiveCountCertificate B) :
    VaryingBernoulliPairwiseScaledCertificate B where
  successProb_pos := hcert.successProb_pos
  successProb_lt_one := hcert.successProb_lt_one
  likelihood_pos := hcert.likelihood_pos
  scaled_bound :=
    theorem3LogOffsetBound B +
      theorem3SmallNScaledBound B hcert.interior_threshold
  scaled_bound_pos :=
    add_pos_of_pos_of_nonneg
      (theorem3LogOffsetBound_pos B
        hcert.successProb_pos hcert.successProb_lt_one)
      (theorem3SmallNScaledBound_nonneg B hcert.interior_threshold
        hcert.successProb_pos hcert.successProb_lt_one)
  pairwise_scaled := by
    intro N a hN hopt i j
    by_cases hlarge : hcert.interior_threshold ≤ N
    · have hmul :=
        bernoulli_optimum_log_scaled_count_pairwise_abs_le_of_positive_counts
          B N hopt hcert.successProb_pos hcert.successProb_lt_one
          hcert.likelihood_pos
          (hcert.positive_counts_eventually N a hN hlarge hopt)
          (by
            intro i j
            simpa [theorem3LogOffset] using
              theorem3LogOffset_le_bound (B := B) i j) i j
      have hscaled :
          |(a.count i : ℝ) / theorem3LogShareWeight B i -
            (a.count j : ℝ) / theorem3LogShareWeight B j| ≤
            theorem3LogOffsetBound B := by
        simpa [
          count_div_theorem3LogShareWeight_eq_count_mul_logScale
            B hcert.successProb_pos hcert.successProb_lt_one a i,
          count_div_theorem3LogShareWeight_eq_count_mul_logScale
            B hcert.successProb_pos hcert.successProb_lt_one a j
        ] using hmul
      have hsmall_nonneg :=
        theorem3SmallNScaledBound_nonneg B hcert.interior_threshold
          hcert.successProb_pos hcert.successProb_lt_one
      exact le_trans hscaled (by linarith)
    · have hNlt : N < hcert.interior_threshold := Nat.lt_of_not_ge hlarge
      have hsmall :=
        theorem3_scaled_count_pairwise_abs_le_of_total_lt
          B hcert.successProb_pos hcert.successProb_lt_one a hopt.1 hNlt i j
      have hoff_nonneg : 0 ≤ theorem3LogOffsetBound B :=
        le_of_lt (theorem3LogOffsetBound_pos B
          hcert.successProb_pos hcert.successProb_lt_one)
      exact le_trans hsmall (by linarith)

/--
Theorem 3 source target from eventual positive counts and finite-prefix
handling.
-/
theorem varying_bernoulli_log_share_asymptotic_of_eventual_positive_count_certificate
    {T : ℕ} [NeZero T] (B : BernoulliSatisfactionModel T)
    (hcert : VaryingBernoulliEventualPositiveCountCertificate B) :
    ConsumptionModel.AsymptoticHomogeneity
      (fun _ => B.toConsumptionModel) (theorem3LogShareProfile B) :=
  varying_bernoulli_log_share_asymptotic_of_certificate B
    (varying_bernoulli_log_share_certificate_of_pairwise_scaled B
      (varying_bernoulli_pairwise_scaled_certificate_of_eventual_positive_counts B hcert))

/--
Theorem 3 source target from pairwise large-count marginal dominance.

This leaves only the analytic Bernoulli-tail threshold proof to derive the
large-count dominance certificate from primitive success-probability
assumptions.
-/
theorem varying_bernoulli_log_share_asymptotic_of_large_count_dominance_certificate
    {T : ℕ} [NeZero T] (B : BernoulliSatisfactionModel T)
    (hcert : VaryingBernoulliLargeCountDominanceCertificate B) :
    ConsumptionModel.AsymptoticHomogeneity
      (fun _ => B.toConsumptionModel) (theorem3LogShareProfile B) :=
  varying_bernoulli_log_share_asymptotic_of_eventual_positive_count_certificate B
    (varying_bernoulli_eventual_positive_count_certificate_of_large_count_dominance
      B hcert)

/--
Theorem 3 source target from the paper's primitive positive Bernoulli
parameters.
-/
theorem varying_bernoulli_log_share_asymptotic_of_primitive
    {T : ℕ} [NeZero T] (B : BernoulliSatisfactionModel T)
    (hprob_pos : ∀ t, 0 < B.successProb t)
    (hprob_lt_one : ∀ t, B.successProb t < 1)
    (hlike_pos : ∀ t, 0 < B.likelihood t) :
    ConsumptionModel.AsymptoticHomogeneity
      (fun _ => B.toConsumptionModel) (theorem3LogShareProfile B) :=
  varying_bernoulli_log_share_asymptotic_of_large_count_dominance_certificate B
    (varying_bernoulli_large_count_dominance_certificate_of_primitive
      B hprob_pos hprob_lt_one hlike_pos)

/--
When all Bernoulli success probabilities are equal, Theorem 3's log-share
target is the uniform `0`-homogeneity profile.
-/
theorem theorem3LogShareProfile_targetShare_eq_uniform
    {T : ℕ} [NeZero T] (B : BernoulliSatisfactionModel T)
    (hprob_pos : ∀ t, 0 < B.successProb t)
    (hprob_lt_one : ∀ t, B.successProb t < 1)
    (hprob_eq : ∀ i j : ItemType T, B.successProb i = B.successProb j)
    (t : ItemType T) :
    (theorem3LogShareProfile B).targetShare t =
      (uniformProfile T).targetShare t := by
  have hweight_pos := theorem3LogShareWeight_pos B hprob_pos hprob_lt_one t
  have hweight_ne : theorem3LogShareWeight B t ≠ 0 := ne_of_gt hweight_pos
  have hTne : (T : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne T)
  have hweight_eq : ∀ i, theorem3LogShareWeight B i = theorem3LogShareWeight B t := by
    intro i
    unfold theorem3LogShareWeight
    rw [hprob_eq i t]
  have hsum :
      (∑ i : ItemType T, theorem3LogShareWeight B i) =
        (T : ℝ) * theorem3LogShareWeight B t := by
    calc
      (∑ i : ItemType T, theorem3LogShareWeight B i)
          = ∑ _i : ItemType T, theorem3LogShareWeight B t :=
            Finset.sum_congr rfl (fun i _ => hweight_eq i)
      _ = (T : ℝ) * theorem3LogShareWeight B t := by
            simp [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul]
  rw [theorem3LogShareProfile_targetShare_eq B hprob_pos hprob_lt_one t]
  rw [uniformProfile_targetShare]
  rw [hsum]
  field_simp [hTne, hweight_ne]

/--
Source Corollary 3: i.i.d. Bernoulli conditional values with common success
probability are asymptotically `0`-homogeneous even when type likelihoods vary.
-/
theorem iid_bernoulli_asymptotic_uniform_homogeneity
    {T : ℕ} [NeZero T] (B : BernoulliSatisfactionModel T)
    (hprob_pos : ∀ t, 0 < B.successProb t)
    (hprob_lt_one : ∀ t, B.successProb t < 1)
    (hlike_pos : ∀ t, 0 < B.likelihood t)
    (hprob_eq : ∀ i j : ItemType T, B.successProb i = B.successProb j) :
    ConsumptionModel.AsymptoticHomogeneity
      (fun _ => B.toConsumptionModel) (uniformProfile T) := by
  obtain ⟨ε, hε, happrox⟩ :=
    varying_bernoulli_log_share_asymptotic_of_primitive
      B hprob_pos hprob_lt_one hlike_pos
  refine ⟨ε, hε, ?_⟩
  intro N a hN hopt t
  have ht := happrox N a hN hopt t
  simpa [GammaHomogeneityProfile.Approx, CountAllocation.HasApproxRepresentation,
    theorem3LogShareProfile_targetShare_eq_uniform B hprob_pos hprob_lt_one
      hprob_eq t] using ht

/-- A consumption model combining a Bernoulli type and a Uniform type. -/
noncomputable def mixedConsumptionModel
    (B : BernoulliSatisfactionModel 1)
    (Ulike : ItemType 1 → ℝ) : ConsumptionModel 2 where
  likelihood t := if t = 0 then B.likelihood 0 else Ulike 0
  valueOfCount t q := if t = 0 then bernoulliAtLeastOneValue (B.successProb 0) q
                      else uniformTopOneValue q

/-- FOC for the mixed model: Uniform marginal vs Bernoulli marginal. -/
theorem mixed_foc_one_zero (B : BernoulliSatisfactionModel 1) (Ulike : ItemType 1 → ℝ)
    (N : ℕ) {a : CountAllocation 2}
    (hopt : (mixedConsumptionModel B Ulike).IsOptimalAtTotal N a)
    (ha0 : 0 < a.count 0) :
    (Ulike 0) * (1 / ((a.count 1 + 1 : ℝ) * (a.count 1 + 2 : ℝ))) ≤
    (B.likelihood 0) * (B.successProb 0) * (1 - B.successProb 0) ^ (a.count 0 - 1) := by
  have hne : (0 : ItemType 2) ≠ 1 := by norm_num
  have hcan : AppliedModelingLib.Allocation.CanMoveOne a 0 := ha0
  have h := ConsumptionModel.weightedForwardMarginal_le_weightedBackwardMarginal_of_optimum
    (mixedConsumptionModel B Ulike) N hopt hne hcan
  unfold mixedConsumptionModel at h
  unfold ConsumptionModel.weightedForwardMarginal ConsumptionModel.weightedBackwardMarginal at h
  unfold ConsumptionModel.marginalValue at h
  unfold AppliedModelingLib.Allocation.marginal at h
  dsimp only at h
  have ha0ne0 : a.count 0 ≠ 0 := ne_of_gt ha0
  rw [dif_neg ha0ne0] at h
  have h_lhs : (if (1 : ItemType 2) = 0 then B.likelihood 0 else Ulike 0) = Ulike 0 :=
    if_neg (by norm_num : (1 : ItemType 2) ≠ 0)
  have h_rhs : (if (0 : ItemType 2) = 0 then B.likelihood 0 else Ulike 0) = B.likelihood 0 :=
    if_pos rfl
  have h_lhs_val1 : (if (1 : ItemType 2) = 0 then bernoulliAtLeastOneValue (B.successProb 0) (a.count 1 + 1) else uniformTopOneValue (a.count 1 + 1)) = uniformTopOneValue (a.count 1 + 1) :=
  by
    exact if_neg (by norm_num)
  have h_lhs_val2 : (if (1 : ItemType 2) = 0 then bernoulliAtLeastOneValue (B.successProb 0) (a.count 1) else uniformTopOneValue (a.count 1)) = uniformTopOneValue (a.count 1) :=
  by
    exact if_neg (by norm_num)
  have h_rhs_val1 : (if (0 : ItemType 2) = 0 then bernoulliAtLeastOneValue (B.successProb 0) (a.count 0) else uniformTopOneValue (a.count 0)) = bernoulliAtLeastOneValue (B.successProb 0) (a.count 0) :=
  by
    exact if_pos rfl
  have h_rhs_val2 : (if (0 : ItemType 2) = 0 then bernoulliAtLeastOneValue (B.successProb 0) (a.count 0 - 1) else uniformTopOneValue (a.count 0 - 1)) = bernoulliAtLeastOneValue (B.successProb 0) (a.count 0 - 1) :=
  by
    exact if_pos rfl
  rw [h_lhs, h_rhs, h_lhs_val1, h_lhs_val2, h_rhs_val1, h_rhs_val2] at h
  rw [uniformTopOneValue_succ_sub] at h
  rw [bernoulliAtLeastOneValue_sub_pred ha0] at h
  have h_assoc : B.likelihood 0 * (B.successProb 0 * (1 - B.successProb 0) ^ (a.count 0 - 1)) = B.likelihood 0 * B.successProb 0 * (1 - B.successProb 0) ^ (a.count 0 - 1) :=
  by ring
  rw [h_assoc] at h
  exact h

/--
The target profile for a mixed Bernoulli-Uniform model.
Bernoulli types (0) get 0 share, Uniform types (1) get all share.
-/
noncomputable def mixedTargetProfile (Ulike : ℝ) : GammaHomogeneityProfile 2 where
  gamma := 1 / 2
  targetWeight t := if t = 0 then 0 else Real.sqrt Ulike

/--
Certificate for the auxiliary mixed Bernoulli-uniform asymptotic interface.

When types have different tail behaviors, the paper strategy says the
faster-decaying Bernoulli type should get negligible share while the uniform
type follows the square-root rule. The exact sequence proof is not source
Theorem 3 and remains a named certificate here.
-/
structure MixedBernoulliUniformHomogeneityCertificate
    (B : BernoulliSatisfactionModel 1) (Ulike : ItemType 1 → ℝ) : Prop where
  bernoulli_success_pos : 0 < B.successProb 0
  bernoulli_success_lt_one : B.successProb 0 < 1
  bernoulli_likelihood_pos : 0 < B.likelihood 0
  uniform_likelihood_pos : 0 < Ulike 0
  asymptotic_mixed :
    ConsumptionModel.AsymptoticHomogeneityTarget
      (fun _ => mixedConsumptionModel B Ulike) (mixedTargetProfile (Ulike 0))
      AppliedModelingLib.Math.ExactInvSqrtRate

/--
Auxiliary mixed Bernoulli-uniform homogeneity bridge from an explicit
certificate.
-/
theorem mixed_bernoulli_uniform_asymptotic_homogeneity
    (B : BernoulliSatisfactionModel 1) (Ulike : ItemType 1 → ℝ)
    (hcert : MixedBernoulliUniformHomogeneityCertificate B Ulike) :
    ConsumptionModel.AsymptoticHomogeneityTarget
      (fun _ => mixedConsumptionModel B Ulike) (mixedTargetProfile (Ulike 0))
      AppliedModelingLib.Math.ExactInvSqrtRate := hcert.asymptotic_mixed

end PRPKG24AccuracyDiversity
