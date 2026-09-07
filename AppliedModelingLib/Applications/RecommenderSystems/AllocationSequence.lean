import AppliedModelingLib.Applications.RecommenderSystems.Allocation
import AppliedModelingLib.Foundations.Math.Asymptotics
import AppliedModelingLib.Foundations.Math.PowerComparisons
import Mathlib.Analysis.Convex.StdSimplex

open Filter Topology
open scoped BigOperators

namespace AppliedModelingLib
namespace Allocation

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Uniform approximate agreement between allocation shares and a target profile. -/
def HasApproxShare (a : Allocation κ) (target : κ → ℝ) (ε : ℝ) : Prop :=
  ∀ k, |share a k - target k| ≤ ε

/-- A sequence of allocations feasible for total size `N` at index `N`. -/
structure Sequence (κ : Type*) [Fintype κ] where
  allocation : ℕ → Allocation κ
  feasible : ∀ N, HasTotal (allocation N) N

namespace Sequence

variable {target : κ → ℝ}

/-- The share of coordinate `k` in the `N`th allocation. -/
noncomputable def share (seq : Sequence κ) (N : ℕ) (k : κ) : ℝ :=
  Allocation.share (seq.allocation N) k

/-- A finite-allocation sequence converges coordinatewise to a target share profile. -/
def ConvergesToProfile (seq : Sequence κ) (target : κ → ℝ) : Prop :=
  ∀ k, Tendsto (fun N => seq.share N k) atTop (nhds (target k))

/--
An eventual uniform approximation rate tending to zero implies coordinatewise
share convergence to the target profile.
-/
theorem convergesToProfile_of_eventual_approx
    (seq : Sequence κ) (target : κ → ℝ) (ε : ℕ → ℝ)
    (hε : Math.TendsToZero ε)
    (happrox : ∀ᶠ N in atTop, HasApproxShare (seq.allocation N) target (ε N)) :
    seq.ConvergesToProfile target := by
  intro k
  have hd :
      Tendsto
        (fun N => Allocation.share (seq.allocation N) k - target k)
        atTop (nhds 0) := by
    have hneg : Tendsto (fun N => -ε N) atTop (nhds 0) := by
      have h := hε.neg
      simpa using h
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hneg hε
    · filter_upwards [happrox] with N hN
      exact (abs_le.mp (hN k)).1
    · filter_upwards [happrox] with N hN
      exact (abs_le.mp (hN k)).2
  have hconst :
      Tendsto (fun _ : ℕ => target k) atTop (nhds (target k)) :=
    tendsto_const_nhds
  have hsum :
      Tendsto
        (fun N => target k + (Allocation.share (seq.allocation N) k - target k))
        atTop (nhds (target k)) := by
    simpa using hconst.add hd
  simpa [share, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hsum

end Sequence

/--
A strict unique maximizer on the finite standard simplex has a uniform
objective gap outside every coordinatewise `ε`-neighborhood of the maximizer.

This is the reusable compactness step behind many finite-type asymptotic
optimizer proofs: once the limiting relaxed objective has a strict unique
simplex maximizer, it is separated by a positive margin from all profiles that
remain a fixed distance away from the maximizer.
-/
theorem exists_gap_on_stdSimplex_of_strict_unique_max
    (objective : (κ → ℝ) → ℝ) (target : κ → ℝ)
    (htarget : target ∈ stdSimplex ℝ κ)
    (hcont : ContinuousOn objective (stdSimplex ℝ κ))
    (hstrict :
      ∀ x : κ → ℝ, x ∈ stdSimplex ℝ κ → x ≠ target →
        objective x < objective target) :
    ∀ ε : ℝ, 0 < ε →
      ∃ η : ℝ, 0 < η ∧
        ∀ x : κ → ℝ, x ∈ stdSimplex ℝ κ →
          (∃ k : κ, ε < |x k - target k|) →
            objective x ≤ objective target - η := by
  classical
  intro ε hε_pos
  let bad : Set (κ → ℝ) :=
    stdSimplex ℝ κ ∩ {x : κ → ℝ | ∃ k : κ, ε ≤ |x k - target k|}
  have hclosed_coord :
      ∀ k : κ, IsClosed {x : κ → ℝ | ε ≤ |x k - target k|} := by
    intro k
    exact isClosed_le continuous_const
      ((continuous_apply k).sub continuous_const).abs
  have hclosed_far :
      IsClosed {x : κ → ℝ | ∃ k : κ, ε ≤ |x k - target k|} := by
    simpa [Set.setOf_exists] using
      (isClosed_iUnion_of_finite (fun k : κ => hclosed_coord k))
  have hcompact_bad : IsCompact bad :=
    (isCompact_stdSimplex ℝ κ).inter_right hclosed_far
  by_cases hbad_empty : bad = ∅
  · refine ⟨1, by norm_num, ?_⟩
    intro x hx_simplex hfar
    have hx_bad : x ∈ bad := by
      rcases hfar with ⟨k, hk⟩
      exact ⟨hx_simplex, ⟨k, le_of_lt hk⟩⟩
    rw [hbad_empty] at hx_bad
    exact hx_bad.elim
  · have hbad_nonempty : bad.Nonempty := Set.nonempty_iff_ne_empty.mpr hbad_empty
    have hcont_bad : ContinuousOn objective bad :=
      hcont.mono (by intro x hx; exact hx.1)
    rcases hcompact_bad.exists_isMaxOn hbad_nonempty hcont_bad with
      ⟨x₀, hx₀_bad, hx₀_max⟩
    have hx₀_ne : x₀ ≠ target := by
      intro hx_eq
      rcases hx₀_bad.2 with ⟨k, hk⟩
      subst x₀
      simp at hk
      linarith
    have hstrict₀ : objective x₀ < objective target :=
      hstrict x₀ hx₀_bad.1 hx₀_ne
    let η : ℝ := objective target - objective x₀
    have hη_pos : 0 < η := by
      dsimp [η]
      linarith
    refine ⟨η, hη_pos, ?_⟩
    intro x hx_simplex hfar
    have hx_bad : x ∈ bad := by
      rcases hfar with ⟨k, hk⟩
      exact ⟨hx_simplex, ⟨k, le_of_lt hk⟩⟩
    have hx_le := hx₀_max hx_bad
    have hx_le' : objective x ≤ objective x₀ := by
      simpa using hx_le
    dsimp [η]
    linarith

/--
An asymptotic target for fixed-total optimal allocations: every positive-size
optimum has shares within `ε N` of `target`, for some error schedule accepted
by `Rate`.
-/
def AsymptoticProfileTarget
    (objectiveWeightSeq : ℕ → κ → ℝ)
    (valueOfCountSeq : ℕ → κ → ℕ → ℝ)
    (target : κ → ℝ) (Rate : (ℕ → ℝ) → Prop) : Prop :=
  ∃ ε : ℕ → ℝ,
    Rate ε ∧
      ∀ N (a : Allocation κ), 0 < N →
        IsOptimalAtTotal (objectiveWeightSeq N) (valueOfCountSeq N) N a →
          HasApproxShare a target (ε N)

/-- The default asymptotic profile target uses filter-based zero convergence. -/
def AsymptoticProfile
    (objectiveWeightSeq : ℕ → κ → ℝ)
    (valueOfCountSeq : ℕ → κ → ℕ → ℝ)
    (target : κ → ℝ) : Prop :=
  AsymptoticProfileTarget objectiveWeightSeq valueOfCountSeq target Math.TendsToZero

namespace AsymptoticProfileTarget

theorem mono_rate
    {objectiveWeightSeq : ℕ → κ → ℝ}
    {valueOfCountSeq : ℕ → κ → ℕ → ℝ}
    {target : κ → ℝ} {Rate₁ Rate₂ : (ℕ → ℝ) → Prop}
    (hRate : ∀ ε, Rate₁ ε → Rate₂ ε) :
    AsymptoticProfileTarget objectiveWeightSeq valueOfCountSeq target Rate₁ →
      AsymptoticProfileTarget objectiveWeightSeq valueOfCountSeq target Rate₂ := by
  intro ⟨ε, hε, happrox⟩
  exact ⟨ε, hRate ε hε, happrox⟩

theorem of_exactInvRate
    {objectiveWeightSeq : ℕ → κ → ℝ}
    {valueOfCountSeq : ℕ → κ → ℕ → ℝ}
    {target : κ → ℝ} :
    AsymptoticProfileTarget objectiveWeightSeq valueOfCountSeq target
        Math.ExactInvRate →
      AsymptoticProfile objectiveWeightSeq valueOfCountSeq target :=
  mono_rate (fun ε hε => Math.ExactInvRate_implies_TendsToZero ε hε)

theorem of_exactInvSqrtRate
    {objectiveWeightSeq : ℕ → κ → ℝ}
    {valueOfCountSeq : ℕ → κ → ℕ → ℝ}
    {target : κ → ℝ} :
    AsymptoticProfileTarget objectiveWeightSeq valueOfCountSeq target
        Math.ExactInvSqrtRate →
      AsymptoticProfile objectiveWeightSeq valueOfCountSeq target :=
  mono_rate (fun ε hε => Math.ExactInvSqrtRate_implies_TendsToZero ε hε)

end AsymptoticProfileTarget

/-- A sequence selecting an optimum of the `N`th fixed-total allocation problem. -/
structure OptimalSequence
    (objectiveWeightSeq : ℕ → κ → ℝ)
    (valueOfCountSeq : ℕ → κ → ℕ → ℝ) where
  allocation : ℕ → Allocation κ
  optimal : ∀ N,
    IsOptimalAtTotal (objectiveWeightSeq N) (valueOfCountSeq N) N (allocation N)

namespace OptimalSequence

/-- Forget optimality and keep only feasibility. -/
def toSequence
    {objectiveWeightSeq : ℕ → κ → ℝ}
    {valueOfCountSeq : ℕ → κ → ℕ → ℝ}
    (seq : OptimalSequence objectiveWeightSeq valueOfCountSeq) :
    Sequence κ where
  allocation := seq.allocation
  feasible := fun N => (seq.optimal N).1

@[simp] theorem toSequence_allocation
    {objectiveWeightSeq : ℕ → κ → ℝ}
    {valueOfCountSeq : ℕ → κ → ℕ → ℝ}
    (seq : OptimalSequence objectiveWeightSeq valueOfCountSeq) (N : ℕ) :
    seq.toSequence.allocation N = seq.allocation N := rfl

/--
Once every finite optimum satisfies an asymptotic profile target, every
selected sequence of optima converges to that target profile.
-/
theorem convergesToProfile_of_asymptoticProfileTarget
    {objectiveWeightSeq : ℕ → κ → ℝ}
    {valueOfCountSeq : ℕ → κ → ℕ → ℝ}
    {target : κ → ℝ}
    (seq : OptimalSequence objectiveWeightSeq valueOfCountSeq)
    (h :
      AsymptoticProfileTarget objectiveWeightSeq valueOfCountSeq target
        Math.TendsToZero) :
    seq.toSequence.ConvergesToProfile target := by
  rcases h with ⟨ε, hε, happrox⟩
  apply Sequence.convergesToProfile_of_eventual_approx
    seq.toSequence target ε hε
  filter_upwards [eventually_gt_atTop 0] with N hN
  exact happrox N (seq.allocation N) hN (seq.optimal N)

theorem convergesToProfile_of_asymptoticProfile
    {objectiveWeightSeq : ℕ → κ → ℝ}
    {valueOfCountSeq : ℕ → κ → ℕ → ℝ}
    {target : κ → ℝ}
    (seq : OptimalSequence objectiveWeightSeq valueOfCountSeq)
    (h : AsymptoticProfile objectiveWeightSeq valueOfCountSeq target) :
    seq.toSequence.ConvergesToProfile target :=
  seq.convergesToProfile_of_asymptoticProfileTarget h

/--
Optimizer convergence from a unique limiting objective gap.

This is the compactness-free form of a common separable-allocation argument.
If the finite objective of every selected optimum is eventually bounded above
by a continuous relaxed objective, a feasible comparison sequence eventually
achieves the relaxed target value from below, and every allocation share profile
outside an `ε`-ball around `target` has a strict relaxed-objective gap, then the
selected finite optima converge to `target`.

The finite comparison objective is deliberately explicit: it can be a
normalized or shifted form of the model objective, as long as the selected
optima also maximize that comparison objective.
-/
theorem convergesToProfile_of_unique_limit_objective_gap
    {objectiveWeightSeq : ℕ → κ → ℝ}
    {valueOfCountSeq : ℕ → κ → ℕ → ℝ}
    {target : κ → ℝ}
    (seq : OptimalSequence objectiveWeightSeq valueOfCountSeq)
    (finiteObj : ℕ → Allocation κ → ℝ)
    (limitObj : (κ → ℝ) → ℝ)
    (candidate : ℕ → Allocation κ)
    (hopt_le :
      ∀ᶠ N in atTop, ∀ b : Allocation κ, HasTotal b N →
        finiteObj N b ≤ finiteObj N (seq.allocation N))
    (hcand_feas :
      ∀ᶠ N in atTop, HasTotal (candidate N) N)
    (hcand_lower :
      ∀ δ : ℝ, 0 < δ →
        ∀ᶠ N in atTop,
          limitObj target - δ ≤ finiteObj N (candidate N))
    (hupper :
      ∀ δ : ℝ, 0 < δ →
        ∀ᶠ N in atTop, ∀ a : Allocation κ, HasTotal a N →
          finiteObj N a ≤ limitObj (fun k => share a k) + δ)
    (hgap :
      ∀ ε : ℝ, 0 < ε →
        ∃ η : ℝ, 0 < η ∧
          ∀ N (a : Allocation κ), 0 < N → HasTotal a N →
            ¬ HasApproxShare a target ε →
              limitObj (fun k => share a k) ≤ limitObj target - η) :
    seq.toSequence.ConvergesToProfile target := by
  have heventual_approx :
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ N in atTop, HasApproxShare (seq.allocation N) target ε := by
    intro ε hε
    rcases hgap ε hε with ⟨η, hη_pos, hη_gap⟩
    let δ : ℝ := η / 3
    have hδ_pos : 0 < δ := by dsimp [δ]; linarith
    filter_upwards
      [eventually_gt_atTop 0, hopt_le, hcand_feas, hcand_lower δ hδ_pos,
        hupper δ hδ_pos]
      with N hNpos hopt_cmp hcandN hcand_lowerN hupperN
    by_contra hnot
    have hseq_upper :
        finiteObj N (seq.allocation N) ≤ limitObj target - η + δ := by
      have hgapN :=
        hη_gap N (seq.allocation N) hNpos (seq.optimal N).1 hnot
      have hupper_seq :=
        hupperN (seq.allocation N) (seq.optimal N).1
      linarith
    have hcand_le_seq :
        finiteObj N (candidate N) ≤ finiteObj N (seq.allocation N) :=
      hopt_cmp (candidate N) hcandN
    have htarget_lower :
        limitObj target - δ ≤ limitObj target - η + δ :=
      le_trans hcand_lowerN (le_trans hcand_le_seq hseq_upper)
    have hη_le_twoδ : η ≤ 2 * δ := by linarith
    have htwoδ_lt_η : 2 * δ < η := by
      dsimp [δ]
      linarith
    exact (not_lt_of_ge hη_le_twoδ) htwoδ_lt_η
  intro k
  rw [Metric.tendsto_nhds]
  intro ε hε
  let ε' : ℝ := ε / 2
  have hε'_pos : 0 < ε' := by dsimp [ε']; linarith
  filter_upwards [heventual_approx ε' hε'_pos] with N hN
  have hle := hN k
  have hlt : |share (seq.allocation N) k - target k| < ε := by
    dsimp [ε'] at hle
    linarith
  simpa [Sequence.share, Real.dist_eq] using hlt

end OptimalSequence

/--
If all positive-size finite optima have pairwise scaled-count gaps bounded by a
fixed constant, then their shares converge to the profile proportional to
`profileWeight` with an exact `C / N` rate.
-/
theorem asymptoticProfileTarget_of_pairwise_scaled_bounded
    [Nonempty κ]
    {objectiveWeightSeq : ℕ → κ → ℝ}
    {valueOfCountSeq : ℕ → κ → ℕ → ℝ}
    {profileWeight : κ → ℝ} {target : κ → ℝ}
    {bound : ℝ}
    (hweight_pos : ∀ k, 0 < profileWeight k)
    (htarget :
      ∀ k, target k = profileWeight k / ∑ i : κ, profileWeight i)
    (hbound_pos : 0 < bound)
    (hpair :
      ∀ N (a : Allocation κ), 0 < N →
        IsOptimalAtTotal (objectiveWeightSeq N) (valueOfCountSeq N) N a →
          ∀ i j,
            |(a.count i : ℝ) / profileWeight i -
              (a.count j : ℝ) / profileWeight j| ≤ bound) :
    AsymptoticProfileTarget objectiveWeightSeq valueOfCountSeq target
      Math.ExactInvRate := by
  refine
    ⟨fun N => bound * (∑ i : κ, profileWeight i) / (N : ℝ), ?_, ?_⟩
  · refine
      ⟨bound * ∑ i : κ, profileWeight i,
        mul_pos hbound_pos
          (Finset.sum_pos (fun i _ => hweight_pos i) Finset.univ_nonempty),
        fun N => rfl⟩
  · intro N a hN hopt k
    have hshare :=
      share_abs_sub_weighted_target_le_total_weight_of_pairwise_scaled_bounded
        (a := a) (weight := profileWeight) (N := N) (C := bound)
        hopt.1 hN hweight_pos (le_of_lt hbound_pos)
        (hpair N a hN hopt) k
    simpa [HasApproxShare, htarget k] using hshare

/--
Certificate form of the bounded pairwise scaled-count profile bridge.

This is the fixed-error counterpart to
`PairwiseScaledSublinearProfileCertificate`: a uniform `O(1)` bound on scaled
count gaps gives an exact `C / N` profile error rate.
-/
structure PairwiseScaledBoundedProfileCertificate
    (objectiveWeightSeq : ℕ → κ → ℝ)
    (valueOfCountSeq : ℕ → κ → ℕ → ℝ)
    (profileWeight : κ → ℝ) (target : κ → ℝ) where
  weight_pos : ∀ k, 0 < profileWeight k
  target_eq :
    ∀ k, target k = profileWeight k / ∑ i : κ, profileWeight i
  bound : ℝ
  bound_pos : 0 < bound
  pairwise_scaled :
    ∀ N (a : Allocation κ), 0 < N →
      IsOptimalAtTotal (objectiveWeightSeq N) (valueOfCountSeq N) N a →
        ∀ i j,
          |(a.count i : ℝ) / profileWeight i -
            (a.count j : ℝ) / profileWeight j| ≤ bound

namespace PairwiseScaledBoundedProfileCertificate

theorem asymptoticProfileTarget
    [Nonempty κ]
    {objectiveWeightSeq : ℕ → κ → ℝ}
    {valueOfCountSeq : ℕ → κ → ℕ → ℝ}
    {profileWeight : κ → ℝ} {target : κ → ℝ}
    (hcert :
      PairwiseScaledBoundedProfileCertificate
        objectiveWeightSeq valueOfCountSeq profileWeight target) :
    AsymptoticProfileTarget objectiveWeightSeq valueOfCountSeq target
      Math.ExactInvRate :=
  asymptoticProfileTarget_of_pairwise_scaled_bounded
    hcert.weight_pos hcert.target_eq hcert.bound_pos hcert.pairwise_scaled

theorem asymptoticProfile
    [Nonempty κ]
    {objectiveWeightSeq : ℕ → κ → ℝ}
    {valueOfCountSeq : ℕ → κ → ℕ → ℝ}
    {profileWeight : κ → ℝ} {target : κ → ℝ}
    (hcert :
      PairwiseScaledBoundedProfileCertificate
        objectiveWeightSeq valueOfCountSeq profileWeight target) :
    AsymptoticProfile objectiveWeightSeq valueOfCountSeq target :=
  AsymptoticProfileTarget.of_exactInvRate hcert.asymptoticProfileTarget

end PairwiseScaledBoundedProfileCertificate

/--
If all positive-size finite optima have pairwise scaled-count gaps at most
`error N * N`, with `error -> 0`, then their shares converge to the profile
proportional to `profileWeight`.
-/
theorem asymptoticProfile_of_pairwise_scaled_sublinear
    [Nonempty κ]
    {objectiveWeightSeq : ℕ → κ → ℝ}
    {valueOfCountSeq : ℕ → κ → ℕ → ℝ}
    {profileWeight : κ → ℝ} {target : κ → ℝ}
    {error : ℕ → ℝ}
    (hweight_pos : ∀ k, 0 < profileWeight k)
    (htarget :
      ∀ k, target k = profileWeight k / ∑ i : κ, profileWeight i)
    (herror_nonneg : ∀ N, 0 ≤ error N)
    (herror_tends_to_zero : Math.TendsToZero error)
    (hpair :
      ∀ N (a : Allocation κ), 0 < N →
        IsOptimalAtTotal (objectiveWeightSeq N) (valueOfCountSeq N) N a →
          ∀ i j,
            |(a.count i : ℝ) / profileWeight i -
              (a.count j : ℝ) / profileWeight j| ≤ error N * (N : ℝ)) :
    AsymptoticProfile objectiveWeightSeq valueOfCountSeq target := by
  let W : ℝ := ∑ i : κ, profileWeight i
  refine ⟨fun N => error N * W, ?_, ?_⟩
  · have herr : Tendsto error atTop (nhds 0) := by
      simpa [Math.TendsToZero] using herror_tends_to_zero
    have hW : Tendsto (fun _ : ℕ => W) atTop (nhds W) := tendsto_const_nhds
    have hmul := herr.mul hW
    simpa [Math.TendsToZero, W] using hmul
  · intro N a hN hopt k
    have hshare :=
      share_abs_sub_weighted_target_le_error_total_weight_of_pairwise_scaled
        (a := a) (weight := profileWeight) (N := N) (error := error N)
        hopt.1 hN hweight_pos (herror_nonneg N) (hpair N a hN hopt) k
    simpa [HasApproxShare, htarget k, W] using hshare

/--
FOC-based sublinear scaled-count bridge. A large scaled gap is ruled out by
finite optimality; the resulting sublinear pairwise scaled-count bound implies
the asymptotic target profile.
-/
theorem asymptoticProfile_of_large_gap_backward_lt_forward
    [Nonempty κ]
    {objectiveWeightSeq : ℕ → κ → ℝ}
    {valueOfCountSeq : ℕ → κ → ℕ → ℝ}
    {profileWeight : κ → ℝ} {target : κ → ℝ}
    {error : ℕ → ℝ}
    (hweight_pos : ∀ k, 0 < profileWeight k)
    (htarget :
      ∀ k, target k = profileWeight k / ∑ i : κ, profileWeight i)
    (herror_nonneg : ∀ N, 0 ≤ error N)
    (herror_tends_to_zero : Math.TendsToZero error)
    (hlarge :
      ∀ N (a : Allocation κ), 0 < N →
        IsOptimalAtTotal (objectiveWeightSeq N) (valueOfCountSeq N) N a →
          ∀ src dst,
            error N * (N : ℝ) <
              (a.count src : ℝ) / profileWeight src -
                (a.count dst : ℝ) / profileWeight dst →
            weightedBackwardMarginal (objectiveWeightSeq N) (valueOfCountSeq N)
                src (a.count src) <
              weightedForwardMarginal (objectiveWeightSeq N) (valueOfCountSeq N)
                dst (a.count dst)) :
    AsymptoticProfile objectiveWeightSeq valueOfCountSeq target := by
  refine asymptoticProfile_of_pairwise_scaled_sublinear
    (hweight_pos := hweight_pos) (htarget := htarget)
    (herror_nonneg := herror_nonneg)
    (herror_tends_to_zero := herror_tends_to_zero) ?_
  intro N a hN hopt i j
  have hC_nonneg : 0 ≤ error N * (N : ℝ) :=
    mul_nonneg (herror_nonneg N) (Nat.cast_nonneg N)
  exact pairwise_scaled_abs_le_of_large_gap_backward_lt_forward
    (a := a) (objectiveWeight := objectiveWeightSeq N)
    (scaledWeight := profileWeight) (valueOfCount := valueOfCountSeq N)
    (N := N) (error := error N)
    hweight_pos hC_nonneg hopt (hlarge N a hN hopt) i j

/--
Floor-aware/eventual FOC bridge.

Distribution-specific estimates often prove large-gap marginal dominance only
after every compared coordinate count is above a fixed floor and after `N` is
large. This theorem absorbs the finite prefix by using a large temporary error,
then applies the generic large-gap FOC bridge.
-/
theorem asymptoticProfile_of_eventual_large_gap_backward_lt_forward
    [Nonempty κ]
    {objectiveWeightSeq : ℕ → κ → ℝ}
    {valueOfCountSeq : ℕ → κ → ℕ → ℝ}
    {profileWeight : κ → ℝ} {target : κ → ℝ}
    {baseError : ℕ → ℝ}
    (hweight_pos : ∀ k, 0 < profileWeight k)
    (htarget :
      ∀ k, target k = profileWeight k / ∑ i : κ, profileWeight i)
    (hbaseError_nonneg : ∀ N, 0 ≤ baseError N)
    (hbaseError_tends_to_zero : Math.TendsToZero baseError)
    (floor : ℕ)
    (hcount_floor_eventually :
      ∀ᶠ N in atTop,
        ∀ a : Allocation κ, 0 < N →
          IsOptimalAtTotal (objectiveWeightSeq N) (valueOfCountSeq N) N a →
            ∀ k, floor < a.count k)
    (hlarge_after_floor :
      ∀ᶠ N in atTop,
        ∀ a : Allocation κ, 0 < N →
          IsOptimalAtTotal (objectiveWeightSeq N) (valueOfCountSeq N) N a →
            ∀ src dst,
              floor < a.count src →
              floor < a.count dst →
              baseError N * (N : ℝ) <
                (a.count src : ℝ) / profileWeight src -
                  (a.count dst : ℝ) / profileWeight dst →
              weightedBackwardMarginal (objectiveWeightSeq N) (valueOfCountSeq N)
                  src (a.count src) <
                weightedForwardMarginal (objectiveWeightSeq N) (valueOfCountSeq N)
                  dst (a.count dst)) :
    AsymptoticProfile objectiveWeightSeq valueOfCountSeq target := by
  classical
  let floorThreshold : ℕ :=
    Classical.choose (eventually_atTop.1 hcount_floor_eventually)
  have hfloorThreshold :
      ∀ N ≥ floorThreshold,
        ∀ a : Allocation κ, 0 < N →
          IsOptimalAtTotal (objectiveWeightSeq N) (valueOfCountSeq N) N a →
            ∀ k, floor < a.count k :=
    Classical.choose_spec (eventually_atTop.1 hcount_floor_eventually)
  let asymThreshold : ℕ :=
    Classical.choose (eventually_atTop.1 hlarge_after_floor)
  have hasymThreshold :
      ∀ N ≥ asymThreshold,
        ∀ a : Allocation κ, 0 < N →
          IsOptimalAtTotal (objectiveWeightSeq N) (valueOfCountSeq N) N a →
            ∀ src dst,
              floor < a.count src →
              floor < a.count dst →
              baseError N * (N : ℝ) <
                (a.count src : ℝ) / profileWeight src -
                  (a.count dst : ℝ) / profileWeight dst →
              weightedBackwardMarginal (objectiveWeightSeq N) (valueOfCountSeq N)
                  src (a.count src) <
                weightedForwardMarginal (objectiveWeightSeq N) (valueOfCountSeq N)
                  dst (a.count dst) :=
    Classical.choose_spec (eventually_atTop.1 hlarge_after_floor)
  let threshold : ℕ := max floorThreshold asymThreshold
  let finitePrefixError : ℝ := (∑ k : κ, 1 / profileWeight k) + 1
  refine asymptoticProfile_of_large_gap_backward_lt_forward
    (profileWeight := profileWeight) (target := target)
    (error := fun N => if N < threshold then finitePrefixError else baseError N)
    hweight_pos htarget ?_ ?_ ?_
  · intro N
    by_cases hN : N < threshold
    · have hsum_nonneg :
          0 ≤ ∑ k : κ, 1 / profileWeight k := by
        exact Finset.sum_nonneg
          (fun k _ => div_nonneg zero_le_one (le_of_lt (hweight_pos k)))
      have hfinite_nonneg : 0 ≤ finitePrefixError := by
        dsimp [finitePrefixError]
        linarith
      simpa [hN] using hfinite_nonneg
    · simp [hN, hbaseError_nonneg N]
  · exact Math.tendsToZero_if_lt_const
      hbaseError_tends_to_zero threshold finitePrefixError
  · intro N a hNpos hopt src dst hgap
    by_cases hsmall : N < threshold
    · exfalso
      have hgap_small :
          finitePrefixError * (N : ℝ) <
            (a.count src : ℝ) / profileWeight src -
              (a.count dst : ℝ) / profileWeight dst := by
        simpa [hsmall] using hgap
      have hsrc_count_le_total : a.count src ≤ N := by
        have hle := count_le_total a src
        have htotal_eq : a.total = N := hopt.1
        rw [htotal_eq] at hle
        exact hle
      have hsrc_count_le_total_real :
          (a.count src : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast hsrc_count_le_total
      have hdst_div_nonneg :
          0 ≤ (a.count dst : ℝ) / profileWeight dst :=
        div_nonneg (Nat.cast_nonneg _) (le_of_lt (hweight_pos dst))
      have hdiff_le_src_div :
          (a.count src : ℝ) / profileWeight src -
              (a.count dst : ℝ) / profileWeight dst ≤
            (a.count src : ℝ) / profileWeight src := by
        linarith
      have hsrc_div_le_N_inv :
          (a.count src : ℝ) / profileWeight src ≤
            (N : ℝ) * (1 / profileWeight src) := by
        rw [div_eq_mul_inv, one_div]
        exact mul_le_mul_of_nonneg_right hsrc_count_le_total_real
          (inv_nonneg.mpr (le_of_lt (hweight_pos src)))
      have hinv_le_sum :
          1 / profileWeight src ≤ ∑ k : κ, 1 / profileWeight k := by
        exact Finset.single_le_sum
          (fun k _ => div_nonneg zero_le_one (le_of_lt (hweight_pos k)))
          (Finset.mem_univ src)
      have hN_nonneg : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
      have hN_inv_le_sum :
          (N : ℝ) * (1 / profileWeight src) ≤
            (N : ℝ) * ∑ k : κ, 1 / profileWeight k :=
        mul_le_mul_of_nonneg_left hinv_le_sum hN_nonneg
      have hdiff_le_sum :
          (a.count src : ℝ) / profileWeight src -
              (a.count dst : ℝ) / profileWeight dst ≤
            (N : ℝ) * ∑ k : κ, 1 / profileWeight k :=
        le_trans hdiff_le_src_div
          (le_trans hsrc_div_le_N_inv hN_inv_le_sum)
      have hNpos_real : 0 < (N : ℝ) := by
        exact_mod_cast hNpos
      have hsum_lt_prefix :
          (N : ℝ) * ∑ k : κ, 1 / profileWeight k <
            finitePrefixError * (N : ℝ) := by
        have hsum_lt :
            (∑ k : κ, 1 / profileWeight k) < finitePrefixError := by
          dsimp [finitePrefixError]
          linarith
        calc
          (N : ℝ) * ∑ k : κ, 1 / profileWeight k
              < (N : ℝ) * finitePrefixError :=
                mul_lt_mul_of_pos_left hsum_lt hNpos_real
          _ = finitePrefixError * (N : ℝ) := by ring
      exact not_lt_of_ge
        (le_trans hdiff_le_sum (le_of_lt hsum_lt_prefix)) hgap_small
    · have hthreshold_le_N : threshold ≤ N := le_of_not_gt hsmall
      have hfloorThreshold_le_threshold : floorThreshold ≤ threshold := by
        dsimp [threshold]
        exact le_max_left floorThreshold asymThreshold
      have hasymThreshold_le_threshold : asymThreshold ≤ threshold := by
        dsimp [threshold]
        exact le_max_right floorThreshold asymThreshold
      have hfloorThreshold_le_N : floorThreshold ≤ N :=
        le_trans hfloorThreshold_le_threshold hthreshold_le_N
      have hasymThreshold_le_N : asymThreshold ≤ N :=
        le_trans hasymThreshold_le_threshold hthreshold_le_N
      have hcounts_floor : ∀ k, floor < a.count k :=
        hfloorThreshold N hfloorThreshold_le_N a hNpos hopt
      have hdomN := hasymThreshold N hasymThreshold_le_N
      have hgap_base :
          baseError N * (N : ℝ) <
            (a.count src : ℝ) / profileWeight src -
              (a.count dst : ℝ) / profileWeight dst := by
        simpa [hsmall] using hgap
      exact hdomN a hNpos hopt src dst
        (hcounts_floor src) (hcounts_floor dst) hgap_base

/--
Certificate form of pairwise scaled-count convergence.

This is the reusable shape for papers that first prove all finite optima have
pairwise scaled-count gaps bounded by a sublinear error schedule, then conclude
convergence to the target profile proportional to `profileWeight`.
-/
structure PairwiseScaledSublinearProfileCertificate
    (objectiveWeightSeq : ℕ → κ → ℝ)
    (valueOfCountSeq : ℕ → κ → ℕ → ℝ)
    (profileWeight : κ → ℝ) (target : κ → ℝ) where
  weight_pos : ∀ k, 0 < profileWeight k
  target_eq :
    ∀ k, target k = profileWeight k / ∑ i : κ, profileWeight i
  error : ℕ → ℝ
  error_nonneg : ∀ N, 0 ≤ error N
  error_tends_to_zero : Math.TendsToZero error
  pairwise_scaled :
    ∀ N (a : Allocation κ), 0 < N →
      IsOptimalAtTotal (objectiveWeightSeq N) (valueOfCountSeq N) N a →
        ∀ i j,
          |(a.count i : ℝ) / profileWeight i -
            (a.count j : ℝ) / profileWeight j| ≤ error N * (N : ℝ)

namespace PairwiseScaledSublinearProfileCertificate

theorem asymptoticProfile
    [Nonempty κ]
    {objectiveWeightSeq : ℕ → κ → ℝ}
    {valueOfCountSeq : ℕ → κ → ℕ → ℝ}
    {profileWeight : κ → ℝ} {target : κ → ℝ}
    (hcert :
      PairwiseScaledSublinearProfileCertificate
        objectiveWeightSeq valueOfCountSeq profileWeight target) :
    AsymptoticProfile objectiveWeightSeq valueOfCountSeq target :=
  asymptoticProfile_of_pairwise_scaled_sublinear
    hcert.weight_pos hcert.target_eq hcert.error_nonneg
    hcert.error_tends_to_zero hcert.pairwise_scaled

end PairwiseScaledSublinearProfileCertificate

/--
Finite-envelope power-law large-gap comparison.

For objectives whose weighted backward/forward marginals are trapped by a
common negative-power template, the sublinear gap `1 / sqrt (N+1)` absorbs the
fixed source/destination count shifts and yields the FOC large-gap comparison
used by asymptotic allocation-profile arguments.
-/
theorem powerLawEnvelope_large_gap_count_eventually
    (objectiveWeight : κ → ℝ) (valueOfCount : κ → ℕ → ℝ)
    {η γ coeff dstShift : ℝ} {floor : ℕ}
    (hη_pos : 0 < η)
    (hγ_eq : 1 / η = γ)
    (hcoeff_pos : 0 < coeff)
    (hdstShift_nonneg : 0 ≤ dstShift)
    (hfloor_pos : 0 < floor)
    (hweight_pos : ∀ k : κ, 0 < objectiveWeight k)
    (backward_le :
      ∀ src qsrc,
        floor < qsrc →
        weightedBackwardMarginal objectiveWeight valueOfCount src qsrc ≤
          objectiveWeight src *
            (coeff * (((qsrc - 1 : ℕ) : ℝ) ^ (-η))))
    (forward_ge :
      ∀ dst qdst,
        floor < qdst →
        objectiveWeight dst *
            (coeff * (((qdst : ℝ) + 1 + dstShift) ^ (-η))) ≤
          weightedForwardMarginal objectiveWeight valueOfCount dst qdst) :
    ∀ᶠ N in atTop,
      ∀ src dst qsrc qdst,
        qsrc ≤ N →
        qdst ≤ N →
        floor < qsrc →
        floor < qdst →
        Math.invSqrtSuccError N * (N : ℝ) <
          (qsrc : ℝ) / objectiveWeight src ^ γ -
            (qdst : ℝ) / objectiveWeight dst ^ γ →
        weightedBackwardMarginal objectiveWeight valueOfCount src qsrc <
          weightedForwardMarginal objectiveWeight valueOfCount dst qdst := by
  classical
  have hshift_ev :
      ∀ᶠ N in atTop,
        ∀ src dst : κ,
          1 / objectiveWeight src ^ γ +
              (1 + dstShift) / objectiveWeight dst ^ γ <
            Math.invSqrtSuccError N * (N : ℝ) := by
    simpa using
      Math.invSqrtSuccError_mul_nat_eventually_gt_fintype_pair
        (fun src dst : κ =>
          1 / objectiveWeight src ^ γ +
            (1 + dstShift) / objectiveWeight dst ^ γ)
  filter_upwards [hshift_ev] with N hshift src dst qsrc qdst
    _hqsrc_le _hqdst_le hsrc_floor hdst_floor hgap
  have hshift_lt_gap :
      1 / objectiveWeight src ^ γ +
          (1 + dstShift) / objectiveWeight dst ^ γ <
        (qsrc : ℝ) / objectiveWeight src ^ γ -
          (qdst : ℝ) / objectiveWeight dst ^ γ := by
    exact lt_trans (hshift src dst) hgap
  have hscaled_shift :
      (((qdst : ℝ) + 1 + dstShift) / objectiveWeight dst ^ γ) <
        (((qsrc - 1 : ℕ) : ℝ) / objectiveWeight src ^ γ) := by
    have hsrc_cast : (((qsrc - 1 : ℕ) : ℝ)) = (qsrc : ℝ) - 1 := by
      rw [Nat.cast_sub (R := ℝ) (by omega : 1 ≤ qsrc)]
      norm_num
    rw [hsrc_cast]
    simpa [add_assoc] using
      Math.scaled_gap_absorbs_additive_shifts
        (qsrc := (qsrc : ℝ)) (qdst := (qdst : ℝ))
        (wsrc := objectiveWeight src ^ γ)
        (wdst := objectiveWeight dst ^ γ)
        (srcShift := 1) (dstShift := 1 + dstShift) hshift_lt_gap
  have hscaled_power :
      (((qdst : ℝ) + 1 + dstShift) / objectiveWeight dst ^ (1 / η)) <
        (((qsrc - 1 : ℕ) : ℝ) / objectiveWeight src ^ (1 / η)) := by
    simpa [hγ_eq] using hscaled_shift
  have hx_pos : 0 < (((qsrc - 1 : ℕ) : ℝ)) := by
    exact_mod_cast (by omega : 0 < qsrc - 1)
  have hy_pos : 0 < (qdst : ℝ) + 1 + dstShift := by
    have hqdst_nonneg : 0 ≤ (qdst : ℝ) := Nat.cast_nonneg qdst
    linarith
  have hpower :
      objectiveWeight src *
          (coeff * (((qsrc - 1 : ℕ) : ℝ) ^ (-η))) <
        objectiveWeight dst *
          (coeff * (((qdst : ℝ) + 1 + dstShift) ^ (-η))) :=
    Math.rpow_neg_marginal_lt_of_scaled_lt
      (p_src := objectiveWeight src) (p_dst := objectiveWeight dst)
      (c := coeff) (eta := η)
      (x := ((qsrc - 1 : ℕ) : ℝ))
      (y := (qdst : ℝ) + 1 + dstShift)
      (hweight_pos src) (hweight_pos dst) hcoeff_pos hη_pos
      hx_pos hy_pos hscaled_power
  have hback_le := backward_le src qsrc hsrc_floor
  have hforward_ge := forward_ge dst qdst hdst_floor
  exact lt_of_le_of_lt hback_le (lt_of_lt_of_le hpower hforward_ge)

/--
Certificate form of the FOC-based pairwise scaled-count bridge.

The large-gap dominance field is the paper-facing analytic/probabilistic
obligation. Generic finite optimality turns it into a pairwise scaled-count
bound, and then into an asymptotic profile.
-/
structure PairwiseScaledSublinearFOCCertificate
    (objectiveWeightSeq : ℕ → κ → ℝ)
    (valueOfCountSeq : ℕ → κ → ℕ → ℝ)
    (profileWeight : κ → ℝ) (target : κ → ℝ) where
  weight_pos : ∀ k, 0 < profileWeight k
  target_eq :
    ∀ k, target k = profileWeight k / ∑ i : κ, profileWeight i
  error : ℕ → ℝ
  error_nonneg : ∀ N, 0 ≤ error N
  error_tends_to_zero : Math.TendsToZero error
  large_gap_backward_lt_forward :
    ∀ N (a : Allocation κ), 0 < N →
      IsOptimalAtTotal (objectiveWeightSeq N) (valueOfCountSeq N) N a →
        ∀ src dst,
          error N * (N : ℝ) <
            (a.count src : ℝ) / profileWeight src -
              (a.count dst : ℝ) / profileWeight dst →
          weightedBackwardMarginal (objectiveWeightSeq N) (valueOfCountSeq N)
              src (a.count src) <
            weightedForwardMarginal (objectiveWeightSeq N) (valueOfCountSeq N)
              dst (a.count dst)

namespace PairwiseScaledSublinearFOCCertificate

noncomputable def toPairwiseScaledSublinearProfileCertificate
    {objectiveWeightSeq : ℕ → κ → ℝ}
    {valueOfCountSeq : ℕ → κ → ℕ → ℝ}
    {profileWeight : κ → ℝ} {target : κ → ℝ}
    (hcert :
      PairwiseScaledSublinearFOCCertificate
        objectiveWeightSeq valueOfCountSeq profileWeight target) :
    PairwiseScaledSublinearProfileCertificate
      objectiveWeightSeq valueOfCountSeq profileWeight target where
  weight_pos := hcert.weight_pos
  target_eq := hcert.target_eq
  error := hcert.error
  error_nonneg := hcert.error_nonneg
  error_tends_to_zero := hcert.error_tends_to_zero
  pairwise_scaled := by
    intro N a _hN hopt src dst
    have hC_nonneg : 0 ≤ hcert.error N * (N : ℝ) :=
      mul_nonneg (hcert.error_nonneg N) (Nat.cast_nonneg N)
    exact pairwise_scaled_abs_le_of_large_gap_backward_lt_forward
      (a := a) (objectiveWeight := objectiveWeightSeq N)
      (scaledWeight := profileWeight) (valueOfCount := valueOfCountSeq N)
      (N := N) (error := hcert.error N)
      hcert.weight_pos hC_nonneg hopt
      (hcert.large_gap_backward_lt_forward N a _hN hopt) src dst

theorem asymptoticProfile
    [Nonempty κ]
    {objectiveWeightSeq : ℕ → κ → ℝ}
    {valueOfCountSeq : ℕ → κ → ℕ → ℝ}
    {profileWeight : κ → ℝ} {target : κ → ℝ}
    (hcert :
      PairwiseScaledSublinearFOCCertificate
        objectiveWeightSeq valueOfCountSeq profileWeight target) :
    AsymptoticProfile objectiveWeightSeq valueOfCountSeq target :=
  hcert.toPairwiseScaledSublinearProfileCertificate.asymptoticProfile

end PairwiseScaledSublinearFOCCertificate

/--
Eventual, floor-aware FOC certificate.

Distribution-specific marginal comparisons often become valid only after a
finite prefix and only for coordinates above a count floor. This certificate
packages those eventual obligations and produces the clean sublinear FOC
certificate by assigning a deliberately large temporary error on the finite
prefix.
-/
structure PairwiseScaledEventualSublinearFOCCertificate
    (objectiveWeightSeq : ℕ → κ → ℝ)
    (valueOfCountSeq : ℕ → κ → ℕ → ℝ)
    (profileWeight : κ → ℝ) (target : κ → ℝ) where
  weight_pos : ∀ k, 0 < profileWeight k
  target_eq :
    ∀ k, target k = profileWeight k / ∑ i : κ, profileWeight i
  baseError : ℕ → ℝ
  baseError_nonneg : ∀ N, 0 ≤ baseError N
  baseError_tends_to_zero : Math.TendsToZero baseError
  floor : ℕ
  count_floor_eventually :
    ∀ᶠ N in atTop,
      ∀ a : Allocation κ, 0 < N →
        IsOptimalAtTotal (objectiveWeightSeq N) (valueOfCountSeq N) N a →
          ∀ k, floor < a.count k
  large_gap_backward_lt_forward_after_floor :
    ∀ᶠ N in atTop,
      ∀ a : Allocation κ, 0 < N →
        IsOptimalAtTotal (objectiveWeightSeq N) (valueOfCountSeq N) N a →
          ∀ src dst,
            floor < a.count src →
            floor < a.count dst →
            baseError N * (N : ℝ) <
              (a.count src : ℝ) / profileWeight src -
                (a.count dst : ℝ) / profileWeight dst →
            weightedBackwardMarginal (objectiveWeightSeq N) (valueOfCountSeq N)
                src (a.count src) <
              weightedForwardMarginal (objectiveWeightSeq N) (valueOfCountSeq N)
                dst (a.count dst)

namespace PairwiseScaledEventualSublinearFOCCertificate

noncomputable def toPairwiseScaledSublinearFOCCertificate
    {objectiveWeightSeq : ℕ → κ → ℝ}
    {valueOfCountSeq : ℕ → κ → ℕ → ℝ}
    {profileWeight : κ → ℝ} {target : κ → ℝ}
    (hcert :
      PairwiseScaledEventualSublinearFOCCertificate
        objectiveWeightSeq valueOfCountSeq profileWeight target) :
    PairwiseScaledSublinearFOCCertificate
      objectiveWeightSeq valueOfCountSeq profileWeight target := by
  classical
  let floorThreshold : ℕ :=
    Classical.choose (eventually_atTop.1 hcert.count_floor_eventually)
  have hfloorThreshold :
      ∀ N ≥ floorThreshold,
        ∀ a : Allocation κ, 0 < N →
          IsOptimalAtTotal (objectiveWeightSeq N) (valueOfCountSeq N) N a →
            ∀ k, hcert.floor < a.count k :=
    Classical.choose_spec (eventually_atTop.1 hcert.count_floor_eventually)
  let asymThreshold : ℕ :=
    Classical.choose
      (eventually_atTop.1 hcert.large_gap_backward_lt_forward_after_floor)
  have hasymThreshold :
      ∀ N ≥ asymThreshold,
        ∀ a : Allocation κ, 0 < N →
          IsOptimalAtTotal (objectiveWeightSeq N) (valueOfCountSeq N) N a →
            ∀ src dst,
              hcert.floor < a.count src →
              hcert.floor < a.count dst →
              hcert.baseError N * (N : ℝ) <
                (a.count src : ℝ) / profileWeight src -
                  (a.count dst : ℝ) / profileWeight dst →
              weightedBackwardMarginal (objectiveWeightSeq N) (valueOfCountSeq N)
                  src (a.count src) <
                weightedForwardMarginal (objectiveWeightSeq N) (valueOfCountSeq N)
                  dst (a.count dst) :=
    Classical.choose_spec
      (eventually_atTop.1 hcert.large_gap_backward_lt_forward_after_floor)
  let threshold : ℕ := max floorThreshold asymThreshold
  let finitePrefixError : ℝ := (∑ k : κ, 1 / profileWeight k) + 1
  refine
    { weight_pos := hcert.weight_pos
      target_eq := hcert.target_eq
      error := fun N => if N < threshold then finitePrefixError else hcert.baseError N
      error_nonneg := ?_
      error_tends_to_zero := ?_
      large_gap_backward_lt_forward := ?_ }
  · intro N
    by_cases hN : N < threshold
    · have hsum_nonneg :
          0 ≤ ∑ k : κ, 1 / profileWeight k := by
        exact Finset.sum_nonneg
          (fun k _ => div_nonneg zero_le_one
            (le_of_lt (hcert.weight_pos k)))
      rw [if_pos hN]
      dsimp [finitePrefixError]
      linarith
    · simp [hN, hcert.baseError_nonneg N]
  · exact Math.tendsToZero_if_lt_const
      hcert.baseError_tends_to_zero threshold finitePrefixError
  · intro N a hNpos hopt src dst hgap
    by_cases hsmall : N < threshold
    · exfalso
      have hgap_small :
          finitePrefixError * (N : ℝ) <
            (a.count src : ℝ) / profileWeight src -
              (a.count dst : ℝ) / profileWeight dst := by
        simpa [hsmall] using hgap
      have hsrc_count_le_total : a.count src ≤ N := by
        have hle := count_le_total a src
        have htotal_eq : a.total = N := hopt.1
        rw [htotal_eq] at hle
        exact hle
      have hsrc_count_le_total_real :
          (a.count src : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast hsrc_count_le_total
      have hdst_div_nonneg :
          0 ≤ (a.count dst : ℝ) / profileWeight dst :=
        div_nonneg (Nat.cast_nonneg _) (le_of_lt (hcert.weight_pos dst))
      have hdiff_le_src_div :
          (a.count src : ℝ) / profileWeight src -
              (a.count dst : ℝ) / profileWeight dst ≤
            (a.count src : ℝ) / profileWeight src := by
        linarith
      have hsrc_div_le_N_inv :
          (a.count src : ℝ) / profileWeight src ≤
            (N : ℝ) * (1 / profileWeight src) := by
        rw [div_eq_mul_inv, one_div]
        exact mul_le_mul_of_nonneg_right hsrc_count_le_total_real
          (inv_nonneg.mpr (le_of_lt (hcert.weight_pos src)))
      have hinv_le_sum :
          1 / profileWeight src ≤ ∑ k : κ, 1 / profileWeight k := by
        exact Finset.single_le_sum
          (fun k _ => div_nonneg zero_le_one
            (le_of_lt (hcert.weight_pos k)))
          (Finset.mem_univ src)
      have hN_nonneg : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
      have hN_inv_le_sum :
          (N : ℝ) * (1 / profileWeight src) ≤
            (N : ℝ) * ∑ k : κ, 1 / profileWeight k :=
        mul_le_mul_of_nonneg_left hinv_le_sum hN_nonneg
      have hdiff_le_sum :
          (a.count src : ℝ) / profileWeight src -
              (a.count dst : ℝ) / profileWeight dst ≤
            (N : ℝ) * ∑ k : κ, 1 / profileWeight k :=
        le_trans hdiff_le_src_div
          (le_trans hsrc_div_le_N_inv hN_inv_le_sum)
      have hNpos_real : 0 < (N : ℝ) := by
        exact_mod_cast hNpos
      have hsum_lt_prefix :
          (N : ℝ) * ∑ k : κ, 1 / profileWeight k <
            finitePrefixError * (N : ℝ) := by
        have hsum_lt :
            (∑ k : κ, 1 / profileWeight k) < finitePrefixError := by
          dsimp [finitePrefixError]
          linarith
        calc
          (N : ℝ) * ∑ k : κ, 1 / profileWeight k
              < (N : ℝ) * finitePrefixError :=
                mul_lt_mul_of_pos_left hsum_lt hNpos_real
          _ = finitePrefixError * (N : ℝ) := by ring
      exact not_lt_of_ge
        (le_trans hdiff_le_sum (le_of_lt hsum_lt_prefix)) hgap_small
    · have hthreshold_le_N : threshold ≤ N := le_of_not_gt hsmall
      have hfloorThreshold_le_threshold : floorThreshold ≤ threshold := by
        dsimp [threshold]
        exact le_max_left floorThreshold asymThreshold
      have hasymThreshold_le_threshold : asymThreshold ≤ threshold := by
        dsimp [threshold]
        exact le_max_right floorThreshold asymThreshold
      have hfloorThreshold_le_N : floorThreshold ≤ N :=
        le_trans hfloorThreshold_le_threshold hthreshold_le_N
      have hasymThreshold_le_N : asymThreshold ≤ N :=
        le_trans hasymThreshold_le_threshold hthreshold_le_N
      have hcounts_floor : ∀ k, hcert.floor < a.count k :=
        hfloorThreshold N hfloorThreshold_le_N a hNpos hopt
      have hdomN := hasymThreshold N hasymThreshold_le_N
      have hgap_base :
          hcert.baseError N * (N : ℝ) <
            (a.count src : ℝ) / profileWeight src -
              (a.count dst : ℝ) / profileWeight dst := by
        simpa [hsmall] using hgap
      exact hdomN a hNpos hopt src dst
        (hcounts_floor src) (hcounts_floor dst) hgap_base

theorem asymptoticProfile
    [Nonempty κ]
    {objectiveWeightSeq : ℕ → κ → ℝ}
    {valueOfCountSeq : ℕ → κ → ℕ → ℝ}
    {profileWeight : κ → ℝ} {target : κ → ℝ}
    (hcert :
      PairwiseScaledEventualSublinearFOCCertificate
        objectiveWeightSeq valueOfCountSeq profileWeight target) :
    AsymptoticProfile objectiveWeightSeq valueOfCountSeq target :=
  hcert.toPairwiseScaledSublinearFOCCertificate.asymptoticProfile

end PairwiseScaledEventualSublinearFOCCertificate

end Allocation
end AppliedModelingLib
