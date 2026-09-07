import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic

/-!
# Uniform Convergence Helpers

Reusable Cauchy-criterion tools for sequences of functions.  These are useful
for continuum asymptotic arguments where a paper proves that every tail of a
function sequence is uniformly close to a large anchor function by an error
that tends to zero.
-/

open Filter Topology

namespace AppliedModelingLib
namespace Math

/-- If every sequence of states sees convergence to one constant limit, then
the convergence is uniform over the state space.  The proof is the elementary
diagonal-selection argument: a failure of uniformity selects one offending
state at each offending index and contradicts convergence of that selected
sequence. -/
theorem tendstoUniformly_const_of_tendsto_along_all_state_sequences
    {α β : Type*} [PseudoMetricSpace β] [Nonempty α]
    {F : ℕ → α → β} {limit : β}
    (hF : ∀ states : ℕ → α,
      Tendsto (fun n : ℕ => F n (states n)) atTop (𝓝 limit)) :
    TendstoUniformly F (fun _ => limit) atTop := by
  classical
  rw [Metric.tendstoUniformly_iff]
  intro epsilon hepsilon
  by_contra hnot
  rw [not_eventually] at hnot
  have hfrequently : ∃ᶠ n : ℕ in atTop, ∃ state : α,
      epsilon ≤ dist limit (F n state) := by
    refine hnot.mono ?_
    intro n hn
    push_neg at hn
    exact hn
  let fallback : α := Classical.choice (inferInstance : Nonempty α)
  let states : ℕ → α := fun n =>
    if hstate : ∃ state : α, epsilon ≤ dist limit (F n state) then
      Classical.choose hstate
    else fallback
  have hlarge : ∃ᶠ n : ℕ in atTop,
      epsilon ≤ dist limit (F n (states n)) := by
    refine hfrequently.mono ?_
    intro n hn
    simp only [states, dif_pos hn]
    exact Classical.choose_spec hn
  have hsmall : ∀ᶠ n : ℕ in atTop,
      dist limit (F n (states n)) < epsilon := by
    have hlimit := (Metric.tendsto_nhds.1 (hF states)) epsilon hepsilon
    filter_upwards [hlimit] with n hn
    simpa only [dist_comm] using hn
  exact frequently_false atTop
    ((hlarge.and_eventually hsmall).mono fun _ hn => (not_lt_of_ge hn.1) hn.2)

/-- Uniform convergence survives composition with a tending index map. -/
theorem TendstoUniformlyOn.comp_tendsto_index
    {ι κ α β : Type*} [UniformSpace β]
    {F : ι → α → β} {f : α → β} {p : Filter ι} {q : Filter κ}
    {s : Set α} {φ : κ → ι}
    (hF : TendstoUniformlyOn F f p s)
    (hφ : Tendsto φ q p) :
    TendstoUniformlyOn (fun k : κ => F (φ k)) f q s := by
  intro u hu
  exact hφ.eventually (hF u hu)

/-- Uniform convergence is unchanged by deleting the first term of a sequence. -/
theorem TendstoUniformlyOn.of_succ
    {α β : Type*} [UniformSpace β]
    {F : ℕ → α → β} {f : α → β} {s : Set α}
    (hF : TendstoUniformlyOn (fun n : ℕ => F (n + 1)) f atTop s) :
    TendstoUniformlyOn F f atTop s := by
  intro u hu
  obtain ⟨K, hK⟩ := eventually_atTop.1 (hF u hu)
  rw [eventually_atTop]
  refine ⟨K + 1, ?_⟩
  intro n hn x hx
  have hpred : K ≤ n - 1 := by omega
  have hidx : n - 1 + 1 = n := by omega
  simpa [hidx] using hK (n - 1) hpred x hx

/--
A uniformly Cauchy sequence of functions into a complete space has a uniform
limit on the set.
-/
theorem exists_tendstoUniformlyOn_of_uniformCauchySeqOn
    {α β : Type*} [UniformSpace β] [CompleteSpace β] [Inhabited β]
    (F : ℕ → α → β) (s : Set α)
    (hF : UniformCauchySeqOn F atTop s) :
    ∃ f : α → β, TendstoUniformlyOn F f atTop s := by
  classical
  let f : α → β := fun x =>
    if hx : x ∈ s then
      Classical.choose (cauchySeq_tendsto_of_complete (hF.cauchySeq hx))
    else
      default
  have hf : ∀ x : α, x ∈ s → Tendsto (fun n : ℕ => F n x) atTop (𝓝 (f x)) := by
    intro x hx
    have hchoose :=
      Classical.choose_spec (cauchySeq_tendsto_of_complete (hF.cauchySeq hx))
    simpa [f, hx] using hchoose
  exact ⟨f, hF.tendstoUniformlyOn_of_tendsto hf⟩

/--
Anchor Cauchy criterion.  If every tail of `F` is uniformly within `mesh M`
of a fixed large anchor `F M`, and `mesh M -> 0`, then `F` is uniformly Cauchy.
-/
theorem uniformCauchySeqOn_of_eventual_anchor_bound
    {α β : Type*} [PseudoMetricSpace β]
    (F : ℕ → α → β) (s : Set α) (mesh : ℕ → ℝ)
    (hmesh : Tendsto mesh atTop (nhds 0))
    (hmesh_nonneg : ∀ M, 0 ≤ mesh M)
    (hanchor :
      ∀ M : ℕ, ∃ K : ℕ, ∀ n : ℕ, K ≤ n →
        ∀ x : α, x ∈ s → dist (F n x) (F M x) ≤ mesh M) :
    UniformCauchySeqOn F atTop s := by
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  have hsmall :
      ∀ᶠ M : ℕ in atTop, mesh M < ε / 2 :=
    hmesh.eventually (eventually_lt_nhds (half_pos hε))
  obtain ⟨M, hMsmall⟩ := hsmall.exists
  obtain ⟨K, hK⟩ := hanchor M
  refine ⟨K, ?_⟩
  intro n hn m hm x hx
  have hn_anchor := hK n hn x hx
  have hm_anchor := hK m hm x hx
  have hdist :
      dist (F n x) (F m x) ≤ mesh M + mesh M := by
    calc
      dist (F n x) (F m x)
          ≤ dist (F n x) (F M x) + dist (F M x) (F m x) :=
            dist_triangle _ _ _
      _ ≤ mesh M + mesh M := by
            gcongr
            simpa [dist_comm] using hm_anchor
  have hsum_lt : mesh M + mesh M < ε := by
    linarith
  exact lt_of_le_of_lt hdist hsum_lt

/--
Eventual-anchor Cauchy criterion.  It is enough to have the anchor envelope
for all sufficiently large anchors; this matches many paper proofs where the
large-anchor regularity assumptions only hold eventually.
-/
theorem uniformCauchySeqOn_of_eventually_eventual_anchor_bound
    {α β : Type*} [PseudoMetricSpace β]
    (F : ℕ → α → β) (s : Set α) (mesh : ℕ → ℝ)
    (hmesh : Tendsto mesh atTop (nhds 0))
    (hmesh_nonneg : ∀ M, 0 ≤ mesh M)
    (hanchor :
      ∀ᶠ M : ℕ in atTop,
        ∃ K : ℕ, ∀ n : ℕ, K ≤ n →
          ∀ x : α, x ∈ s → dist (F n x) (F M x) ≤ mesh M) :
    UniformCauchySeqOn F atTop s := by
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  have hsmall :
      ∀ᶠ M : ℕ in atTop, mesh M < ε / 2 :=
    hmesh.eventually (eventually_lt_nhds (half_pos hε))
  obtain ⟨M, hMsmall, K, hK⟩ := (hsmall.and hanchor).exists
  refine ⟨K, ?_⟩
  intro n hn m hm x hx
  have hn_anchor := hK n hn x hx
  have hm_anchor := hK m hm x hx
  have hdist :
      dist (F n x) (F m x) ≤ mesh M + mesh M := by
    calc
      dist (F n x) (F m x)
          ≤ dist (F n x) (F M x) + dist (F M x) (F m x) :=
            dist_triangle _ _ _
      _ ≤ mesh M + mesh M := by
            gcongr
            simpa [dist_comm] using hm_anchor
  have hsum_lt : mesh M + mesh M < ε := by
    linarith
  exact lt_of_le_of_lt hdist hsum_lt

/--
Anchor convergence criterion.  The anchor Cauchy criterion plus completeness
produces a uniform limit.
-/
theorem exists_tendstoUniformlyOn_of_eventual_anchor_bound
    {α β : Type*} [PseudoMetricSpace β] [CompleteSpace β] [Inhabited β]
    (F : ℕ → α → β) (s : Set α) (mesh : ℕ → ℝ)
    (hmesh : Tendsto mesh atTop (nhds 0))
    (hmesh_nonneg : ∀ M, 0 ≤ mesh M)
    (hanchor :
      ∀ M : ℕ, ∃ K : ℕ, ∀ n : ℕ, K ≤ n →
        ∀ x : α, x ∈ s → dist (F n x) (F M x) ≤ mesh M) :
    ∃ f : α → β, TendstoUniformlyOn F f atTop s :=
  exists_tendstoUniformlyOn_of_uniformCauchySeqOn F s
    (uniformCauchySeqOn_of_eventual_anchor_bound F s mesh hmesh
      hmesh_nonneg hanchor)

/--
Eventual-anchor convergence criterion.  The anchor envelope may start only
after a finite number of anchors.
-/
theorem exists_tendstoUniformlyOn_of_eventually_eventual_anchor_bound
    {α β : Type*} [PseudoMetricSpace β] [CompleteSpace β] [Inhabited β]
    (F : ℕ → α → β) (s : Set α) (mesh : ℕ → ℝ)
    (hmesh : Tendsto mesh atTop (nhds 0))
    (hmesh_nonneg : ∀ M, 0 ≤ mesh M)
    (hanchor :
      ∀ᶠ M : ℕ in atTop,
        ∃ K : ℕ, ∀ n : ℕ, K ≤ n →
          ∀ x : α, x ∈ s → dist (F n x) (F M x) ≤ mesh M) :
    ∃ f : α → β, TendstoUniformlyOn F f atTop s :=
  exists_tendstoUniformlyOn_of_uniformCauchySeqOn F s
    (uniformCauchySeqOn_of_eventually_eventual_anchor_bound F s mesh hmesh
      hmesh_nonneg hanchor)

/--
Uniform convergence transfer through a vanishing tracking error.  If `G n`
converges uniformly to `f` on `s`, and `F n` is uniformly within `mesh n` of
`G n` with `mesh n -> 0`, then `F n` has the same uniform limit.
-/
theorem tendstoUniformlyOn_of_tendstoUniformlyOn_of_eventual_dist_le
    {α β : Type*} [PseudoMetricSpace β]
    (F G : ℕ → α → β) (f : α → β) (s : Set α) (mesh : ℕ → ℝ)
    (hG : TendstoUniformlyOn G f atTop s)
    (hmesh : Tendsto mesh atTop (nhds 0))
    (hclose :
      ∀ᶠ n : ℕ in atTop,
        ∀ x : α, x ∈ s → dist (F n x) (G n x) ≤ mesh n) :
    TendstoUniformlyOn F f atTop s := by
  rw [Metric.tendstoUniformlyOn_iff] at hG ⊢
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  have hG_event := hG (ε / 2) hhalf
  have hmesh_event :
      ∀ᶠ n : ℕ in atTop, mesh n < ε / 2 :=
    hmesh.eventually (eventually_lt_nhds hhalf)
  filter_upwards [hG_event, hmesh_event, hclose] with n hGn hmesh_n hclose_n x hx
  have hdist :
      dist (f x) (F n x) ≤ dist (f x) (G n x) + dist (G n x) (F n x) :=
    dist_triangle _ _ _
  have hclose' : dist (G n x) (F n x) ≤ mesh n := by
    simpa [dist_comm] using hclose_n x hx
  have hsum_lt :
      dist (f x) (G n x) + dist (G n x) (F n x) < ε := by
    have hsum_lt' :
        dist (f x) (G n x) + dist (G n x) (F n x) <
          ε / 2 + ε / 2 := by
      exact lt_of_le_of_lt
        (add_le_add_right hclose' (dist (f x) (G n x)))
        (add_lt_add (hGn x hx) hmesh_n)
    linarith
  exact lt_of_le_of_lt hdist hsum_lt

/--
Pointwise convergence over a finite index set is uniform convergence over that
index set.  This packages the standard "take the maximum burn-in over finitely
many coordinates" step used in learning and finite-sample convergence
arguments.
-/
theorem tendstoUniformlyOn_univ_of_fintype
    {α β : Type*} [Fintype α] [PseudoMetricSpace β]
    (F : ℕ → α → β) (f : α → β)
    (h : ∀ x : α, Tendsto (fun n : ℕ => F n x) atTop (nhds (f x))) :
    TendstoUniformlyOn F f atTop Set.univ := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hclose :
      ∀ x : α, ∀ᶠ n : ℕ in atTop, dist (f x) (F n x) < ε := by
    intro x
    have hx : Tendsto (fun n : ℕ => F n x) atTop (nhds (f x)) := h x
    exact ((Metric.tendsto_nhds.1 hx) ε hε).mono fun n hn => by
      simpa [dist_comm] using hn
  exact (eventually_all.2 hclose).mono fun _n hn x _hx => hn x

/--
Uniform convergence over each coordinate of a finite right-hand index lifts to
uniform convergence on the product domain.  This is the mixed continuous/finite
version of taking a common burn-in across finitely many coordinates.
-/
theorem tendstoUniformlyOn_prod_right_of_finite
    {α β ι κ : Type*} [Finite ι] [PseudoMetricSpace β]
    {F : κ → α → ι → β} {f : α → ι → β} {p : Filter κ} {s : Set α}
    (h :
      ∀ i : ι,
        TendstoUniformlyOn (fun k : κ => fun x : α => F k x i)
          (fun x : α => f x i) p s) :
    TendstoUniformlyOn
      (fun k : κ => fun x : α × ι => F k x.1 x.2)
      (fun x : α × ι => f x.1 x.2) p (s ×ˢ Set.univ) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hclose :
      ∀ i : ι, ∀ᶠ k : κ in p,
        ∀ x : α, x ∈ s → dist (f x i) (F k x i) < ε := by
    intro i
    exact (Metric.tendstoUniformlyOn_iff.1 (h i)) ε hε
  exact (eventually_all.2 hclose).mono fun k hk x hx => by
    exact hk x.2 x.1 hx.1

/--
Uniform convergence through representative tracking.  If an estimator is
uniformly close to `f` evaluated at a representative point, the representatives
uniformly approach the true point, and `f` is Lipschitz in that point uniformly
over the auxiliary index, then the estimator converges uniformly to `f`.

This is the deterministic core behind grid/representative learning arguments:
probability-specific laws of large numbers supply `htrack`, while the mesh or
ranking argument supplies `hrep`.
-/
theorem tendstoUniformlyOn_prod_of_lipschitz_tracking_rep
    {ι : Type*}
    (F : ℕ → ℝ → ι → ℝ) (f : ℝ → ι → ℝ)
    (rep : ℕ → ℝ → ℝ) (s : Set ℝ)
    (noise mesh : ℕ → ℝ) (K : ℝ)
    (hK : 0 ≤ K)
    (hnoise : Tendsto noise atTop (nhds 0))
    (hmesh : Tendsto mesh atTop (nhds 0))
    (htrack :
      ∀ᶠ n : ℕ in atTop,
        ∀ θ : ℝ, θ ∈ s → ∀ y : ι,
          dist (F n θ y) (f (rep n θ) y) ≤ noise n)
    (hrep :
      ∀ᶠ n : ℕ in atTop,
        ∀ θ : ℝ, θ ∈ s → dist (rep n θ) θ ≤ mesh n)
    (hlip :
      ∀ θ θ' : ℝ, ∀ y : ι,
        dist (f θ y) (f θ' y) ≤ K * dist θ θ') :
    TendstoUniformlyOn
      (fun n : ℕ => fun p : ℝ × ι => F n p.1 p.2)
      (fun p : ℝ × ι => f p.1 p.2) atTop (s ×ˢ Set.univ) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hscaled : Tendsto (fun n : ℕ => K * mesh n) atTop (nhds 0) := by
    simpa using (tendsto_const_nhds (x := K)).mul hmesh
  have hsum :
      Tendsto (fun n : ℕ => noise n + K * mesh n) atTop (nhds 0) := by
    simpa using hnoise.add hscaled
  have hsmall :
      ∀ᶠ n : ℕ in atTop, noise n + K * mesh n < ε :=
    hsum.eventually (eventually_lt_nhds hε)
  filter_upwards [htrack, hrep, hsmall] with n htrack_n hrep_n hsmall_n p hp
  have hpθ : p.1 ∈ s := hp.1
  have htrack_point :
      dist (F n p.1 p.2) (f (rep n p.1) p.2) ≤ noise n :=
    htrack_n p.1 hpθ p.2
  have hrep_point : dist (rep n p.1) p.1 ≤ mesh n :=
    hrep_n p.1 hpθ
  have hlip_point :
      dist (f p.1 p.2) (f (rep n p.1) p.2) ≤
        K * dist p.1 (rep n p.1) :=
    hlip p.1 (rep n p.1) p.2
  have hdist :
      dist (f p.1 p.2) (F n p.1 p.2) ≤
        K * mesh n + noise n := by
    calc
      dist (f p.1 p.2) (F n p.1 p.2)
          ≤ dist (f p.1 p.2) (f (rep n p.1) p.2) +
              dist (f (rep n p.1) p.2) (F n p.1 p.2) :=
            dist_triangle _ _ _
      _ ≤ K * dist p.1 (rep n p.1) + noise n := by
            gcongr
            simpa [dist_comm] using htrack_point
      _ ≤ K * mesh n + noise n := by
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_right
              (mul_le_mul_of_nonneg_left
                (by simpa [dist_comm] using hrep_point) hK)
              (noise n)
  have hsum_comm : K * mesh n + noise n = noise n + K * mesh n := by
    ring
  exact lt_of_le_of_lt hdist (by simpa [hsum_comm] using hsmall_n)

end Math
end AppliedModelingLib
