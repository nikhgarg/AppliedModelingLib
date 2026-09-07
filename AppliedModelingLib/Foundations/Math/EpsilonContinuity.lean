import AppliedModelingLib.Foundations.Probability.FiniteExpectation
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic.Linarith

open scoped BigOperators

namespace AppliedModelingLib

/-- Elementary epsilon-delta continuity at a real point. -/
def EpsilonContinuousAt (f : ℝ → ℝ) (x : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ y : ℝ, |y - x| < δ → |f y - f x| < ε

/-- Constant real functions are epsilon-delta continuous. -/
theorem epsilonContinuousAt_const (c x : ℝ) :
    EpsilonContinuousAt (fun _ : ℝ => c) x := by
  intro ε hε
  exact ⟨1, zero_lt_one, by intro y hy; simpa using hε⟩

/-- Mathlib continuity at a point implies the elementary epsilon-delta interface. -/
theorem epsilonContinuousAt_of_continuousAt {f : ℝ → ℝ} {x : ℝ}
    (hf : ContinuousAt f x) :
    EpsilonContinuousAt f x := by
  rw [Metric.continuousAt_iff] at hf
  simpa [Real.dist_eq] using hf

/--
Composing an epsilon-delta continuous real function with a mathlib-continuous
real change of parameter preserves epsilon-delta continuity.
-/
theorem epsilonContinuousAt_comp_of_continuousAt {f g : ℝ → ℝ} {x : ℝ}
    (hf : EpsilonContinuousAt f (g x))
    (hg : ContinuousAt g x) :
    EpsilonContinuousAt (fun y => f (g y)) x := by
  intro ε hε
  rcases hf ε hε with ⟨δf, hδf_pos, hfδ⟩
  rcases epsilonContinuousAt_of_continuousAt hg δf hδf_pos with
    ⟨δg, hδg_pos, hgδ⟩
  refine ⟨δg, hδg_pos, ?_⟩
  intro y hy
  exact hfδ (g y) (hgδ y hy)

/--
Epsilon-delta continuity is local: changing a function away from a
neighborhood of the point does not affect continuity at that point.
-/
theorem epsilonContinuousAt_congr_eventually {f g : ℝ → ℝ} {x : ℝ}
    (hf : EpsilonContinuousAt f x)
    (hfg : ∀ᶠ y in nhds x, f y = g y)
    (hx : f x = g x) :
    EpsilonContinuousAt g x := by
  intro ε hε
  rcases hf ε hε with ⟨δf, hδf_pos, hδf⟩
  rcases Metric.eventually_nhds_iff.1 hfg with ⟨δg, hδg_pos, hδg⟩
  refine ⟨min δf δg, lt_min hδf_pos hδg_pos, ?_⟩
  intro y hy
  have hyf : |y - x| < δf := lt_of_lt_of_le hy (min_le_left δf δg)
  have hyg : dist y x < δg := by
    simpa [Real.dist_eq] using lt_of_lt_of_le hy (min_le_right δf δg)
  have hy_eq : f y = g y := hδg hyg
  calc
    |g y - g x| = |f y - f x| := by rw [← hy_eq, ← hx]
    _ < ε := hδf y hyf

/-- Finite sums preserve mathlib continuity at a point. -/
theorem continuousAt_finset_sum {ι : Type*} [DecidableEq ι]
    (s : Finset ι) {f : ι → ℝ → ℝ} {x : ℝ}
    (hf : ∀ i ∈ s, ContinuousAt (f i) x) :
    ContinuousAt (fun y => ∑ i ∈ s, f i y) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) x)
  | insert a s ha ih =>
      have ha_cont : ContinuousAt (f a) x := hf a (Finset.mem_insert_self a s)
      have hs_cont :
          ContinuousAt (fun y => ∑ i ∈ s, f i y) x := by
        exact ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      simpa [Finset.sum_insert, ha] using ha_cont.add hs_cont

/-- Sums of epsilon-delta continuous real functions are continuous. -/
theorem epsilonContinuousAt_add {f g : ℝ → ℝ} {x : ℝ}
    (hf : EpsilonContinuousAt f x) (hg : EpsilonContinuousAt g x) :
    EpsilonContinuousAt (fun y => f y + g y) x := by
  intro ε hε
  have hhalf_pos : 0 < ε / 2 := half_pos hε
  rcases hf (ε / 2) hhalf_pos with ⟨δf, hδf_pos, hfδ⟩
  rcases hg (ε / 2) hhalf_pos with ⟨δg, hδg_pos, hgδ⟩
  refine ⟨min δf δg, lt_min hδf_pos hδg_pos, ?_⟩
  intro y hy
  have hyf : |y - x| < δf := lt_of_lt_of_le hy (min_le_left δf δg)
  have hyg : |y - x| < δg := lt_of_lt_of_le hy (min_le_right δf δg)
  have hf_bound := hfδ y hyf
  have hg_bound := hgδ y hyg
  calc
    |(f y + g y) - (f x + g x)|
        = |(f y - f x) + (g y - g x)| := by ring_nf
    _ ≤ |f y - f x| + |g y - g x| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add hf_bound hg_bound
    _ = ε := by ring

/-- Multiplying an epsilon-delta continuous real function by a constant preserves continuity. -/
theorem epsilonContinuousAt_mul_const {f : ℝ → ℝ} {x c : ℝ}
    (hf : EpsilonContinuousAt f x) :
    EpsilonContinuousAt (fun y => f y * c) x := by
  by_cases hc : c = 0
  · subst c
    simpa using epsilonContinuousAt_const 0 x
  · intro ε hε
    have hcabs_pos : 0 < |c| := abs_pos.mpr hc
    have hscaled_pos : 0 < ε / |c| := div_pos hε hcabs_pos
    rcases hf (ε / |c|) hscaled_pos with ⟨δ, hδ_pos, hδ⟩
    refine ⟨δ, hδ_pos, ?_⟩
    intro y hy
    have hfy := hδ y hy
    have hcancel : (ε / |c|) * |c| = ε := by
      calc
        (ε / |c|) * |c| = ε * (|c| / |c|) := by ring
        _ = ε * 1 := by rw [div_self (ne_of_gt hcabs_pos)]
        _ = ε := by ring
    calc
      |f y * c - f x * c| = |(f y - f x) * c| := by ring_nf
      _ = |f y - f x| * |c| := abs_mul _ _
      _ < (ε / |c|) * |c| := mul_lt_mul_of_pos_right hfy hcabs_pos
      _ = ε := hcancel

/-- Multiplying a continuous real function by a constant on the left preserves continuity. -/
theorem epsilonContinuousAt_const_mul {f : ℝ → ℝ} {x c : ℝ}
    (hf : EpsilonContinuousAt f x) :
    EpsilonContinuousAt (fun y => c * f y) x := by
  simpa [mul_comm] using epsilonContinuousAt_mul_const (c := c) hf

/-- Negating an epsilon-delta continuous real function preserves continuity. -/
theorem epsilonContinuousAt_neg {f : ℝ → ℝ} {x : ℝ}
    (hf : EpsilonContinuousAt f x) :
    EpsilonContinuousAt (fun y => - f y) x := by
  simpa using epsilonContinuousAt_const_mul (c := -1) hf

/-- Differences of epsilon-delta continuous real functions are continuous. -/
theorem epsilonContinuousAt_sub {f g : ℝ → ℝ} {x : ℝ}
    (hf : EpsilonContinuousAt f x) (hg : EpsilonContinuousAt g x) :
    EpsilonContinuousAt (fun y => f y - g y) x := by
  simpa [sub_eq_add_neg] using epsilonContinuousAt_add hf (epsilonContinuousAt_neg hg)

/-- Finite sums of epsilon-delta continuous real functions are continuous. -/
theorem epsilonContinuousAt_finset_sum {ι : Type*} [DecidableEq ι]
    (s : Finset ι) {f : ι → ℝ → ℝ} {x : ℝ}
    (hf : ∀ i ∈ s, EpsilonContinuousAt (f i) x) :
    EpsilonContinuousAt (fun y => ∑ i ∈ s, f i y) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using epsilonContinuousAt_const 0 x
  | insert i s his ih =>
      have hi : EpsilonContinuousAt (f i) x := hf i (Finset.mem_insert_self i s)
      have hs : ∀ j ∈ s, EpsilonContinuousAt (f j) x := by
        intro j hj
        exact hf j (Finset.mem_insert_of_mem hj)
      have hsum : EpsilonContinuousAt (fun y => ∑ j ∈ s, f j y) x := ih hs
      simpa [Finset.sum_insert his] using epsilonContinuousAt_add hi hsum

/--
If each finite PMF atom varies epsilon-delta continuously in a real parameter,
then the finite expectation of any fixed payoff function is continuous.
-/
theorem epsilonContinuousAt_pmfExp_of_atom
    {α : Type*} [Fintype α] [DecidableEq α]
    {μ : ℝ → PMF α} {x : ℝ}
    (hμ : ∀ a : α, EpsilonContinuousAt (fun θ => ((μ θ) a).toReal) x)
    (payoff : α → ℝ) :
    EpsilonContinuousAt (fun θ => pmfExp (μ θ) payoff) x := by
  unfold pmfExp
  exact epsilonContinuousAt_finset_sum (Finset.univ)
    (fun a _ => epsilonContinuousAt_mul_const (c := payoff a) (hμ a))

/--
If the right PMF in an independent pair expectation varies atomwise
continuously, then the pair expectation is continuous.
-/
theorem epsilonContinuousAt_pmfPairExp_right_of_atom
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (μ : PMF α) {ν : ℝ → PMF β} {x : ℝ}
    (hν : ∀ b : β, EpsilonContinuousAt (fun θ => ((ν θ) b).toReal) x)
    (payoff : α → β → ℝ) :
    EpsilonContinuousAt (fun θ => pmfPairExp μ (ν θ) payoff) x := by
  unfold pmfPairExp pmfExp
  exact epsilonContinuousAt_finset_sum (Finset.univ)
    (fun a _ =>
      epsilonContinuousAt_const_mul (c := (μ a).toReal)
        (epsilonContinuousAt_pmfExp_of_atom
          (μ := ν) (x := x) hν (fun b => payoff a b)))

/--
If the left PMF in an independent pair expectation varies atomwise
continuously, then the pair expectation is continuous.
-/
theorem epsilonContinuousAt_pmfPairExp_left_of_atom
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {μ : ℝ → PMF α} (ν : PMF β) {x : ℝ}
    (hμ : ∀ a : α, EpsilonContinuousAt (fun θ => ((μ θ) a).toReal) x)
    (payoff : α → β → ℝ) :
    EpsilonContinuousAt (fun θ => pmfPairExp (μ θ) ν payoff) x := by
  unfold pmfPairExp
  exact epsilonContinuousAt_pmfExp_of_atom
    (μ := μ) (x := x) hμ
    (fun a => pmfExp ν (fun b => payoff a b))

/--
If `f x < g x` and both functions are epsilon-delta continuous at `x`, then
`f < g` persists on some right-neighborhood of `x`.
-/
theorem exists_right_radius_lt_of_epsilonContinuousAt
    {f g : ℝ → ℝ} {x : ℝ}
    (hf : EpsilonContinuousAt f x) (hg : EpsilonContinuousAt g x)
    (hlt : f x < g x) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y : ℝ, x < y → y < x + δ → f y < g y := by
  let gap : ℝ := g x - f x
  have hgap_pos : 0 < gap := sub_pos.mpr hlt
  have hthird_pos : 0 < gap / 3 := by positivity
  rcases hf (gap / 3) hthird_pos with ⟨δf, hδf_pos, hfδ⟩
  rcases hg (gap / 3) hthird_pos with ⟨δg, hδg_pos, hgδ⟩
  refine ⟨min δf δg, lt_min hδf_pos hδg_pos, ?_⟩
  intro y hxy hy
  have hdist_min : |y - x| < min δf δg := by
    rw [abs_lt]
    constructor <;> linarith
  have hdist_f : |y - x| < δf :=
    lt_of_lt_of_le hdist_min (min_le_left δf δg)
  have hdist_g : |y - x| < δg :=
    lt_of_lt_of_le hdist_min (min_le_right δf δg)
  have hf_bound := (abs_lt.mp (hfδ y hdist_f)).2
  have hg_bound := (abs_lt.mp (hgδ y hdist_g)).1
  dsimp [gap] at hf_bound hg_bound
  linarith

end AppliedModelingLib
