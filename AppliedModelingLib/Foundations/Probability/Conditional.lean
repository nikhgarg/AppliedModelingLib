import AppliedModelingLib.Foundations.Probability.FiniteExpectation
import Mathlib.Topology.Instances.Real.Lemmas

namespace AppliedModelingLib

/-- A convenient algebra lemma for positivity after division by a positive real. -/
theorem zero_lt_div_iff_pos_right {a b : ℝ} (hb : 0 < b) :
    0 < a / b ↔ 0 < a := by
  constructor
  · intro hdiv
    have hprod : 0 < (a / b) * b := mul_pos hdiv hb
    have hcancel : (a / b) * b = a := by
      field_simp [hb.ne']
    calc
      0 < (a / b) * b := hprod
      _ = a := hcancel
  · intro ha
    by_contra hnot
    have hnonpos : a / b ≤ 0 := le_of_not_gt hnot
    have hprod_nonpos : (a / b) * b ≤ 0 := by
      exact mul_nonpos_of_nonpos_of_nonneg hnonpos (le_of_lt hb)
    have hcancel : (a / b) * b = a := by
      field_simp [hb.ne']
    have : a ≤ 0 := by
      calc
        a = (a / b) * b := hcancel.symm
        _ ≤ 0 := hprod_nonpos
    linarith

/-- Expectation of `f` restricted to an event `p`, implemented via an indicator. -/
noncomputable def pmfIndicatorExp {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p] (f : α → ℝ) : ℝ :=
  pmfExp μ (fun a => if p a then f a else 0)

theorem pmfIndicatorExp_eq_zero_of_pmfProb_eq_zero {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p] (f : α → ℝ)
    (hprob : pmfProb μ p = 0) :
    pmfIndicatorExp μ p f = 0 := by
  unfold pmfIndicatorExp pmfExp
  have hsum_nonneg : ∀ a : α, 0 ≤ (μ a).toReal * (if p a then (1 : ℝ) else 0) := by
    intro a
    exact mul_nonneg ENNReal.toReal_nonneg (by by_cases hp : p a <;> simp [hp])
  have hsum_nonneg' : ∀ a ∈ (Finset.univ : Finset α), 0 ≤ (μ a).toReal * (if p a then (1 : ℝ) else 0) := by
    intro a _
    exact hsum_nonneg a
  have hprob' : ∑ b : α, (μ b).toReal * (if p b then (1 : ℝ) else 0) = 0 := by
    simpa [pmfProb, pmfExp] using hprob
  have hmass_zero : ∀ a : α, p a → (μ a).toReal = 0 := by
    intro a ha
    have hle : (μ a).toReal ≤ 0 := by
      have hsingle : (μ a).toReal * (if p a then (1 : ℝ) else 0) ≤
          ∑ b : α, (μ b).toReal * (if p b then (1 : ℝ) else 0) := by
        exact Finset.single_le_sum hsum_nonneg' (Finset.mem_univ a)
      have hsingle' : (μ a).toReal * (if p a then (1 : ℝ) else 0) ≤ 0 := by
        rwa [hprob'] at hsingle
      simpa [ha] using hsingle'
    exact le_antisymm hle ENNReal.toReal_nonneg
  have hterm : ∀ a : α, (μ a).toReal * (if p a then f a else 0) = 0 := by
    intro a
    by_cases ha : p a
    · simp [ha, hmass_zero a ha]
    · simp [ha]
  calc
    ∑ a : α, (μ a).toReal * (if p a then f a else 0)
        = ∑ a : α, (0 : ℝ) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          exact hterm a
    _ = 0 := by simp

@[simp] theorem pmfIndicatorExp_const_one {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p] :
    pmfIndicatorExp μ p (fun _ => 1) = pmfProb μ p := by
  rfl

@[simp] theorem pmfIndicatorExp_const {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p] (c : ℝ) :
    pmfIndicatorExp μ p (fun _ => c) = pmfProb μ p * c := by
  classical
  unfold pmfIndicatorExp pmfProb pmfExp
  calc
    ∑ a : α, (μ a).toReal * (if p a then c else 0)
        = ∑ a : α, ((μ a).toReal * (if p a then (1 : ℝ) else 0)) * c := by
            refine Finset.sum_congr rfl ?_
            intro a _
            by_cases hp : p a <;> simp [hp]
    _ = (∑ a : α, (μ a).toReal * (if p a then (1 : ℝ) else 0)) * c := by
            rw [Finset.sum_mul]

/-- Multiplying an indicator integrand by a constant pulls out of the expectation. -/
theorem pmfIndicatorExp_const_mul {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p] (c : ℝ) (f : α → ℝ) :
    pmfIndicatorExp μ p (fun a => c * f a) = c * pmfIndicatorExp μ p f := by
  unfold pmfIndicatorExp pmfExp
  calc
    ∑ a : α, (μ a).toReal * (if p a then c * f a else 0) =
        ∑ a : α, c * ((μ a).toReal * (if p a then f a else 0)) := by
          apply Finset.sum_congr rfl
          intro a _
          by_cases ha : p a
          · simp [ha]
            ring
          · simp [ha]
    _ = c * ∑ a : α, (μ a).toReal * (if p a then f a else 0) := by
      rw [Finset.mul_sum]

/-- Conditional expectation of `f` on event `p`, with value `0` when `p` has zero probability. -/
noncomputable def pmfConditionalExp {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p] (f : α → ℝ) : ℝ :=
  let q := pmfProb μ p
  if _h : q = 0 then 0 else pmfIndicatorExp μ p f / q

@[simp] theorem pmfConditionalExp_of_prob_zero {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p] (f : α → ℝ)
    (h : pmfProb μ p = 0) :
    pmfConditionalExp μ p f = 0 := by
  simp [pmfConditionalExp, h]

theorem pmfConditionalExp_eq_div_of_pos {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p] (f : α → ℝ)
    (h : 0 < pmfProb μ p) :
    pmfConditionalExp μ p f = pmfIndicatorExp μ p f / pmfProb μ p := by
  simp [pmfConditionalExp, h.ne']

/-- A constant multiplier pulls through a finite conditional expectation. -/
theorem pmfConditionalExp_const_mul {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p] (κ : ℝ) (f : α → ℝ) :
    pmfConditionalExp μ p (fun a => κ * f a) = κ * pmfConditionalExp μ p f := by
  classical
  by_cases hzero : pmfProb μ p = 0
  · rw [pmfConditionalExp_of_prob_zero μ p (fun a => κ * f a) hzero,
      pmfConditionalExp_of_prob_zero μ p f hzero]
    ring
  · have hpos : 0 < pmfProb μ p :=
      lt_of_le_of_ne (pmfProb_nonneg μ p) (by simpa [eq_comm] using hzero)
    rw [pmfConditionalExp_eq_div_of_pos μ p (fun a => κ * f a) hpos,
      pmfConditionalExp_eq_div_of_pos μ p f hpos]
    unfold pmfIndicatorExp
    have hpoint : (fun a => if p a then κ * f a else 0) =
        (fun a => κ * (if p a then f a else 0)) := by
      funext a
      by_cases ha : p a <;> simp [ha]
    rw [hpoint, pmfExp_const_mul]
    ring

/-- Conditional expectations preserve subtraction of real-valued integrands. -/
theorem pmfConditionalExp_sub {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p] (f g : α → ℝ) :
    pmfConditionalExp μ p (fun a => f a - g a) =
      pmfConditionalExp μ p f - pmfConditionalExp μ p g := by
  classical
  by_cases hzero : pmfProb μ p = 0
  · rw [pmfConditionalExp_of_prob_zero μ p (fun a => f a - g a) hzero,
      pmfConditionalExp_of_prob_zero μ p f hzero,
      pmfConditionalExp_of_prob_zero μ p g hzero]
    ring
  · have hpos : 0 < pmfProb μ p :=
      lt_of_le_of_ne (pmfProb_nonneg μ p) (by simpa [eq_comm] using hzero)
    rw [pmfConditionalExp_eq_div_of_pos μ p (fun a => f a - g a) hpos,
      pmfConditionalExp_eq_div_of_pos μ p f hpos,
      pmfConditionalExp_eq_div_of_pos μ p g hpos]
    unfold pmfIndicatorExp
    have hpoint : (fun a => if p a then f a - g a else 0) =
        (fun a => (if p a then f a else 0) - (if p a then g a else 0)) := by
      funext a
      by_cases ha : p a <;> simp [ha]
    rw [hpoint, pmfExp_sub]
    ring

/-- Positive-probability conditional expectation with the denominator cleared. -/
theorem pmfConditionalExp_mul_prob_eq_indicatorExp_of_pos
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p] (f : α → ℝ)
    (h : 0 < pmfProb μ p) :
    pmfConditionalExp μ p f * pmfProb μ p = pmfIndicatorExp μ p f := by
  rw [pmfConditionalExp_eq_div_of_pos μ p f h]
  field_simp [h.ne']

theorem pmfIndicatorExp_nonneg_of_nonneg
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p] (f : α → ℝ)
    (hf : ∀ a, p a → 0 ≤ f a) :
    0 ≤ pmfIndicatorExp μ p f := by
  unfold pmfIndicatorExp pmfExp
  refine Finset.sum_nonneg ?_
  intro a _
  refine mul_nonneg ENNReal.toReal_nonneg ?_
  by_cases hp : p a
  · simpa [hp] using hf a hp
  · simp [hp]

/-- Indicator expectations over an event inherit a pointwise upper bound. -/
theorem pmfIndicatorExp_le_prob_mul_of_forall_le
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p] (f : α → ℝ)
    {c : ℝ} (hf : ∀ a, p a → f a ≤ c) :
    pmfIndicatorExp μ p f ≤ pmfProb μ p * c := by
  unfold pmfIndicatorExp pmfProb pmfExp
  calc
    (∑ a : α, (μ a).toReal * (if p a then f a else 0))
        ≤ ∑ a : α, (μ a).toReal * (if p a then c else 0) := by
            refine Finset.sum_le_sum ?_
            intro a _
            by_cases hp : p a
            · simpa [hp] using
                mul_le_mul_of_nonneg_left (hf a hp) ENNReal.toReal_nonneg
            · simp [hp]
    _ = (∑ a : α, (μ a).toReal * (if p a then (1 : ℝ) else 0)) * c := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl ?_
            intro a _
            by_cases hp : p a <;> simp [hp]

/-- The conditional expectation of a constant-one value is one on positive events. -/
theorem pmfConditionalExp_const_one_eq_one_of_pos
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p]
    (h : 0 < pmfProb μ p) :
    pmfConditionalExp μ p (fun _ => (1 : ℝ)) = 1 := by
  rw [pmfConditionalExp_eq_div_of_pos μ p (fun _ => (1 : ℝ)) h]
  simp [h.ne']

/-- Conditional expectations preserve nonnegativity on positive events. -/
theorem pmfConditionalExp_nonneg_of_nonneg
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p] (f : α → ℝ)
    (hf : ∀ a, p a → 0 ≤ f a) :
    0 ≤ pmfConditionalExp μ p f := by
  by_cases hzero : pmfProb μ p = 0
  · simpa [pmfConditionalExp_of_prob_zero μ p f hzero]
  · have hpos : 0 < pmfProb μ p :=
      lt_of_le_of_ne (pmfProb_nonneg μ p) (by simpa [eq_comm] using hzero)
    rw [pmfConditionalExp_eq_div_of_pos μ p f hpos]
    exact div_nonneg (pmfIndicatorExp_nonneg_of_nonneg μ p f hf) (le_of_lt hpos)

/-- Conditional expectations preserve upper bounds on positive events. -/
theorem pmfConditionalExp_le_of_forall_le_of_pos
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p] (f : α → ℝ)
    (h : 0 < pmfProb μ p) {c : ℝ}
    (hf : ∀ a, p a → f a ≤ c) :
    pmfConditionalExp μ p f ≤ c := by
  rw [pmfConditionalExp_eq_div_of_pos μ p f h]
  have hle := pmfIndicatorExp_le_prob_mul_of_forall_le μ p f hf
  rw [div_le_iff₀ h]
  calc
    pmfIndicatorExp μ p f ≤ pmfProb μ p * c := hle
    _ = c * pmfProb μ p := by ring

/-- Conditional expectations preserve interval bounds on positive events. -/
theorem pmfConditionalExp_mem_Icc_of_mem_Icc_of_pos
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p] (f : α → ℝ)
    (h : 0 < pmfProb μ p) {a b : ℝ}
    (hf : ∀ x, p x → f x ∈ Set.Icc a b) :
    pmfConditionalExp μ p f ∈ Set.Icc a b := by
  constructor
  · have hneg :
        pmfConditionalExp μ p (fun x => -f x) ≤ -a :=
      pmfConditionalExp_le_of_forall_le_of_pos μ p (fun x => -f x) h
        (fun x hx => neg_le_neg (hf x hx).1)
    rw [pmfConditionalExp_eq_div_of_pos μ p f h]
    rw [pmfConditionalExp_eq_div_of_pos μ p (fun x => -f x) h] at hneg
    have hind_neg :
        pmfIndicatorExp μ p (fun x => -f x) = -pmfIndicatorExp μ p f := by
      unfold pmfIndicatorExp pmfExp
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl ?_
      intro x _
      by_cases hx : p x <;> simp [hx]
    rw [hind_neg, neg_div] at hneg
    linarith
  · exact pmfConditionalExp_le_of_forall_le_of_pos μ p f h
      (fun x hx => (hf x hx).2)

theorem pmfConditionalExp_pos_iff {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p] (f : α → ℝ)
    (h : 0 < pmfProb μ p) :
    0 < pmfConditionalExp μ p f ↔ 0 < pmfIndicatorExp μ p f := by
  rw [pmfConditionalExp_eq_div_of_pos (μ := μ) (p := p) (f := f) h]
  exact zero_lt_div_iff_pos_right h

/--
Finite law of total expectation over the fibers of a state map.

The conditional expectation is defined as `0` on zero-probability fibers, so the
formula does not need a separate support restriction.
-/
theorem pmfExp_eq_sum_state_prob_mul_conditionalExp
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (μ : PMF α) (state : α → β) (f : α → ℝ) :
    pmfExp μ f =
      ∑ b : β,
        pmfProb μ (fun a => state a = b) *
          pmfConditionalExp μ (fun a => state a = b) f := by
  classical
  symm
  have hterm :
      ∀ b : β,
        pmfProb μ (fun a => state a = b) *
            pmfConditionalExp μ (fun a => state a = b) f =
          pmfIndicatorExp μ (fun a => state a = b) f := by
    intro b
    by_cases hpos : 0 < pmfProb μ (fun a => state a = b)
    · have hclear :=
        pmfConditionalExp_mul_prob_eq_indicatorExp_of_pos
          (μ := μ) (p := fun a => state a = b) (f := f) hpos
      calc
        pmfProb μ (fun a => state a = b) *
            pmfConditionalExp μ (fun a => state a = b) f
            =
          pmfConditionalExp μ (fun a => state a = b) f *
            pmfProb μ (fun a => state a = b) := by ring
        _ = pmfIndicatorExp μ (fun a => state a = b) f := hclear
    · have hzero : pmfProb μ (fun a => state a = b) = 0 := by
        exact le_antisymm (le_of_not_gt hpos)
          (pmfProb_nonneg μ (fun a => state a = b))
      simp [hzero, pmfIndicatorExp_eq_zero_of_pmfProb_eq_zero]
  calc
    ∑ b : β,
        pmfProb μ (fun a => state a = b) *
          pmfConditionalExp μ (fun a => state a = b) f
        =
      ∑ b : β, pmfIndicatorExp μ (fun a => state a = b) f := by
        refine Finset.sum_congr rfl ?_
        intro b _
        exact hterm b
    _ = pmfExp μ f := by
        unfold pmfIndicatorExp pmfExp
        calc
          ∑ b : β, ∑ a : α,
              (μ a).toReal * (if state a = b then f a else 0)
              =
            ∑ a : α, ∑ b : β,
              (μ a).toReal * (if state a = b then f a else 0) := by
              exact Finset.sum_comm
          _ = ∑ a : α, (μ a).toReal * f a := by
              refine Finset.sum_congr rfl ?_
              intro a _
              calc
                ∑ b : β,
                    (μ a).toReal * (if state a = b then f a else 0)
                    =
                  ∑ b : β,
                    if b = state a then (μ a).toReal * f a else 0 := by
                    refine Finset.sum_congr rfl ?_
                    intro b _
                    by_cases hb : state a = b
                    · rw [if_pos hb, if_pos hb.symm]
                    · have hb' : b ≠ state a := fun h => hb h.symm
                      rw [if_neg hb, if_neg hb']
                      ring
                _ = (μ a).toReal * f a := by
                    simpa using
                      (Finset.sum_ite_eq' Finset.univ (state a)
                        (fun _ : β => (μ a).toReal * f a))

/--
If every positive-probability fiber of a finite state map has positive
conditional expectation, then the unconditional expectation is positive.
-/
theorem pmfExp_pos_of_state_conditionalExp_pos
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (μ : PMF α) (state : α → β) (f : α → ℝ)
    (hcond : ∀ b : β, 0 < pmfProb μ (fun a => state a = b) →
      0 < pmfConditionalExp μ (fun a => state a = b) f) :
    0 < pmfExp μ f := by
  classical
  rw [pmfExp_eq_sum_state_prob_mul_conditionalExp μ state f]
  have htotal : pmfProb μ (fun _ : α => True) = 1 := by
    simp [pmfProb]
  have htotal_pos : 0 < pmfProb μ (fun _ : α => True) := by
    rw [htotal]
    norm_num
  rcases (pmfProb_pos_iff_exists_pos_mass μ (fun _ : α => True)).mp htotal_pos with
    ⟨a₀, _htrue, hmass⟩
  let b₀ : β := state a₀
  have hb₀_prob : 0 < pmfProb μ (fun a => state a = b₀) :=
    pmfProb_pos_of_mass μ (fun a => state a = b₀) a₀ rfl hmass
  have hb₀_cond : 0 < pmfConditionalExp μ (fun a => state a = b₀) f :=
    hcond b₀ hb₀_prob
  have hterm_pos :
      0 < pmfProb μ (fun a => state a = b₀) *
        pmfConditionalExp μ (fun a => state a = b₀) f :=
    mul_pos hb₀_prob hb₀_cond
  have hnonneg :
      ∀ b : β,
        0 ≤ pmfProb μ (fun a => state a = b) *
          pmfConditionalExp μ (fun a => state a = b) f := by
    intro b
    by_cases hpos : 0 < pmfProb μ (fun a => state a = b)
    · exact mul_nonneg (pmfProb_nonneg μ (fun a => state a = b))
        (le_of_lt (hcond b hpos))
    · have hzero : pmfProb μ (fun a => state a = b) = 0 := by
        exact le_antisymm (le_of_not_gt hpos)
          (pmfProb_nonneg μ (fun a => state a = b))
      simp [hzero]
  have hle :
      pmfProb μ (fun a => state a = b₀) *
          pmfConditionalExp μ (fun a => state a = b₀) f ≤
        ∑ b : β,
          pmfProb μ (fun a => state a = b) *
            pmfConditionalExp μ (fun a => state a = b) f := by
    exact Finset.single_le_sum (fun b _ => hnonneg b) (Finset.mem_univ b₀)
  exact lt_of_lt_of_le hterm_pos hle

/-- Conditional probability of event `q` given event `p` under a finite PMF. -/
noncomputable def pmfConditionalProb {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p q : α → Prop) [DecidablePred p] [DecidablePred q] : ℝ :=
  pmfConditionalExp μ p (fun a => if q a then 1 else 0)

/-- The indicator expectation of `q` restricted to `p` is `Pr[p and q]`. -/
theorem pmfIndicatorExp_event_eq_inter_prob
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p q : α → Prop) [DecidablePred p] [DecidablePred q] :
    pmfIndicatorExp μ p (fun a => if q a then 1 else 0) =
      pmfProb μ (fun a => p a ∧ q a) := by
  classical
  unfold pmfIndicatorExp pmfProb
  refine pmfExp_congr μ ?_
  intro a
  by_cases hp : p a <;> by_cases hq : q a <;> simp [hp, hq]

/-- Positive-probability conditional event formula for finite PMFs. -/
theorem pmfConditionalProb_eq_inter_div_of_pos
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    (h : 0 < pmfProb μ p) :
    pmfConditionalProb μ p q =
      pmfProb μ (fun a => p a ∧ q a) / pmfProb μ p := by
  unfold pmfConditionalProb
  rw [pmfConditionalExp_eq_div_of_pos μ p (fun a => if q a then 1 else 0) h]
  rw [pmfIndicatorExp_event_eq_inter_prob]

/--
Uniform conditional probability bound for a finite fiber with at most one
favorable point.  This is the algebraic deferred-decisions step: if the
conditioning event has `fiberCard` points and the target event has at most one
point inside it, then the conditional probability is at most `1 / fiberCard`.
-/
theorem pmfConditionalProb_uniformPMF_le_inv_of_condition_eventSet_card_le_one
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (condition event : α → Prop) [DecidablePred condition]
    [DecidablePred event] {fiberCard : ℕ}
    (conditionSet eventSet : Finset α)
    (hcondition_mem : ∀ a, a ∈ conditionSet ↔ condition a)
    (hevent_mem : ∀ a, a ∈ eventSet ↔ condition a ∧ event a)
    (hfiber_pos : 0 < fiberCard)
    (hcondition_card : conditionSet.card = fiberCard)
    (hevent_card : eventSet.card ≤ 1) :
    pmfConditionalProb (uniformPMF α) condition event ≤
      ((fiberCard : ℝ)⁻¹) := by
  classical
  have hcondition_prob :
      pmfProb (uniformPMF α) condition =
        (conditionSet.card : ℝ) / (Fintype.card α : ℝ) := by
    calc
      pmfProb (uniformPMF α) condition =
          pmfProb (uniformPMF α) (fun a => a ∈ conditionSet) := by
            exact pmfProb_congr (uniformPMF α) (by
              intro a
              constructor
              · intro ha
                exact (hcondition_mem a).2 ha
              · intro ha
                exact (hcondition_mem a).1 ha)
      _ = (conditionSet.card : ℝ) / (Fintype.card α : ℝ) := by
            exact pmfProb_uniformPMF_finset conditionSet
  have hcondition_pos : 0 < pmfProb (uniformPMF α) condition := by
    rw [hcondition_prob, hcondition_card]
    exact div_pos
      (by exact_mod_cast hfiber_pos)
      (by exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty α›))
  have hevent_prob :
      pmfProb (uniformPMF α) (fun a => condition a ∧ event a) =
        (eventSet.card : ℝ) / (Fintype.card α : ℝ) := by
    calc
      pmfProb (uniformPMF α) (fun a => condition a ∧ event a) =
          pmfProb (uniformPMF α) (fun a => a ∈ eventSet) := by
            exact pmfProb_congr (uniformPMF α) (by
              intro a
              constructor
              · intro ha
                exact (hevent_mem a).2 ha
              · intro ha
                exact (hevent_mem a).1 ha)
      _ = (eventSet.card : ℝ) / (Fintype.card α : ℝ) := by
            exact pmfProb_uniformPMF_finset eventSet
  have hevent_card_real : (eventSet.card : ℝ) ≤ 1 := by
    exact_mod_cast hevent_card
  have hfiber_pos_real : 0 < (fiberCard : ℝ) := by
    exact_mod_cast hfiber_pos
  have hcard_alpha_pos : 0 < (Fintype.card α : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty α›)
  rw [pmfConditionalProb_eq_inter_div_of_pos
    (uniformPMF α) condition event hcondition_pos]
  rw [hevent_prob, hcondition_prob, hcondition_card]
  calc
    ((eventSet.card : ℝ) / (Fintype.card α : ℝ)) /
        ((fiberCard : ℝ) / (Fintype.card α : ℝ)) =
        (eventSet.card : ℝ) / (fiberCard : ℝ) := by
          field_simp [hcard_alpha_pos.ne', hfiber_pos_real.ne']
    _ ≤ 1 / (fiberCard : ℝ) :=
          div_le_div_of_nonneg_right hevent_card_real
            (le_of_lt hfiber_pos_real)
    _ = ((fiberCard : ℝ)⁻¹) := by rw [one_div]

/--
Uniform conditional probability bound for a finite fiber with at most one
favorable point and a certified lower bound on the fiber size.  This is the
form used by deferred-decision arguments that inject each possible continuation
into the realized conditioning fiber without classifying every point of that
fiber.
-/
theorem pmfConditionalProb_uniformPMF_le_inv_of_condition_eventSet_card_le_one_of_le
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (condition event : α → Prop) [DecidablePred condition]
    [DecidablePred event] {fiberCard : ℕ}
    (conditionSet eventSet : Finset α)
    (hcondition_mem : ∀ a, a ∈ conditionSet ↔ condition a)
    (hevent_mem : ∀ a, a ∈ eventSet ↔ condition a ∧ event a)
    (hfiber_pos : 0 < fiberCard)
    (hfiber_le_condition_card : fiberCard ≤ conditionSet.card)
    (hevent_card : eventSet.card ≤ 1) :
    pmfConditionalProb (uniformPMF α) condition event ≤
      ((fiberCard : ℝ)⁻¹) := by
  classical
  have hcondition_card_pos : 0 < conditionSet.card :=
    lt_of_lt_of_le hfiber_pos hfiber_le_condition_card
  have hcondition_prob :
      pmfProb (uniformPMF α) condition =
        (conditionSet.card : ℝ) / (Fintype.card α : ℝ) := by
    calc
      pmfProb (uniformPMF α) condition =
          pmfProb (uniformPMF α) (fun a => a ∈ conditionSet) := by
            exact pmfProb_congr (uniformPMF α) (by
              intro a
              constructor
              · intro ha
                exact (hcondition_mem a).2 ha
              · intro ha
                exact (hcondition_mem a).1 ha)
      _ = (conditionSet.card : ℝ) / (Fintype.card α : ℝ) := by
            exact pmfProb_uniformPMF_finset conditionSet
  have hcondition_pos : 0 < pmfProb (uniformPMF α) condition := by
    rw [hcondition_prob]
    exact div_pos
      (by exact_mod_cast hcondition_card_pos)
      (by exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty α›))
  have hevent_prob :
      pmfProb (uniformPMF α) (fun a => condition a ∧ event a) =
        (eventSet.card : ℝ) / (Fintype.card α : ℝ) := by
    calc
      pmfProb (uniformPMF α) (fun a => condition a ∧ event a) =
          pmfProb (uniformPMF α) (fun a => a ∈ eventSet) := by
            exact pmfProb_congr (uniformPMF α) (by
              intro a
              constructor
              · intro ha
                exact (hevent_mem a).2 ha
              · intro ha
                exact (hevent_mem a).1 ha)
      _ = (eventSet.card : ℝ) / (Fintype.card α : ℝ) := by
            exact pmfProb_uniformPMF_finset eventSet
  have hevent_card_real : (eventSet.card : ℝ) ≤ 1 := by
    exact_mod_cast hevent_card
  have hcondition_card_pos_real : 0 < (conditionSet.card : ℝ) := by
    exact_mod_cast hcondition_card_pos
  have hfiber_pos_real : 0 < (fiberCard : ℝ) := by
    exact_mod_cast hfiber_pos
  have hfiber_le_condition_card_real :
      (fiberCard : ℝ) ≤ (conditionSet.card : ℝ) := by
    exact_mod_cast hfiber_le_condition_card
  have hcard_alpha_pos : 0 < (Fintype.card α : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty α›)
  rw [pmfConditionalProb_eq_inter_div_of_pos
    (uniformPMF α) condition event hcondition_pos]
  rw [hevent_prob, hcondition_prob]
  calc
    ((eventSet.card : ℝ) / (Fintype.card α : ℝ)) /
        ((conditionSet.card : ℝ) / (Fintype.card α : ℝ)) =
        (eventSet.card : ℝ) / (conditionSet.card : ℝ) := by
          field_simp [hcard_alpha_pos.ne', hcondition_card_pos_real.ne']
    _ ≤ 1 / (conditionSet.card : ℝ) :=
      div_le_div_of_nonneg_right hevent_card_real
        (le_of_lt hcondition_card_pos_real)
    _ = ((conditionSet.card : ℝ)⁻¹) := by rw [one_div]
    _ ≤ ((fiberCard : ℝ)⁻¹) := by
      exact
        (inv_le_inv₀ hcondition_card_pos_real hfiber_pos_real).mpr
          hfiber_le_condition_card_real

/--
Uniform conditional probability bound for a finite fiber with at most one
favorable point, stated with canonical filtered finite sets.
-/
theorem pmfConditionalProb_uniformPMF_le_inv_of_condition_card_event_card_le_one
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (condition event : α → Prop) [DecidablePred condition]
    [DecidablePred event] {fiberCard : ℕ}
    (hfiber_pos : 0 < fiberCard)
    (hcondition_card :
      ((Finset.univ : Finset α).filter condition).card = fiberCard)
    (hevent_card :
      ((Finset.univ : Finset α).filter
        (fun a => condition a ∧ event a)).card ≤ 1) :
    pmfConditionalProb (uniformPMF α) condition event ≤
      ((fiberCard : ℝ)⁻¹) := by
  classical
  let conditionSet : Finset α :=
    (Finset.univ : Finset α).filter condition
  let eventSet : Finset α :=
    (Finset.univ : Finset α).filter fun a => condition a ∧ event a
  have hcondition_prob :
      pmfProb (uniformPMF α) condition =
        (conditionSet.card : ℝ) / (Fintype.card α : ℝ) := by
    simpa [conditionSet] using
      (pmfProb_uniformPMF_finset (α := α) conditionSet)
  have hcondition_pos : 0 < pmfProb (uniformPMF α) condition := by
    rw [hcondition_prob, hcondition_card]
    exact div_pos
      (by exact_mod_cast hfiber_pos)
      (by exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty α›))
  have hevent_prob :
      pmfProb (uniformPMF α) (fun a => condition a ∧ event a) =
        (eventSet.card : ℝ) / (Fintype.card α : ℝ) := by
    simpa [eventSet] using
      (pmfProb_uniformPMF_finset (α := α) eventSet)
  have hevent_card_real : (eventSet.card : ℝ) ≤ 1 := by
    exact_mod_cast hevent_card
  have hfiber_pos_real : 0 < (fiberCard : ℝ) := by
    exact_mod_cast hfiber_pos
  have hcard_alpha_pos : 0 < (Fintype.card α : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty α›)
  rw [pmfConditionalProb_eq_inter_div_of_pos
    (uniformPMF α) condition event hcondition_pos]
  rw [hevent_prob, hcondition_prob, hcondition_card]
  calc
    ((eventSet.card : ℝ) / (Fintype.card α : ℝ)) /
        ((fiberCard : ℝ) / (Fintype.card α : ℝ)) =
        (eventSet.card : ℝ) / (fiberCard : ℝ) := by
          field_simp [hcard_alpha_pos.ne', hfiber_pos_real.ne']
    _ ≤ 1 / (fiberCard : ℝ) :=
          div_le_div_of_nonneg_right hevent_card_real
            (le_of_lt hfiber_pos_real)
    _ = ((fiberCard : ℝ)⁻¹) := by rw [one_div]

/--
If every fiber of a finite map inside a conditioning event has the same
positive cardinality, then the conditional pushforward of the uniform law is
the uniform law on the codomain, stated as equality of event probabilities.
-/
theorem pmfConditionalProb_uniformPMF_comp_eq_of_constant_conditional_fiber_card
    {α β : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (condition : α → Prop) [DecidablePred condition]
    (f : α → β) (fiberCard : ℕ) (hfiber_pos : 0 < fiberCard)
    (hfiber : ∀ b : β,
      ((Finset.univ : Finset α).filter
        (fun a => condition a ∧ f a = b)).card = fiberCard)
    (p : β → Prop) [DecidablePred p] :
    pmfConditionalProb (uniformPMF α) condition (fun a => p (f a)) =
      pmfProb (uniformPMF β) p := by
  classical
  let sourceEvent : Finset α :=
    (Finset.univ : Finset α).filter fun a => condition a ∧ p (f a)
  let conditionSet : Finset α :=
    (Finset.univ : Finset α).filter fun a => condition a
  let targetEvent : Finset β :=
    (Finset.univ : Finset β).filter fun b => p b
  have hsource_card :
      sourceEvent.card = fiberCard * targetEvent.card := by
    have hmaps : ∀ a ∈ sourceEvent, f a ∈ targetEvent := by
      intro a ha
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2.2⟩
    calc
      sourceEvent.card =
          ∑ b ∈ targetEvent,
            ((sourceEvent.filter fun a => f a = b).card) := by
            exact Finset.card_eq_sum_card_fiberwise hmaps
      _ = ∑ _b ∈ targetEvent, fiberCard := by
            refine Finset.sum_congr rfl ?_
            intro b hb
            have hp : p b := (Finset.mem_filter.mp hb).2
            have hfiber_event :
                sourceEvent.filter (fun a => f a = b) =
                  (Finset.univ : Finset α).filter
                    (fun a => condition a ∧ f a = b) := by
              ext a
              by_cases hfb : f a = b
              · simp [sourceEvent, hfb, hp]
              · simp [sourceEvent, hfb]
            rw [hfiber_event, hfiber b]
      _ = fiberCard * targetEvent.card := by
            rw [Finset.sum_const, nsmul_eq_mul]
            exact Nat.mul_comm targetEvent.card fiberCard
  have hcondition_card :
      conditionSet.card = fiberCard * Fintype.card β := by
    have hmaps : ∀ a ∈ conditionSet, f a ∈ (Finset.univ : Finset β) := by
      intro a _ha
      exact Finset.mem_univ _
    calc
      conditionSet.card =
          ∑ b : β,
            ((conditionSet.filter fun a => f a = b).card) := by
            simpa using
              (Finset.card_eq_sum_card_fiberwise
                (s := conditionSet)
                (t := (Finset.univ : Finset β))
                (f := f) hmaps)
      _ = ∑ _b : β, fiberCard := by
            refine Finset.sum_congr rfl ?_
            intro b _hb
            have hfiber_event :
                conditionSet.filter (fun a => f a = b) =
                  (Finset.univ : Finset α).filter
                    (fun a => condition a ∧ f a = b) := by
              ext a
              simp [conditionSet]
            rw [hfiber_event, hfiber b]
      _ = fiberCard * Fintype.card β := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            exact Nat.mul_comm (Fintype.card β) fiberCard
  have hcondition_card_pos : 0 < conditionSet.card := by
    rw [hcondition_card]
    exact Nat.mul_pos hfiber_pos (Fintype.card_pos_iff.mpr ‹Nonempty β›)
  have hcondition_prob :
      pmfProb (uniformPMF α) condition =
        (conditionSet.card : ℝ) / (Fintype.card α : ℝ) := by
    simpa [conditionSet] using
      (pmfProb_uniformPMF_finset (α := α) conditionSet)
  have hcondition_prob_pos :
      0 < pmfProb (uniformPMF α) condition := by
    rw [hcondition_prob]
    exact div_pos
      (by exact_mod_cast hcondition_card_pos)
      (by exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty α›))
  have hsource_prob :
      pmfProb (uniformPMF α) (fun a => condition a ∧ p (f a)) =
        (sourceEvent.card : ℝ) / (Fintype.card α : ℝ) := by
    simpa [sourceEvent] using
      (pmfProb_uniformPMF_finset (α := α) sourceEvent)
  have htarget_prob :
      pmfProb (uniformPMF β) p =
        (targetEvent.card : ℝ) / (Fintype.card β : ℝ) := by
    simpa [targetEvent] using
      (pmfProb_uniformPMF_finset (α := β) targetEvent)
  rw [pmfConditionalProb_eq_inter_div_of_pos
    (uniformPMF α) condition (fun a => p (f a)) hcondition_prob_pos]
  rw [hsource_prob, hcondition_prob, htarget_prob]
  have hfiber_ne_real : (fiberCard : ℝ) ≠ 0 := by
    exact_mod_cast hfiber_pos.ne'
  have hcard_alpha_ne_real : (Fintype.card α : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty α›).ne'
  have hcard_beta_ne_real : (Fintype.card β : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty β›).ne'
  rw [hsource_card, hcondition_card]
  norm_num [Nat.cast_mul]
  field_simp [hfiber_ne_real, hcard_alpha_ne_real, hcard_beta_ne_real]

/--
If every fiber of a finite map inside a conditioning event has the same
positive cardinality, then the conditional expectation of a function of that
map equals its expectation under the uniform law on the codomain.
-/
theorem pmfConditionalExp_uniformPMF_comp_eq_of_constant_conditional_fiber_card
    {α β : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (condition : α → Prop) [DecidablePred condition]
    (f : α → β) (fiberCard : ℕ) (hfiber_pos : 0 < fiberCard)
    (hfiber : ∀ b : β,
      ((Finset.univ : Finset α).filter
        (fun a => condition a ∧ f a = b)).card = fiberCard)
    (F : β → ℝ) :
    pmfConditionalExp (uniformPMF α) condition (fun a => F (f a)) =
      pmfExp (uniformPMF β) F := by
  classical
  let conditionSet : Finset α :=
    (Finset.univ : Finset α).filter condition
  have hcondition_card :
      conditionSet.card = fiberCard * Fintype.card β := by
    have hmaps : ∀ a ∈ conditionSet, f a ∈ (Finset.univ : Finset β) := by
      intro a _ha
      exact Finset.mem_univ _
    calc
      conditionSet.card =
          ∑ b : β,
            ((conditionSet.filter fun a => f a = b).card) := by
            simpa using
              (Finset.card_eq_sum_card_fiberwise
                (s := conditionSet)
                (t := (Finset.univ : Finset β))
                (f := f) hmaps)
      _ = ∑ _b : β, fiberCard := by
            refine Finset.sum_congr rfl ?_
            intro b _hb
            have hfiber_event :
                conditionSet.filter (fun a => f a = b) =
                  (Finset.univ : Finset α).filter
                    (fun a => condition a ∧ f a = b) := by
              ext a
              simp [conditionSet]
            rw [hfiber_event, hfiber b]
      _ = fiberCard * Fintype.card β := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            exact Nat.mul_comm (Fintype.card β) fiberCard
  have hcondition_card_pos : 0 < conditionSet.card := by
    rw [hcondition_card]
    exact Nat.mul_pos hfiber_pos (Fintype.card_pos_iff.mpr ‹Nonempty β›)
  have hcondition_prob :
      pmfProb (uniformPMF α) condition =
        (conditionSet.card : ℝ) / (Fintype.card α : ℝ) := by
    simpa [conditionSet] using
      (pmfProb_uniformPMF_finset (α := α) conditionSet)
  have hcondition_prob_pos :
      0 < pmfProb (uniformPMF α) condition := by
    rw [hcondition_prob]
    exact div_pos
      (by exact_mod_cast hcondition_card_pos)
      (by exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty α›))
  have hindicator :
      pmfIndicatorExp (uniformPMF α) condition (fun a => F (f a)) =
        (Fintype.card α : ℝ)⁻¹ *
          ∑ b : β, (fiberCard : ℝ) * F b := by
    unfold pmfIndicatorExp pmfExp
    calc
      ∑ a : α, (uniformPMF α a).toReal *
          (if condition a then F (f a) else 0) =
          ∑ a ∈ conditionSet,
            (Fintype.card α : ℝ)⁻¹ * F (f a) := by
            calc
              ∑ a : α, (uniformPMF α a).toReal *
                  (if condition a then F (f a) else 0) =
                  ∑ a : α,
                    if condition a then
                      (Fintype.card α : ℝ)⁻¹ * F (f a)
                    else 0 := by
                    refine Finset.sum_congr rfl ?_
                    intro a _ha
                    rw [uniformPMF_apply_toReal]
                    by_cases ha : condition a <;> simp [ha]
              _ = ∑ a ∈ conditionSet,
                    (Fintype.card α : ℝ)⁻¹ * F (f a) := by
                    simpa [conditionSet] using
                      (Finset.sum_filter (s := (Finset.univ : Finset α))
                        (p := condition)
                        (f := fun a => (Fintype.card α : ℝ)⁻¹ * F (f a))).symm
      _ = ∑ b : β,
          ∑ a ∈ conditionSet with f a = b,
            (Fintype.card α : ℝ)⁻¹ * F (f a) := by
            symm
            simpa using
              (Finset.sum_fiberwise (s := conditionSet) (g := f)
                (f := fun a => (Fintype.card α : ℝ)⁻¹ * F (f a)))
      _ = ∑ b : β,
          (Fintype.card α : ℝ)⁻¹ * ((fiberCard : ℝ) * F b) := by
            refine Finset.sum_congr rfl ?_
            intro b _hb
            have hfiber_event :
                conditionSet.filter (fun a => f a = b) =
                  (Finset.univ : Finset α).filter
                    (fun a => condition a ∧ f a = b) := by
              ext a
              simp [conditionSet]
            calc
              ∑ a ∈ conditionSet with f a = b,
                  (Fintype.card α : ℝ)⁻¹ * F (f a) =
                  ∑ a ∈ conditionSet with f a = b,
                    (Fintype.card α : ℝ)⁻¹ * F b := by
                    refine Finset.sum_congr rfl ?_
                    intro a ha
                    rw [(Finset.mem_filter.mp ha).2]
              _ =
                  ((conditionSet.filter fun a => f a = b).card : ℝ) *
                    ((Fintype.card α : ℝ)⁻¹ * F b) := by
                    simp [nsmul_eq_mul]
              _ = (Fintype.card α : ℝ)⁻¹ * ((fiberCard : ℝ) * F b) := by
                    rw [hfiber_event, hfiber b]
                    ring
      _ = (Fintype.card α : ℝ)⁻¹ *
          ∑ b : β, (fiberCard : ℝ) * F b := by
            rw [Finset.mul_sum]
  rw [pmfConditionalExp_eq_div_of_pos
    (uniformPMF α) condition (fun a => F (f a)) hcondition_prob_pos]
  rw [hindicator, hcondition_prob, hcondition_card]
  unfold pmfExp
  simp only [uniformPMF_apply_toReal]
  have hfiber_ne_real : (fiberCard : ℝ) ≠ 0 := by
    exact_mod_cast hfiber_pos.ne'
  have hcard_alpha_ne_real : (Fintype.card α : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty α›).ne'
  have hcard_beta_ne_real : (Fintype.card β : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty β›).ne'
  norm_num [Nat.cast_mul]
  rw [← Finset.mul_sum]
  field_simp [hfiber_ne_real, hcard_alpha_ne_real, hcard_beta_ne_real]
  have hcancel :
      (Fintype.card β : ℝ) *
          ((∑ i, F i) / (Fintype.card β : ℝ)) =
        ∑ i, F i := by
    field_simp [hcard_beta_ne_real]
  rw [← Finset.sum_div]
  exact hcancel.symm

/-- A nonnegative random variable bounded by `c` has expectation at most its
conditional expectation on a positive event plus `c` times the probability of
the complementary event. -/
theorem pmfExp_le_pmfConditionalExp_add_mul_prob_not
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p]
    (f : α → ℝ) (c : ℝ)
    (hp_pos : 0 < pmfProb μ p)
    (h_nonneg : ∀ a, 0 ≤ f a)
    (h_le : ∀ a, f a ≤ c) :
    pmfExp μ f ≤
      pmfConditionalExp μ p f + c * pmfProb μ (fun a => ¬ p a) := by
  have hsplit :
      pmfExp μ f =
        pmfIndicatorExp μ p f + pmfIndicatorExp μ (fun a => ¬ p a) f := by
    simp only [pmfExp, pmfIndicatorExp]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro a _ha
    by_cases hp : p a <;> simp [hp]
  have hconditional_nonneg : 0 ≤ pmfConditionalExp μ p f :=
    pmfConditionalExp_nonneg_of_nonneg μ p f (fun a _ha => h_nonneg a)
  have hgood_le :
      pmfIndicatorExp μ p f ≤ pmfConditionalExp μ p f := by
    rw [← pmfConditionalExp_mul_prob_eq_indicatorExp_of_pos μ p f hp_pos]
    exact mul_le_of_le_one_right hconditional_nonneg (pmfProb_le_one μ p)
  have hbad_le :
      pmfIndicatorExp μ (fun a => ¬ p a) f ≤
        c * pmfProb μ (fun a => ¬ p a) := by
    calc
      pmfIndicatorExp μ (fun a => ¬ p a) f ≤
          pmfProb μ (fun a => ¬ p a) * c :=
            pmfIndicatorExp_le_prob_mul_of_forall_le μ (fun a => ¬ p a) f
              (fun a _ha => h_le a)
      _ = c * pmfProb μ (fun a => ¬ p a) := by ring
  rw [hsplit]
  exact add_le_add hgood_le hbad_le

/-- Conditional expectations agree when their integrands agree on the
conditioning event. -/
theorem pmfConditionalExp_congr_on
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p]
    {f g : α → ℝ} (h : ∀ a, p a → f a = g a) :
    pmfConditionalExp μ p f = pmfConditionalExp μ p g := by
  by_cases hp_zero : pmfProb μ p = 0
  · simp [pmfConditionalExp, hp_zero]
  · have hp_pos : 0 < pmfProb μ p :=
      lt_of_le_of_ne (pmfProb_nonneg μ p) (by simpa [eq_comm] using hp_zero)
    have hindicator : pmfIndicatorExp μ p f = pmfIndicatorExp μ p g := by
      unfold pmfIndicatorExp
      refine pmfExp_congr μ ?_
      intro a
      by_cases ha : p a
      · simp [ha, h a ha]
      · simp [ha]
    rw [pmfConditionalExp_eq_div_of_pos μ p f hp_pos,
      pmfConditionalExp_eq_div_of_pos μ p g hp_pos, hindicator]

/-- Conditional expectation is monotone when the integrands are ordered on
the conditioning event. -/
theorem pmfConditionalExp_mono_of_forall_le
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p]
    {f g : α → ℝ} (h : ∀ a, p a → f a ≤ g a) :
    pmfConditionalExp μ p f ≤ pmfConditionalExp μ p g := by
  by_cases hp_zero : pmfProb μ p = 0
  · simp [pmfConditionalExp, hp_zero]
  · have hp_pos : 0 < pmfProb μ p :=
      lt_of_le_of_ne (pmfProb_nonneg μ p) (by simpa [eq_comm] using hp_zero)
    rw [pmfConditionalExp_eq_div_of_pos μ p f hp_pos,
      pmfConditionalExp_eq_div_of_pos μ p g hp_pos]
    apply div_le_div_of_nonneg_right _ (le_of_lt hp_pos)
    unfold pmfIndicatorExp
    apply pmfExp_le_pmfExp_of_forall_le
    intro a
    by_cases ha : p a
    · simpa [ha] using h a ha
    · simp [ha]

/--
Conditional expectation is strictly monotone when the integrands are ordered
on the conditioning event and are strictly ordered at one positive-mass atom
of that event.
-/
theorem pmfConditionalExp_lt_of_forall_le_exists_pos_lt
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p]
    {f g : α → ℝ} (hprob : 0 < pmfProb μ p)
    (hle : ∀ a, p a → f a ≤ g a)
    (hexists : ∃ a, p a ∧ 0 < (μ a).toReal ∧ f a < g a) :
    pmfConditionalExp μ p f < pmfConditionalExp μ p g := by
  have hindicator : pmfIndicatorExp μ p f < pmfIndicatorExp μ p g := by
    unfold pmfIndicatorExp
    apply pmfExp_lt_pmfExp_of_forall_le_exists_pos_lt
    · intro a
      by_cases ha : p a
      · simpa [ha] using hle a ha
      · simp [ha]
    · obtain ⟨a, ha, hmass, hstrict⟩ := hexists
      exact ⟨a, hmass, by simpa [ha] using hstrict⟩
  rw [pmfConditionalExp_eq_div_of_pos μ p f hprob,
    pmfConditionalExp_eq_div_of_pos μ p g hprob]
  exact (div_lt_div_iff_of_pos_right hprob).2 hindicator

/--
Conditional finite-loss accounting with an exceptional event.  On any
positive-probability conditioning event, the usual comparison argument is
unchanged: a truthful loss bounded by `K`, which is no worse off the bad event
than a comparison loss bounded below by one, has conditional expectation at
most the displayed exceptional-event factor times the conditional comparison
loss.
-/
theorem pmfConditionalExp_loss_le_one_add_mul_conditionalProb_mul_of_bad
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (condition bad : α → Prop)
    [DecidablePred condition] [DecidablePred bad]
    (truth comparison : α → ℝ) (K : ℝ)
    (hcondition_pos : 0 < pmfProb μ condition)
    (hK : 1 ≤ K)
    (htruth_bound : ∀ a, condition a → truth a ≤ K)
    (hcomparison_lower : ∀ a, condition a → 1 ≤ comparison a)
    (hgood : ∀ a, condition a → ¬ bad a → truth a ≤ comparison a) :
    pmfConditionalExp μ condition truth ≤
      (1 + (K - 1) * pmfConditionalProb μ condition bad) *
        pmfConditionalExp μ condition comparison := by
  classical
  have hpoint : ∀ a, condition a →
      truth a ≤ comparison a + (K - 1) * (if bad a then (1 : ℝ) else 0) := by
    intro a ha
    by_cases hbad : bad a
    · simp [hbad]
      linarith [htruth_bound a ha, hcomparison_lower a ha]
    · simp [hbad]
      exact hgood a ha hbad
  have hindicator :
      pmfIndicatorExp μ condition truth ≤
        pmfIndicatorExp μ condition comparison +
          (K - 1) * pmfProb μ (fun a => condition a ∧ bad a) := by
    calc
      pmfIndicatorExp μ condition truth ≤
          pmfIndicatorExp μ condition
            (fun a => comparison a +
              (K - 1) * (if bad a then (1 : ℝ) else 0)) := by
            unfold pmfIndicatorExp
            apply pmfExp_le_pmfExp_of_forall_le
            intro a
            by_cases hcondition : condition a
            · simpa only [hcondition, if_true, mul_ite] using
                hpoint a hcondition
            · simp [hcondition]
      _ = pmfIndicatorExp μ condition comparison +
          (K - 1) * pmfProb μ (fun a => condition a ∧ bad a) := by
            unfold pmfIndicatorExp pmfProb pmfExp
            calc
              ∑ a : α, (μ a).toReal *
                  (if condition a then
                    comparison a +
                      (K - 1) * (if bad a then (1 : ℝ) else 0)
                  else 0) =
                  ∑ a : α,
                    ((μ a).toReal * (if condition a then comparison a else 0) +
                      (K - 1) * ((μ a).toReal *
                        (if condition a ∧ bad a then (1 : ℝ) else 0))) := by
                    refine Finset.sum_congr rfl ?_
                    intro a _
                    by_cases hcondition : condition a <;>
                      by_cases hbad : bad a <;> simp [hcondition, hbad]; ring
              _ =
                  (∑ a : α,
                    (μ a).toReal * (if condition a then comparison a else 0)) +
                    (K - 1) *
                      ∑ a : α, (μ a).toReal *
                        (if condition a ∧ bad a then (1 : ℝ) else 0) := by
                    rw [Finset.sum_add_distrib, Finset.mul_sum]
  have hbase :
      pmfConditionalExp μ condition truth ≤
        pmfConditionalExp μ condition comparison +
          (K - 1) * pmfConditionalProb μ condition bad := by
    have hdiv := div_le_div_of_nonneg_right hindicator (le_of_lt hcondition_pos)
    rw [pmfConditionalExp_eq_div_of_pos μ condition truth hcondition_pos,
      pmfConditionalExp_eq_div_of_pos μ condition comparison hcondition_pos,
      pmfConditionalProb_eq_inter_div_of_pos μ condition bad hcondition_pos]
    convert hdiv using 1; ring
  have hcomparison_exp : 1 ≤ pmfConditionalExp μ condition comparison := by
    calc
      1 = pmfConditionalExp μ condition (fun _ : α => (1 : ℝ)) :=
        (pmfConditionalExp_const_one_eq_one_of_pos μ condition hcondition_pos).symm
      _ ≤ pmfConditionalExp μ condition comparison :=
        pmfConditionalExp_mono_of_forall_le μ condition
          (fun a ha => hcomparison_lower a ha)
  have hexception_nonneg :
      0 ≤ (K - 1) * pmfConditionalProb μ condition bad := by
    apply mul_nonneg (sub_nonneg.mpr hK)
    unfold pmfConditionalProb
    apply pmfConditionalExp_nonneg_of_nonneg
    intro a _
    by_cases hbad : bad a <;> simp [hbad]
  have hexception_mul :
      (K - 1) * pmfConditionalProb μ condition bad ≤
        ((K - 1) * pmfConditionalProb μ condition bad) *
          pmfConditionalExp μ condition comparison := by
    nlinarith [mul_nonneg hexception_nonneg
      (sub_nonneg.mpr hcomparison_exp)]
  calc
    pmfConditionalExp μ condition truth ≤
        pmfConditionalExp μ condition comparison +
          (K - 1) * pmfConditionalProb μ condition bad := hbase
    _ ≤ pmfConditionalExp μ condition comparison +
          ((K - 1) * pmfConditionalProb μ condition bad) *
            pmfConditionalExp μ condition comparison := by
          linarith
    _ = (1 + (K - 1) * pmfConditionalProb μ condition bad) *
          pmfConditionalExp μ condition comparison := by ring

/-- A random variable taking values in `[0, 1]` has conditional expectation on
a positive event at most its unconditional expectation plus the probability of
the complementary event. -/
theorem pmfConditionalExp_le_pmfExp_add_prob_not_of_forall_le_one
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p]
    (f : α → ℝ) (hp_pos : 0 < pmfProb μ p)
    (h_nonneg : ∀ a, 0 ≤ f a)
    (h_le_one : ∀ a, f a ≤ 1) :
    pmfConditionalExp μ p f ≤ pmfExp μ f + pmfProb μ (fun a => ¬ p a) := by
  have hconditional_le_one : pmfConditionalExp μ p f ≤ 1 :=
    pmfConditionalExp_le_of_forall_le_of_pos μ p f hp_pos
      (fun a _ha => h_le_one a)
  have hindicator_le : pmfIndicatorExp μ p f ≤ pmfExp μ f := by
    unfold pmfIndicatorExp
    refine pmfExp_le_pmfExp_of_forall_le μ _ _ ?_
    intro a
    by_cases ha : p a
    · simp [ha]
    · simpa [ha] using h_nonneg a
  have hgood_le :
      pmfConditionalExp μ p f * pmfProb μ p ≤ pmfExp μ f := by
    rw [pmfConditionalExp_mul_prob_eq_indicatorExp_of_pos μ p f hp_pos]
    exact hindicator_le
  have htail_le :
      pmfConditionalExp μ p f * (1 - pmfProb μ p) ≤
        1 * (1 - pmfProb μ p) := by
    apply mul_le_mul_of_nonneg_right hconditional_le_one
    exact sub_nonneg.mpr (pmfProb_le_one μ p)
  calc
    pmfConditionalExp μ p f =
        pmfConditionalExp μ p f * pmfProb μ p +
          pmfConditionalExp μ p f * (1 - pmfProb μ p) := by ring
    _ ≤ pmfExp μ f + 1 * (1 - pmfProb μ p) :=
          add_le_add hgood_le htail_le
    _ = pmfExp μ f + pmfProb μ (fun a => ¬ p a) := by
          rw [pmfProb_compl]
          ring

/-- A random variable taking values in `[0, 1]` has conditional expectation on
a positive event at most its unconditional expectation plus the complement of
the conditioning probability. -/
theorem pmfConditionalExp_le_pmfExp_add_one_sub_prob_of_forall_le_one
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p]
    (f : α → ℝ) (hp_pos : 0 < pmfProb μ p)
    (h_nonneg : ∀ a, 0 ≤ f a)
    (h_le_one : ∀ a, f a ≤ 1) :
    pmfConditionalExp μ p f ≤ pmfExp μ f + (1 - pmfProb μ p) := by
  simpa only [pmfProb_compl] using
    (pmfConditionalExp_le_pmfExp_add_prob_not_of_forall_le_one
      μ p f hp_pos h_nonneg h_le_one)

/--
Conditional probability is continuous along any filter when the conditioning
event and the joint event converge and the limiting conditioning probability is
positive.
-/
theorem pmfConditionalProb_tendsto_of_inter_tendsto_of_condition_tendsto
    {ι α : Type*} [Fintype α] [DecidableEq α] {l : Filter ι}
    (μSeq : ι → PMF α) (μ : PMF α)
    (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    (hp_pos : 0 < pmfProb μ p)
    (hinter :
      Filter.Tendsto
        (fun i : ι => pmfProb (μSeq i) (fun a => p a ∧ q a))
        l
        (nhds (pmfProb μ (fun a => p a ∧ q a))))
    (hcondition :
      Filter.Tendsto
        (fun i : ι => pmfProb (μSeq i) p)
        l
        (nhds (pmfProb μ p))) :
    Filter.Tendsto
      (fun i : ι => pmfConditionalProb (μSeq i) p q)
      l
      (nhds (pmfConditionalProb μ p q)) := by
  classical
  have hseq_pos :
      ∀ᶠ i in l, 0 < pmfProb (μSeq i) p :=
    hcondition.eventually (eventually_gt_nhds hp_pos)
  have hquot :
      Filter.Tendsto
        (fun i : ι =>
          pmfProb (μSeq i) (fun a => p a ∧ q a) /
            pmfProb (μSeq i) p)
        l
        (nhds
          (pmfProb μ (fun a => p a ∧ q a) / pmfProb μ p)) :=
    hinter.div hcondition hp_pos.ne'
  rw [pmfConditionalProb_eq_inter_div_of_pos μ p q hp_pos]
  exact hquot.congr' <| hseq_pos.mono fun i hi => by
    exact (pmfConditionalProb_eq_inter_div_of_pos (μSeq i) p q hi).symm

/-- If an event holds on every finite PMF atom, its probability is one. -/
theorem pmfProb_eq_one_of_forall
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p]
    (hp : ∀ a, p a) :
    pmfProb μ p = 1 := by
  unfold pmfProb
  simpa [hp] using (pmfExp_const μ (1 : ℝ))

/--
If `q` implies `p`, then the probability of `p ∧ q` is just the probability
of `q`.
-/
theorem pmfProb_inter_eq_right_of_imp
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    (himp : ∀ a, q a → p a) :
    pmfProb μ (fun a => p a ∧ q a) = pmfProb μ q := by
  classical
  unfold pmfProb
  refine pmfExp_congr μ ?_
  intro a
  by_cases hq : q a
  · have hp : p a := himp a hq
    simp [hp, hq]
  · simp [hq]

/-- Conditioning on an event that always holds leaves event probability unchanged. -/
theorem pmfConditionalProb_eq_pmfProb_of_forall_condition
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    (hp : ∀ a, p a) :
    pmfConditionalProb μ p q = pmfProb μ q := by
  classical
  have hp_prob : pmfProb μ p = 1 :=
    pmfProb_eq_one_of_forall μ p hp
  have hp_pos : 0 < pmfProb μ p := by
    rw [hp_prob]
    norm_num
  rw [pmfConditionalProb_eq_inter_div_of_pos μ p q hp_pos]
  rw [pmfProb_inter_eq_right_of_imp μ p q (by intro a _hq; exact hp a)]
  rw [hp_prob]
  ring

/--
For nested events `q ⊆ p`, the probability of `q` is the conditional
probability of `q` given `p`, multiplied by the probability of `p`.
-/
theorem pmfProb_eq_mul_conditionalProb_of_imp
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    (himp : ∀ a, q a → p a)
    (hp_pos : 0 < pmfProb μ p) :
    pmfProb μ q = pmfConditionalProb μ p q * pmfProb μ p := by
  rw [pmfConditionalProb_eq_inter_div_of_pos μ p q hp_pos]
  rw [pmfProb_inter_eq_right_of_imp μ p q himp]
  field_simp [hp_pos.ne']

/--
Conditional probabilities are unchanged when the target events agree on the
conditioning event.
-/
theorem pmfConditionalProb_congr_of_condition
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p q r : α → Prop)
    [DecidablePred p] [DecidablePred q] [DecidablePred r]
    (hqr : ∀ a, p a → (q a ↔ r a)) :
    pmfConditionalProb μ p q = pmfConditionalProb μ p r := by
  classical
  have hind :
      pmfIndicatorExp μ p (fun a => if q a then (1 : ℝ) else 0) =
        pmfIndicatorExp μ p (fun a => if r a then (1 : ℝ) else 0) := by
    unfold pmfIndicatorExp
    refine pmfExp_congr μ ?_
    intro a
    by_cases hp : p a
    · have hiff := hqr a hp
      by_cases hq : q a
      · have hr : r a := hiff.1 hq
        simp [hp, hq, hr]
      · have hr : ¬ r a := fun hr => hq (hiff.2 hr)
        simp [hp, hq, hr]
    · simp [hp]
  unfold pmfConditionalProb pmfConditionalExp
  simp [hind]

/--
Conditional probability is invariant under replacing the conditioning event by
an equivalent event and replacing the target by an event that agrees on that
conditioning event.
-/
theorem pmfConditionalProb_congr
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p p' q q' : α → Prop)
    [DecidablePred p] [DecidablePred p'] [DecidablePred q] [DecidablePred q']
    (hp : ∀ a, p a ↔ p' a)
    (hq : ∀ a, p a → (q a ↔ q' a)) :
    pmfConditionalProb μ p q = pmfConditionalProb μ p' q' := by
  classical
  have hprob : pmfProb μ p = pmfProb μ p' :=
    pmfProb_congr μ hp
  have hind :
      pmfIndicatorExp μ p (fun a => if q a then (1 : ℝ) else 0) =
        pmfIndicatorExp μ p' (fun a => if q' a then (1 : ℝ) else 0) := by
    unfold pmfIndicatorExp
    refine pmfExp_congr μ ?_
    intro a
    by_cases hpa : p a
    · have hp'a : p' a := (hp a).1 hpa
      have hiff := hq a hpa
      by_cases hqa : q a
      · have hq'a : q' a := hiff.1 hqa
        simp [hpa, hp'a, hqa, hq'a]
      · have hq'a : ¬ q' a := fun hq'a => hqa (hiff.2 hq'a)
        simp [hpa, hp'a, hqa, hq'a]
    · have hp'a : ¬ p' a := fun hp'a => hpa ((hp a).2 hp'a)
      simp [hpa, hp'a]
  unfold pmfConditionalProb pmfConditionalExp
  simp [hprob, hind]

/--
Conditional probability is monotone in the target event, relative to the
conditioning event.
-/
theorem pmfConditionalProb_le_of_imp_of_condition
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p q r : α → Prop)
    [DecidablePred p] [DecidablePred q] [DecidablePred r]
    (himp : ∀ a, p a → q a → r a) :
    pmfConditionalProb μ p q ≤ pmfConditionalProb μ p r := by
  classical
  by_cases hp_pos : 0 < pmfProb μ p
  · rw [pmfConditionalProb_eq_inter_div_of_pos μ p q hp_pos]
    rw [pmfConditionalProb_eq_inter_div_of_pos μ p r hp_pos]
    exact div_le_div_of_nonneg_right
      (pmfProb_le_of_imp μ
        (fun a => p a ∧ q a) (fun a => p a ∧ r a)
        (by intro a ha; exact ⟨ha.1, himp a ha.1 ha.2⟩))
      (le_of_lt hp_pos)
  · have hp_zero : pmfProb μ p = 0 := by
      exact le_antisymm (le_of_not_gt hp_pos) (pmfProb_nonneg μ p)
    unfold pmfConditionalProb
    rw [pmfConditionalExp_of_prob_zero μ p
      (fun a => if q a then (1 : ℝ) else 0) hp_zero]
    rw [pmfConditionalExp_of_prob_zero μ p
      (fun a => if r a then (1 : ℝ) else 0) hp_zero]

/-- Conditional probability complement rule on a positive-probability event. -/
theorem pmfConditionalProb_compl_eq_one_sub_of_pos
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    (hp_pos : 0 < pmfProb μ p) :
    pmfConditionalProb μ p (fun a => ¬ q a) =
      1 - pmfConditionalProb μ p q := by
  rw [pmfConditionalProb_eq_inter_div_of_pos μ p (fun a => ¬ q a) hp_pos]
  rw [pmfConditionalProb_eq_inter_div_of_pos μ p q hp_pos]
  have hsplit := pmfProb_eq_inter_add_inter_not μ p q
  have hdiff :
      pmfProb μ (fun a => p a ∧ ¬ q a) =
        pmfProb μ p - pmfProb μ (fun a => p a ∧ q a) := by
    linarith
  rw [hdiff]
  field_simp [hp_pos.ne']

/--
Finite conditional-probability chain rule:
`Pr[q and r | p] = Pr[r | p and q] * Pr[q | p]`, when both conditioning
events have positive probability.
-/
theorem pmfConditionalProb_inter_eq_mul_conditionalProb_of_pos
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p q r : α → Prop)
    [DecidablePred p] [DecidablePred q] [DecidablePred r]
    (hp_pos : 0 < pmfProb μ p)
    (hpq_pos : 0 < pmfProb μ (fun a => p a ∧ q a)) :
    pmfConditionalProb μ p (fun a => q a ∧ r a) =
      pmfConditionalProb μ (fun a => p a ∧ q a) r *
        pmfConditionalProb μ p q := by
  classical
  rw [pmfConditionalProb_eq_inter_div_of_pos
    μ p (fun a => q a ∧ r a) hp_pos]
  rw [pmfConditionalProb_eq_inter_div_of_pos
    μ (fun a => p a ∧ q a) r hpq_pos]
  rw [pmfConditionalProb_eq_inter_div_of_pos μ p q hp_pos]
  have hnum :
      pmfProb μ (fun a => p a ∧ (q a ∧ r a)) =
        pmfProb μ (fun a => (p a ∧ q a) ∧ r a) := by
    exact pmfProb_congr μ (by intro a; tauto)
  rw [hnum]
  field_simp [hp_pos.ne', hpq_pos.ne']

/--
Conditional expectation of a two-valued random variable on a positive
conditioning event.
-/
theorem pmfConditionalExp_eq_conditionalProb_mul_add_one_sub_mul_of_forall_eq_if
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    (f : α → ℝ) (x y : ℝ)
    (hp_pos : 0 < pmfProb μ p)
    (hpoint : ∀ a, p a → f a = if q a then x else y) :
    pmfConditionalExp μ p f =
      pmfConditionalProb μ p q * x +
        (1 - pmfConditionalProb μ p q) * y := by
  classical
  have hindicator :
      pmfIndicatorExp μ p f =
        pmfProb μ (fun a => p a ∧ q a) * x +
          pmfProb μ (fun a => p a ∧ ¬ q a) * y := by
    unfold pmfIndicatorExp pmfProb pmfExp
    calc
      ∑ a : α, (μ a).toReal * (if p a then f a else 0)
          =
        ∑ a : α, (
          ((μ a).toReal * (if p a ∧ q a then (1 : ℝ) else 0)) * x +
            ((μ a).toReal * (if p a ∧ ¬ q a then (1 : ℝ) else 0)) * y) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          by_cases hp : p a
          · rw [hpoint a hp]
            by_cases hq : q a <;> simp [hp, hq]
          · simp [hp]
      _ =
        (∑ a : α,
          ((μ a).toReal * (if p a ∧ q a then (1 : ℝ) else 0)) * x) +
          ∑ a : α,
            ((μ a).toReal * (if p a ∧ ¬ q a then (1 : ℝ) else 0)) * y := by
          rw [Finset.sum_add_distrib]
      _ =
        (∑ a : α, (μ a).toReal * (if p a ∧ q a then (1 : ℝ) else 0)) * x +
          (∑ a : α, (μ a).toReal * (if p a ∧ ¬ q a then (1 : ℝ) else 0)) * y := by
          rw [Finset.sum_mul, Finset.sum_mul]
  rw [pmfConditionalExp_eq_div_of_pos μ p f hp_pos]
  rw [hindicator]
  rw [pmfConditionalProb_eq_inter_div_of_pos μ p q hp_pos]
  have hsplit := pmfProb_eq_inter_add_inter_not μ p q
  have hdiff :
      pmfProb μ (fun a => p a ∧ ¬ q a) =
        pmfProb μ p - pmfProb μ (fun a => p a ∧ q a) := by
    linarith
  rw [hdiff]
  field_simp [hp_pos.ne']

/--
If the conditional probability of `q` given `p` is at most `eps`, then the
conditional probability of its complement is at least `1 - eps`.
-/
theorem one_sub_le_pmfConditionalProb_compl_of_conditionalProb_le
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    {eps : ℝ}
    (hp_pos : 0 < pmfProb μ p)
    (hprob : pmfConditionalProb μ p q ≤ eps) :
    1 - eps ≤ pmfConditionalProb μ p (fun a => ¬ q a) := by
  rw [pmfConditionalProb_compl_eq_one_sub_of_pos μ p q hp_pos]
  linarith

/--
Finite product lower bound for a nested sequence of events.  If `event 0`
always holds and every conditional transition `event r -> event (r+1)` has
probability at least `base`, then `event k` has probability at least
`base ^ k`.
-/
theorem pmfProb_ge_pow_of_nested_conditionalProb_ge
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (μ : PMF Ω) (event : ℕ → Ω → Prop)
    [∀ r, DecidablePred fun ω => event r ω]
    (k : ℕ) {base : ℝ}
    (hbase_nonneg : 0 ≤ base)
    (hzero : ∀ ω, event 0 ω)
    (hnested : ∀ r, r < k → ∀ ω, event (r + 1) ω → event r ω)
    (hcond : ∀ r, r < k →
      base ≤ pmfConditionalProb μ
        (fun ω => event r ω) (fun ω => event (r + 1) ω)) :
    base ^ k ≤ pmfProb μ (fun ω => event k ω) := by
  classical
  induction k with
  | zero =>
      have hprob0 : pmfProb μ (fun ω => event 0 ω) = 1 :=
        pmfProb_eq_one_of_forall μ (fun ω => event 0 ω) hzero
      simp [hprob0]
  | succ k ih =>
      by_cases hbase_zero : base = 0
      · subst base
        simp [pmfProb_nonneg]
      · have hbase_pos : 0 < base :=
          lt_of_le_of_ne hbase_nonneg (Ne.symm hbase_zero)
        have hprev :
            base ^ k ≤ pmfProb μ (fun ω => event k ω) :=
          ih
            (by
              intro r hr
              exact hnested r (Nat.lt_trans hr (Nat.lt_succ_self k)))
            (by
              intro r hr
              exact hcond r (Nat.lt_trans hr (Nat.lt_succ_self k)))
        have hprev_pos : 0 < pmfProb μ (fun ω => event k ω) :=
          lt_of_lt_of_le (pow_pos hbase_pos k) hprev
        have hstep :
            base ≤ pmfConditionalProb μ
              (fun ω => event k ω) (fun ω => event (k + 1) ω) :=
          hcond k (Nat.lt_succ_self k)
        have hstep_nonneg :
            0 ≤ pmfConditionalProb μ
              (fun ω => event k ω) (fun ω => event (k + 1) ω) :=
          le_trans hbase_nonneg hstep
        have hpow_nonneg : 0 ≤ base ^ k := pow_nonneg hbase_nonneg k
        have hmul :
            base * base ^ k ≤
              pmfConditionalProb μ
                (fun ω => event k ω) (fun ω => event (k + 1) ω) *
                pmfProb μ (fun ω => event k ω) :=
          mul_le_mul hstep hprev hpow_nonneg hstep_nonneg
        have hprod :
            pmfProb μ (fun ω => event (k + 1) ω) =
              pmfConditionalProb μ
                (fun ω => event k ω) (fun ω => event (k + 1) ω) *
                pmfProb μ (fun ω => event k ω) :=
          pmfProb_eq_mul_conditionalProb_of_imp μ
            (fun ω => event k ω) (fun ω => event (k + 1) ω)
            (hnested k (Nat.lt_succ_self k)) hprev_pos
        calc
          base ^ (k + 1) = base * base ^ k := by
            rw [pow_succ]
            ring
          _ ≤ pmfConditionalProb μ
                (fun ω => event k ω) (fun ω => event (k + 1) ω) *
                pmfProb μ (fun ω => event k ω) := hmul
          _ = pmfProb μ (fun ω => event (k + 1) ω) := hprod.symm

/-- Conditional probabilities are nonnegative. -/
theorem pmfConditionalProb_nonneg
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p q : α → Prop) [DecidablePred p] [DecidablePred q] :
    0 ≤ pmfConditionalProb μ p q := by
  exact
    pmfConditionalExp_nonneg_of_nonneg μ p
      (fun a => if q a then (1 : ℝ) else 0)
      (by intro a _hp; by_cases hq : q a <;> simp [hq])

/--
Finite product upper bound for a nested sequence of events.  If `event 0`
always holds and every conditional transition `event r -> event (r+1)` has
probability at most `base`, then `event k` has probability at most
`base ^ k`.
-/
theorem pmfProb_le_pow_of_nested_conditionalProb_le
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (μ : PMF Ω) (event : ℕ → Ω → Prop)
    [∀ r, DecidablePred fun ω => event r ω]
    (k : ℕ) {base : ℝ}
    (hbase_nonneg : 0 ≤ base)
    (hzero : ∀ ω, event 0 ω)
    (hnested : ∀ r, r < k → ∀ ω, event (r + 1) ω → event r ω)
    (hcond : ∀ r, r < k →
      pmfConditionalProb μ
        (fun ω => event r ω) (fun ω => event (r + 1) ω) ≤ base) :
    pmfProb μ (fun ω => event k ω) ≤ base ^ k := by
  classical
  induction k with
  | zero =>
      have hprob0 : pmfProb μ (fun ω => event 0 ω) = 1 :=
        pmfProb_eq_one_of_forall μ (fun ω => event 0 ω) hzero
      simp [hprob0]
  | succ k ih =>
      have hprev_le :
          pmfProb μ (fun ω => event k ω) ≤ base ^ k :=
        ih
          (by
            intro r hr
            exact hnested r (Nat.lt_trans hr (Nat.lt_succ_self k)))
          (by
            intro r hr
            exact hcond r (Nat.lt_trans hr (Nat.lt_succ_self k)))
      by_cases hprev_zero : pmfProb μ (fun ω => event k ω) = 0
      · have hle_zero :
            pmfProb μ (fun ω => event (k + 1) ω) ≤ 0 := by
          have hsubset :
              pmfProb μ (fun ω => event (k + 1) ω) ≤
                pmfProb μ (fun ω => event k ω) :=
            pmfProb_le_of_imp μ
              (fun ω => event (k + 1) ω) (fun ω => event k ω)
              (hnested k (Nat.lt_succ_self k))
          simpa [hprev_zero] using hsubset
        exact le_trans hle_zero (pow_nonneg hbase_nonneg (k + 1))
      · have hprev_pos : 0 < pmfProb μ (fun ω => event k ω) :=
          lt_of_le_of_ne (pmfProb_nonneg μ (fun ω => event k ω))
            (by simpa [eq_comm] using hprev_zero)
        have hstep :
            pmfConditionalProb μ
              (fun ω => event k ω) (fun ω => event (k + 1) ω) ≤ base :=
          hcond k (Nat.lt_succ_self k)
        have hmul :
            pmfConditionalProb μ
                (fun ω => event k ω) (fun ω => event (k + 1) ω) *
                pmfProb μ (fun ω => event k ω) ≤
              base * base ^ k :=
          mul_le_mul hstep hprev_le
            (pmfProb_nonneg μ (fun ω => event k ω)) hbase_nonneg
        have hprod :
            pmfProb μ (fun ω => event (k + 1) ω) =
              pmfConditionalProb μ
                (fun ω => event k ω) (fun ω => event (k + 1) ω) *
                pmfProb μ (fun ω => event k ω) :=
          pmfProb_eq_mul_conditionalProb_of_imp μ
            (fun ω => event k ω) (fun ω => event (k + 1) ω)
            (hnested k (Nat.lt_succ_self k)) hprev_pos
        calc
          pmfProb μ (fun ω => event (k + 1) ω)
              = pmfConditionalProb μ
                  (fun ω => event k ω) (fun ω => event (k + 1) ω) *
                  pmfProb μ (fun ω => event k ω) := hprod
          _ ≤ base * base ^ k := hmul
          _ = base ^ (k + 1) := by
            rw [pow_succ]
            ring

/-- Split a finite PMF event according to a finite state map. -/
theorem pmfProb_eq_sum_state_inter
    {Ω σ : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype σ] [DecidableEq σ]
    (μ : PMF Ω) (p : Ω → Prop) [DecidablePred p] (state : Ω → σ) :
    pmfProb μ p =
      ∑ s : σ, pmfProb μ (fun ω => p ω ∧ state ω = s) := by
  classical
  unfold pmfProb pmfExp
  calc
    ∑ ω : Ω, (μ ω).toReal * (if p ω then (1 : ℝ) else 0)
        = ∑ ω : Ω, ∑ s : σ,
            (μ ω).toReal *
              (if p ω ∧ state ω = s then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro ω _
          by_cases hp : p ω
          · simp [hp, eq_comm]
          · simp [hp]
    _ = ∑ s : σ, ∑ ω : Ω,
          (μ ω).toReal *
            (if p ω ∧ state ω = s then (1 : ℝ) else 0) := by
          rw [Finset.sum_comm]

/--
Finite law of total probability over the fibers of a state map, written as an
expectation of statewise conditional probabilities.  Zero-probability fibers
contribute zero mass, so no support restriction is needed.
-/
theorem pmfProb_eq_pmfExp_state_conditionalProb
    {Ω σ : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype σ] [DecidableEq σ]
    (μ : PMF Ω) (q : Ω → Prop) [DecidablePred q] (state : Ω → σ) :
    pmfProb μ q =
      pmfExp μ
        (fun ω => pmfConditionalProb μ (fun ω' => state ω' = state ω) q) := by
  classical
  let c : σ → ℝ := fun s =>
    pmfConditionalProb μ (fun ω => state ω = s) q
  have hfiber : ∀ s : σ,
      pmfProb μ (fun ω => q ω ∧ state ω = s) =
        c s * pmfProb μ (fun ω => state ω = s) := by
    intro s
    by_cases hpos : 0 < pmfProb μ (fun ω => state ω = s)
    · have hc :=
        pmfConditionalProb_eq_inter_div_of_pos
          μ (fun ω => state ω = s) q hpos
      have hcomm :
          pmfProb μ (fun ω => q ω ∧ state ω = s) =
            pmfProb μ (fun ω => state ω = s ∧ q ω) := by
        exact pmfProb_congr μ (by
          intro ω
          constructor
          · intro hω
            exact ⟨hω.2, hω.1⟩
          · intro hω
            exact ⟨hω.2, hω.1⟩)
      rw [hcomm]
      dsimp [c]
      rw [hc]
      field_simp [hpos.ne']
    · have hzero : pmfProb μ (fun ω => state ω = s) = 0 := by
        exact le_antisymm (le_of_not_gt hpos)
          (pmfProb_nonneg μ (fun ω => state ω = s))
      have hleft_zero :
          pmfProb μ (fun ω => q ω ∧ state ω = s) = 0 := by
        have hle :
            pmfProb μ (fun ω => q ω ∧ state ω = s) ≤
              pmfProb μ (fun ω => state ω = s) :=
          pmfProb_le_of_imp μ
            (fun ω => q ω ∧ state ω = s)
            (fun ω => state ω = s)
            (by intro ω hω; exact hω.2)
        exact le_antisymm (by simpa [hzero] using hle)
          (pmfProb_nonneg μ (fun ω => q ω ∧ state ω = s))
      rw [hleft_zero, hzero]
      ring
  calc
    pmfProb μ q =
        ∑ s : σ, pmfProb μ (fun ω => q ω ∧ state ω = s) := by
          rw [pmfProb_eq_sum_state_inter μ q state]
    _ = ∑ s : σ, c s * pmfProb μ (fun ω => state ω = s) := by
          refine Finset.sum_congr rfl ?_
          intro s _
          exact hfiber s
    _ = ∑ s : σ, (pmfProb μ (fun ω => state ω = s)) * c s := by
          refine Finset.sum_congr rfl ?_
          intro s _
          ring
    _ = pmfExp (μ.map state) c := by
          unfold pmfExp
          refine Finset.sum_congr rfl ?_
          intro s _
          rw [pmf_map_apply_toReal_eq_pmfProb_preimage]
    _ = pmfExp μ (fun ω => c (state ω)) := by
          rw [pmfExp_map]

/--
Statewise conditional-probability bounds integrate to an unconditional
expectation bound.  Zero-probability fibers contribute zero by the convention
in `pmfConditionalProb`, so only positive fibers require a hypothesis.
-/
theorem pmfProb_le_pmfExp_state_conditionalProb_bound
    {Ω σ : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype σ] [DecidableEq σ]
    (μ : PMF Ω) (q : Ω → Prop) [DecidablePred q]
    (state : Ω → σ) (bound : σ → ℝ)
    (hbound_nonneg : ∀ s : σ, 0 ≤ bound s)
    (hstate_bound : ∀ s : σ,
      0 < pmfProb μ (fun ω => state ω = s) →
        pmfConditionalProb μ (fun ω => state ω = s) q ≤ bound s) :
    pmfProb μ q ≤ pmfExp μ (fun ω => bound (state ω)) := by
  classical
  rw [pmfProb_eq_pmfExp_state_conditionalProb μ q state]
  apply pmfExp_le_pmfExp_of_forall_le
  intro ω
  by_cases hpos : 0 < pmfProb μ (fun ω' => state ω' = state ω)
  · exact hstate_bound (state ω) hpos
  · have hzero : pmfProb μ (fun ω' => state ω' = state ω) = 0 := by
      exact le_antisymm (le_of_not_gt hpos)
        (pmfProb_nonneg μ (fun ω' => state ω' = state ω))
    have hconditional_zero :
        pmfConditionalProb μ (fun ω' => state ω' = state ω) q = 0 := by
      simp [pmfConditionalProb, pmfConditionalExp, hzero]
    rw [hconditional_zero]
    exact hbound_nonneg (state ω)

/-- A statewise conditional domination remains valid after restricting both
events by an arbitrary gate.  This is the finite-PMF bookkeeping principle for
finite first-hit decompositions: the gate can encode that no earlier relevant
event has occurred. -/
theorem pmfProb_inter_le_mul_inter_of_state_conditionalProb_le
    {Ω σ : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype σ] [DecidableEq σ]
    (μ : PMF Ω) (gate target candidate : Ω → Prop)
    [DecidablePred gate] [DecidablePred target] [DecidablePred candidate]
    (state : Ω → σ) (c : ℝ) (hc_nonneg : 0 ≤ c)
    (hstate : ∀ s : σ,
      0 < pmfProb μ (fun ω => gate ω ∧ state ω = s) →
        pmfConditionalProb μ (fun ω => gate ω ∧ state ω = s) target ≤
          c * pmfConditionalProb μ
            (fun ω => gate ω ∧ state ω = s) candidate) :
    pmfProb μ (fun ω => gate ω ∧ target ω) ≤
      c * pmfProb μ (fun ω => gate ω ∧ candidate ω) := by
  classical
  have hpiece : ∀ s : σ,
      pmfProb μ (fun ω => (gate ω ∧ state ω = s) ∧ target ω) ≤
        c * pmfProb μ (fun ω => (gate ω ∧ state ω = s) ∧ candidate ω) := by
    intro s
    by_cases hpos : 0 < pmfProb μ (fun ω => gate ω ∧ state ω = s)
    · have hs := hstate s hpos
      rw [pmfConditionalProb_eq_inter_div_of_pos
        μ (fun ω => gate ω ∧ state ω = s) target hpos] at hs
      rw [pmfConditionalProb_eq_inter_div_of_pos
        μ (fun ω => gate ω ∧ state ω = s) candidate hpos] at hs
      calc
        pmfProb μ (fun ω => (gate ω ∧ state ω = s) ∧ target ω) =
            (pmfProb μ (fun ω => (gate ω ∧ state ω = s) ∧ target ω) /
              pmfProb μ (fun ω => gate ω ∧ state ω = s)) *
              pmfProb μ (fun ω => gate ω ∧ state ω = s) := by
                field_simp [hpos.ne']
        _ ≤ (c *
              (pmfProb μ (fun ω => (gate ω ∧ state ω = s) ∧ candidate ω) /
                pmfProb μ (fun ω => gate ω ∧ state ω = s))) *
              pmfProb μ (fun ω => gate ω ∧ state ω = s) := by
                exact mul_le_mul_of_nonneg_right hs (le_of_lt hpos)
        _ = c * pmfProb μ
            (fun ω => (gate ω ∧ state ω = s) ∧ candidate ω) := by
              field_simp [hpos.ne']
    · have hzero : pmfProb μ (fun ω => gate ω ∧ state ω = s) = 0 := by
        exact le_antisymm (le_of_not_gt hpos)
          (pmfProb_nonneg μ (fun ω => gate ω ∧ state ω = s))
      have hleft_zero :
          pmfProb μ (fun ω => (gate ω ∧ state ω = s) ∧ target ω) = 0 := by
        apply le_antisymm
        · simpa [hzero] using
            (pmfProb_le_of_imp μ
              (fun ω => (gate ω ∧ state ω = s) ∧ target ω)
              (fun ω => gate ω ∧ state ω = s)
              (by
                intro ω hω
                exact hω.1))
        · exact pmfProb_nonneg μ _
      rw [hleft_zero]
      exact mul_nonneg hc_nonneg
        (pmfProb_nonneg μ (fun ω => (gate ω ∧ state ω = s) ∧ candidate ω))
  have htarget_sum :
      pmfProb μ (fun ω => gate ω ∧ target ω) =
        ∑ s : σ, pmfProb μ
          (fun ω => (gate ω ∧ state ω = s) ∧ target ω) := by
    rw [pmfProb_eq_sum_state_inter μ (fun ω => gate ω ∧ target ω) state]
    refine Finset.sum_congr rfl ?_
    intro s _
    apply pmfProb_congr
    intro ω
    tauto
  have hcandidate_sum :
      pmfProb μ (fun ω => gate ω ∧ candidate ω) =
        ∑ s : σ, pmfProb μ
          (fun ω => (gate ω ∧ state ω = s) ∧ candidate ω) := by
    rw [pmfProb_eq_sum_state_inter μ (fun ω => gate ω ∧ candidate ω) state]
    refine Finset.sum_congr rfl ?_
    intro s _
    apply pmfProb_congr
    intro ω
    tauto
  rw [htarget_sum, hcandidate_sum, Finset.mul_sum]
  exact Finset.sum_le_sum fun s _ => hpiece s

/--
Conditional-mixture upper bound.  If a finite state map refines a conditioning
event and the conditional probability of `q` is at most `c` on every positive
refined state, then the coarser conditional probability is also at most `c`.
-/
theorem pmfConditionalProb_le_of_state_refinement
    {Ω σ : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype σ] [DecidableEq σ]
    (μ : PMF Ω) (p q : Ω → Prop) [DecidablePred p] [DecidablePred q]
    (state : Ω → σ) {c : ℝ}
    (hp_pos : 0 < pmfProb μ p)
    (hstate : ∀ s : σ,
      0 < pmfProb μ (fun ω => p ω ∧ state ω = s) →
        pmfConditionalProb μ (fun ω => p ω ∧ state ω = s) q ≤ c) :
    pmfConditionalProb μ p q ≤ c := by
  classical
  have hstate_bound : ∀ s : σ,
      pmfProb μ (fun ω => (p ω ∧ state ω = s) ∧ q ω) ≤
        c * pmfProb μ (fun ω => p ω ∧ state ω = s) := by
    intro s
    by_cases hpos : 0 < pmfProb μ (fun ω => p ω ∧ state ω = s)
    · have h := hstate s hpos
      rw [pmfConditionalProb_eq_inter_div_of_pos
        μ (fun ω => p ω ∧ state ω = s) q hpos] at h
      rwa [div_le_iff₀ hpos] at h
    · have hstate_zero :
          pmfProb μ (fun ω => p ω ∧ state ω = s) = 0 := by
        exact le_antisymm (le_of_not_gt hpos)
          (pmfProb_nonneg μ (fun ω => p ω ∧ state ω = s))
      have hleft_zero :
          pmfProb μ (fun ω => (p ω ∧ state ω = s) ∧ q ω) = 0 := by
        have hle :
            pmfProb μ (fun ω => (p ω ∧ state ω = s) ∧ q ω) ≤
              pmfProb μ (fun ω => p ω ∧ state ω = s) :=
          pmfProb_le_of_imp μ
            (fun ω => (p ω ∧ state ω = s) ∧ q ω)
            (fun ω => p ω ∧ state ω = s)
            (by intro ω hω; exact hω.1)
        exact le_antisymm (by simpa [hstate_zero] using hle)
          (pmfProb_nonneg μ (fun ω => (p ω ∧ state ω = s) ∧ q ω))
      rw [hleft_zero, hstate_zero]
      simp
  have hinter_bound :
      pmfProb μ (fun ω => p ω ∧ q ω) ≤ c * pmfProb μ p := by
    calc
      pmfProb μ (fun ω => p ω ∧ q ω)
          = ∑ s : σ,
              pmfProb μ (fun ω => (p ω ∧ q ω) ∧ state ω = s) := by
            rw [pmfProb_eq_sum_state_inter μ (fun ω => p ω ∧ q ω) state]
      _ ≤ ∑ s : σ,
            c * pmfProb μ (fun ω => p ω ∧ state ω = s) := by
            refine Finset.sum_le_sum ?_
            intro s _
            simpa [and_assoc, and_left_comm, and_comm] using hstate_bound s
      _ = c * ∑ s : σ,
            pmfProb μ (fun ω => p ω ∧ state ω = s) := by
            rw [Finset.mul_sum]
      _ = c * pmfProb μ p := by
            rw [← pmfProb_eq_sum_state_inter μ p state]
  rw [pmfConditionalProb_eq_inter_div_of_pos μ p q hp_pos]
  rwa [div_le_iff₀ hp_pos]

/--
Conditional-mixture lower bound.  If a finite state map refines a conditioning
event and the conditional probability of `q` is at least `c` on every positive
refined state, then the coarser conditional probability is also at least `c`.
-/
theorem pmfConditionalProb_ge_of_state_refinement
    {Ω σ : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype σ] [DecidableEq σ]
    (μ : PMF Ω) (p q : Ω → Prop) [DecidablePred p] [DecidablePred q]
    (state : Ω → σ) {c : ℝ}
    (hp_pos : 0 < pmfProb μ p)
    (hstate : ∀ s : σ,
      0 < pmfProb μ (fun ω => p ω ∧ state ω = s) →
        c ≤ pmfConditionalProb μ (fun ω => p ω ∧ state ω = s) q) :
    c ≤ pmfConditionalProb μ p q := by
  classical
  have hstate_bound : ∀ s : σ,
      c * pmfProb μ (fun ω => p ω ∧ state ω = s) ≤
        pmfProb μ (fun ω => (p ω ∧ state ω = s) ∧ q ω) := by
    intro s
    by_cases hpos : 0 < pmfProb μ (fun ω => p ω ∧ state ω = s)
    · have h := hstate s hpos
      rw [pmfConditionalProb_eq_inter_div_of_pos
        μ (fun ω => p ω ∧ state ω = s) q hpos] at h
      rwa [le_div_iff₀ hpos] at h
    · have hstate_zero :
          pmfProb μ (fun ω => p ω ∧ state ω = s) = 0 := by
        exact le_antisymm (le_of_not_gt hpos)
          (pmfProb_nonneg μ (fun ω => p ω ∧ state ω = s))
      rw [hstate_zero]
      simpa using
        pmfProb_nonneg μ (fun ω => (p ω ∧ state ω = s) ∧ q ω)
  have hinter_bound :
      c * pmfProb μ p ≤ pmfProb μ (fun ω => p ω ∧ q ω) := by
    calc
      c * pmfProb μ p
          = c * ∑ s : σ,
              pmfProb μ (fun ω => p ω ∧ state ω = s) := by
            rw [← pmfProb_eq_sum_state_inter μ p state]
      _ = ∑ s : σ,
            c * pmfProb μ (fun ω => p ω ∧ state ω = s) := by
            rw [Finset.mul_sum]
      _ ≤ ∑ s : σ,
            pmfProb μ (fun ω => (p ω ∧ state ω = s) ∧ q ω) := by
            refine Finset.sum_le_sum ?_
            intro s _
            exact hstate_bound s
      _ = pmfProb μ (fun ω => p ω ∧ q ω) := by
            rw [pmfProb_eq_sum_state_inter μ (fun ω => p ω ∧ q ω) state]
            refine Finset.sum_congr rfl ?_
            intro s _
            apply pmfProb_congr
            intro ω
            simp [and_assoc, and_left_comm, and_comm]
  rw [pmfConditionalProb_eq_inter_div_of_pos μ p q hp_pos]
  rwa [le_div_iff₀ hp_pos]

/--
Conditional-mixture upper bound without a separate positive-probability
hypothesis for the coarse conditioning event.  When that event has zero
probability, the conditional probability is the default value `0`.
-/
theorem pmfConditionalProb_le_of_state_refinement_or_zero
    {Ω σ : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype σ] [DecidableEq σ]
    (μ : PMF Ω) (p q : Ω → Prop) [DecidablePred p] [DecidablePred q]
    (state : Ω → σ) {c : ℝ}
    (hc_nonneg : 0 ≤ c)
    (hstate : ∀ s : σ,
      0 < pmfProb μ (fun ω => p ω ∧ state ω = s) →
        pmfConditionalProb μ (fun ω => p ω ∧ state ω = s) q ≤ c) :
    pmfConditionalProb μ p q ≤ c := by
  classical
  by_cases hp_pos : 0 < pmfProb μ p
  · exact
      pmfConditionalProb_le_of_state_refinement
        μ p q state hp_pos hstate
  · have hp_zero : pmfProb μ p = 0 := by
      exact le_antisymm (le_of_not_gt hp_pos) (pmfProb_nonneg μ p)
    unfold pmfConditionalProb
    rw [pmfConditionalExp_of_prob_zero μ p
      (fun a => if q a then (1 : ℝ) else 0) hp_zero]
    exact hc_nonneg

/--
Conditional-mixture equality.  If a finite state map refines a conditioning
event and every positive refined state has the same conditional probability of
`q`, then the coarser conditional probability also has that value.
-/
theorem pmfConditionalProb_eq_of_state_refinement
    {Ω σ : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype σ] [DecidableEq σ]
    (μ : PMF Ω) (p q : Ω → Prop) [DecidablePred p] [DecidablePred q]
    (state : Ω → σ) {c : ℝ}
    (hp_pos : 0 < pmfProb μ p)
    (hstate : ∀ s : σ,
      0 < pmfProb μ (fun ω => p ω ∧ state ω = s) →
        pmfConditionalProb μ (fun ω => p ω ∧ state ω = s) q = c) :
    pmfConditionalProb μ p q = c := by
  classical
  have hstate_eq : ∀ s : σ,
      pmfProb μ (fun ω => (p ω ∧ state ω = s) ∧ q ω) =
        c * pmfProb μ (fun ω => p ω ∧ state ω = s) := by
    intro s
    by_cases hpos : 0 < pmfProb μ (fun ω => p ω ∧ state ω = s)
    · have h := hstate s hpos
      rw [pmfConditionalProb_eq_inter_div_of_pos
        μ (fun ω => p ω ∧ state ω = s) q hpos] at h
      rw [← h]
      field_simp [hpos.ne']
    · have hstate_zero :
          pmfProb μ (fun ω => p ω ∧ state ω = s) = 0 := by
        exact le_antisymm (le_of_not_gt hpos)
          (pmfProb_nonneg μ (fun ω => p ω ∧ state ω = s))
      have hleft_zero :
          pmfProb μ (fun ω => (p ω ∧ state ω = s) ∧ q ω) = 0 := by
        have hle :
            pmfProb μ (fun ω => (p ω ∧ state ω = s) ∧ q ω) ≤
              pmfProb μ (fun ω => p ω ∧ state ω = s) :=
          pmfProb_le_of_imp μ
            (fun ω => (p ω ∧ state ω = s) ∧ q ω)
            (fun ω => p ω ∧ state ω = s)
            (by intro ω hω; exact hω.1)
        exact le_antisymm (by simpa [hstate_zero] using hle)
          (pmfProb_nonneg μ (fun ω => (p ω ∧ state ω = s) ∧ q ω))
      rw [hleft_zero, hstate_zero]
      ring
  have hinter_eq :
      pmfProb μ (fun ω => p ω ∧ q ω) = c * pmfProb μ p := by
    calc
      pmfProb μ (fun ω => p ω ∧ q ω)
          = ∑ s : σ,
              pmfProb μ (fun ω => (p ω ∧ q ω) ∧ state ω = s) := by
            rw [pmfProb_eq_sum_state_inter μ (fun ω => p ω ∧ q ω) state]
      _ = ∑ s : σ,
            c * pmfProb μ (fun ω => p ω ∧ state ω = s) := by
            refine Finset.sum_congr rfl ?_
            intro s _
            simpa [and_assoc, and_left_comm, and_comm] using hstate_eq s
      _ = c * ∑ s : σ,
            pmfProb μ (fun ω => p ω ∧ state ω = s) := by
            rw [Finset.mul_sum]
      _ = c * pmfProb μ p := by
            rw [← pmfProb_eq_sum_state_inter μ p state]
  rw [pmfConditionalProb_eq_inter_div_of_pos μ p q hp_pos]
  rw [hinter_eq]
  field_simp [hp_pos.ne']

/--
If the conditional distribution of a finite state map is a PMF `ρ`, then every
event determined by that state has conditional probability equal to its
probability under `ρ`.
-/
theorem pmfConditionalProb_state_event_eq_pmfProb_of_conditional_atom_eq
    {Ω σ : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype σ] [DecidableEq σ]
    (μ : PMF Ω) (p : Ω → Prop) [DecidablePred p]
    (state : Ω → σ) (ρ : PMF σ)
    (target : σ → Prop) [DecidablePred target]
    (hp_pos : 0 < pmfProb μ p)
    (hstate : ∀ s : σ,
      pmfConditionalProb μ p (fun ω => state ω = s) = (ρ s).toReal) :
    pmfConditionalProb μ p (fun ω => target (state ω)) =
      pmfProb ρ target := by
  classical
  have hstate_ratio : ∀ s : σ,
      pmfProb μ (fun ω => p ω ∧ state ω = s) / pmfProb μ p =
        (ρ s).toReal := by
    intro s
    have hs := hstate s
    rw [pmfConditionalProb_eq_inter_div_of_pos
      μ p (fun ω => state ω = s) hp_pos] at hs
    exact hs
  have hnum :
      pmfProb μ (fun ω => p ω ∧ target (state ω)) =
        ∑ s : σ,
          if target s then
            pmfProb μ (fun ω => p ω ∧ state ω = s)
          else 0 := by
    calc
      pmfProb μ (fun ω => p ω ∧ target (state ω))
          = ∑ s : σ,
              pmfProb μ
                (fun ω => (p ω ∧ target (state ω)) ∧ state ω = s) := by
            rw [pmfProb_eq_sum_state_inter μ
              (fun ω => p ω ∧ target (state ω)) state]
      _ = ∑ s : σ,
            if target s then
              pmfProb μ (fun ω => p ω ∧ state ω = s)
            else 0 := by
            refine Finset.sum_congr rfl ?_
            intro s _
            by_cases hs : target s
            · rw [if_pos hs]
              exact pmfProb_congr μ (by
                intro ω
                constructor
                · intro hω
                  exact ⟨hω.1.1, hω.2⟩
                · intro hω
                  exact ⟨⟨hω.1, by simpa [hω.2] using hs⟩, hω.2⟩)
            · rw [if_neg hs]
              rw [pmfProb_congr μ
                (p := fun ω => (p ω ∧ target (state ω)) ∧ state ω = s)
                (q := fun _ => False) (by
                intro ω
                constructor
                · intro hω
                  exact (hs (by simpa [hω.2] using hω.1.2)).elim
                · intro hω
                  cases hω)]
              simp [pmfProb, pmfExp]
  calc
    pmfConditionalProb μ p (fun ω => target (state ω))
        = pmfProb μ (fun ω => p ω ∧ target (state ω)) /
            pmfProb μ p := by
          rw [pmfConditionalProb_eq_inter_div_of_pos
            μ p (fun ω => target (state ω)) hp_pos]
    _ = (∑ s : σ,
          if target s then
            pmfProb μ (fun ω => p ω ∧ state ω = s)
          else 0) / pmfProb μ p := by
          rw [hnum]
    _ = ∑ s : σ,
          (if target s then
            pmfProb μ (fun ω => p ω ∧ state ω = s)
          else 0) / pmfProb μ p := by
          rw [Finset.sum_div]
    _ = ∑ s : σ, if target s then (ρ s).toReal else 0 := by
          refine Finset.sum_congr rfl ?_
          intro s _
          by_cases hs : target s
          · simp [hs, hstate_ratio s]
          · simp [hs]
    _ = pmfProb ρ target := by
          simp [pmfProb, pmfExp]

/--
Conditional negative dependence implies the pairwise negative-correlation
inequality `Pr[p and q] <= Pr[p] * Pr[q]`.
-/
theorem pmfProb_inter_le_mul_of_conditionalProb_le
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    (hq_pos : 0 < pmfProb μ q)
    (hcond : pmfConditionalProb μ q p ≤ pmfProb μ p) :
    pmfProb μ (fun a => p a ∧ q a) ≤
      pmfProb μ p * pmfProb μ q := by
  rw [pmfConditionalProb_eq_inter_div_of_pos μ q p hq_pos] at hcond
  rw [div_le_iff₀ hq_pos] at hcond
  simpa [and_comm, mul_comm] using hcond

/--
Pairwise negative correlation implies the corresponding conditional comparison
when the conditioning event has positive probability.
-/
theorem pmfConditionalProb_le_of_inter_le_mul
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    (hq_pos : 0 < pmfProb μ q)
    (hinter : pmfProb μ (fun a => p a ∧ q a) ≤
      pmfProb μ p * pmfProb μ q) :
    pmfConditionalProb μ q p ≤ pmfProb μ p := by
  rw [pmfConditionalProb_eq_inter_div_of_pos μ q p hq_pos]
  rw [div_le_iff₀ hq_pos]
  simpa [and_comm, mul_comm] using hinter

/--
Strict pairwise negative correlation implies the corresponding strict
conditional comparison when the conditioning event has positive probability.
-/
theorem pmfConditionalProb_lt_of_inter_lt_mul
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    (hq_pos : 0 < pmfProb μ q)
    (hinter : pmfProb μ (fun a => p a ∧ q a) <
      pmfProb μ p * pmfProb μ q) :
    pmfConditionalProb μ q p < pmfProb μ p := by
  rw [pmfConditionalProb_eq_inter_div_of_pos μ q p hq_pos]
  rw [div_lt_iff₀ hq_pos]
  simpa [and_comm, mul_comm] using hinter

/-- Probability of an event on a pair of independent PMF draws. -/
noncomputable def pmfPairProb {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (μ : PMF α) (ν : PMF β) (p : α × β → Prop) [DecidablePred p] : ℝ :=
  pmfPairExp μ ν (fun a b => if p (a, b) then 1 else 0)

/-- Pairwise indicator expectation on a product of two independent PMFs. -/
noncomputable def pmfPairIndicatorExp {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (μ : PMF α) (ν : PMF β) (p : α × β → Prop) [DecidablePred p]
    (f : α × β → ℝ) : ℝ :=
  pmfPairExp μ ν (fun a b => if p (a, b) then f (a, b) else 0)

@[simp] theorem pmfPairIndicatorExp_const_one {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (μ : PMF α) (ν : PMF β) (p : α × β → Prop) [DecidablePred p] :
    pmfPairIndicatorExp μ ν p (fun _ => 1) = pmfPairProb μ ν p := by
  rfl

/-- Conditional expectation on a product of two independent PMFs. -/
noncomputable def pmfPairConditionalExp {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (μ : PMF α) (ν : PMF β) (p : α × β → Prop) [DecidablePred p]
    (f : α × β → ℝ) : ℝ :=
  let q := pmfPairProb μ ν p
  if _h : q = 0 then 0 else pmfPairIndicatorExp μ ν p f / q

@[simp] theorem pmfPairConditionalExp_of_prob_zero {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (μ : PMF α) (ν : PMF β) (p : α × β → Prop) [DecidablePred p]
    (f : α × β → ℝ) (h : pmfPairProb μ ν p = 0) :
    pmfPairConditionalExp μ ν p f = 0 := by
  simp [pmfPairConditionalExp, h]

theorem pmfPairConditionalExp_eq_div_of_pos {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (μ : PMF α) (ν : PMF β) (p : α × β → Prop) [DecidablePred p]
    (f : α × β → ℝ) (h : 0 < pmfPairProb μ ν p) :
    pmfPairConditionalExp μ ν p f = pmfPairIndicatorExp μ ν p f / pmfPairProb μ ν p := by
  simp [pmfPairConditionalExp, h.ne']

theorem pmfPairConditionalExp_pos_iff {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (μ : PMF α) (ν : PMF β) (p : α × β → Prop) [DecidablePred p]
    (f : α × β → ℝ) (h : 0 < pmfPairProb μ ν p) :
    0 < pmfPairConditionalExp μ ν p f ↔ 0 < pmfPairIndicatorExp μ ν p f := by
  rw [pmfPairConditionalExp_eq_div_of_pos (μ := μ) (ν := ν) (p := p) (f := f) h]
  exact zero_lt_div_iff_pos_right h

end AppliedModelingLib
