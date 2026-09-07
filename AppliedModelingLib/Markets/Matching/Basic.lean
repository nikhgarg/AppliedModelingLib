import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Real.Basic

namespace AppliedModelingLib
namespace Matching

/-- A matching between Men and Women. -/
structure Assignment (M W : Type*) where
  m_match : M → Option W
  w_match : W → Option M
  consistent_m : ∀ m w, m_match m = some w ↔ w_match w = some m

namespace Assignment

/-- Swap the two sides of a matching. -/
def swap {M W : Type*} (mu : Assignment M W) : Assignment W M where
  m_match := mu.w_match
  w_match := mu.m_match
  consistent_m w m := (mu.consistent_m m w).symm

@[simp] theorem swap_m_match {M W : Type*} (mu : Assignment M W) (w : W) :
    mu.swap.m_match w = mu.w_match w := rfl

@[simp] theorem swap_w_match {M W : Type*} (mu : Assignment M W) (m : M) :
    mu.swap.w_match m = mu.m_match m := rfl

@[simp] theorem swap_swap {M W : Type*} (mu : Assignment M W) :
    mu.swap.swap = mu := by
  cases mu
  rfl

/-- Relabel the women side of a matching by an equivalence. -/
def relabelWomen {M W W' : Type*} (e : W ≃ W')
    (mu : Assignment M W) : Assignment M W' where
  m_match m := Option.map e (mu.m_match m)
  w_match w' := mu.w_match (e.symm w')
  consistent_m m w' := by
    constructor
    · intro h
      cases hmu : mu.m_match m with
      | none =>
          simp [hmu] at h
      | some w =>
          simp [hmu] at h
          subst w'
          simpa using (mu.consistent_m m w).1 hmu
    · intro h
      have hm : mu.m_match m = some (e.symm w') :=
        (mu.consistent_m m (e.symm w')).2 h
      simp [hm]

@[simp] theorem relabelWomen_m_match
    {M W W' : Type*} (e : W ≃ W') (mu : Assignment M W) (m : M) :
    (mu.relabelWomen e).m_match m = Option.map e (mu.m_match m) := rfl

@[simp] theorem relabelWomen_w_match
    {M W W' : Type*} (e : W ≃ W') (mu : Assignment M W) (w' : W') :
    (mu.relabelWomen e).w_match w' = mu.w_match (e.symm w') := rfl

@[simp] theorem relabelWomen_w_match_apply
    {M W W' : Type*} (e : W ≃ W') (mu : Assignment M W) (w : W) :
    (mu.relabelWomen e).w_match (e w) = mu.w_match w := by
  simp

/-- Two consistent matchings are equal when they give every man the same partner. -/
theorem ext_of_m_match {M W : Type*} {mu nu : Assignment M W}
    (h : ∀ m, mu.m_match m = nu.m_match m) : mu = nu := by
  cases mu with
  | mk mu_m mu_w mu_consistent =>
    cases nu with
    | mk nu_m nu_w nu_consistent =>
      simp only at h
      have hm : mu_m = nu_m := funext h
      subst nu_m
      have hw : mu_w = nu_w := by
        funext w
        cases hmu : mu_w w with
        | none =>
            cases hnu : nu_w w with
            | none => rfl
            | some m =>
                have hm_match : mu_m m = some w := (nu_consistent m w).2 hnu
                have : mu_w w = some m := (mu_consistent m w).1 hm_match
                rw [hmu] at this
                cases this
        | some m =>
            have hm_match : mu_m m = some w := (mu_consistent m w).2 hmu
            have hnu : nu_w w = some m := (nu_consistent m w).1 hm_match
            exact hnu.symm
      subst nu_w
      rfl

@[simp] theorem relabelWomen_symm_relabelWomen
    {M W W' : Type*} (e : W ≃ W') (mu : Assignment M W) :
    (mu.relabelWomen e).relabelWomen e.symm = mu := by
  apply ext_of_m_match
  intro m
  cases h : mu.m_match m <;> simp [h]

@[simp] theorem relabelWomen_relabelWomen_symm
    {M W W' : Type*} (e : W ≃ W') (mu : Assignment M W') :
    (mu.relabelWomen e.symm).relabelWomen e = mu := by
  apply ext_of_m_match
  intro m
  cases h : mu.m_match m <;> simp [h]

/-- Relabel the men side of a matching by an equivalence. -/
def relabelMen {M M' W : Type*} (e : M ≃ M')
    (mu : Assignment M W) : Assignment M' W :=
  (mu.swap.relabelWomen e).swap

@[simp] theorem relabelMen_m_match
    {M M' W : Type*} (e : M ≃ M') (mu : Assignment M W) (m' : M') :
    (mu.relabelMen e).m_match m' = mu.m_match (e.symm m') := rfl

@[simp] theorem relabelMen_w_match
    {M M' W : Type*} (e : M ≃ M') (mu : Assignment M W) (w : W) :
    (mu.relabelMen e).w_match w = Option.map e (mu.w_match w) := rfl

@[simp] theorem relabelMen_m_match_apply
    {M M' W : Type*} (e : M ≃ M') (mu : Assignment M W) (m : M) :
    (mu.relabelMen e).m_match (e m) = mu.m_match m := by
  simp

@[simp] theorem relabelMen_symm_relabelMen
    {M M' W : Type*} (e : M ≃ M') (mu : Assignment M W) :
    (mu.relabelMen e).relabelMen e.symm = mu := by
  apply ext_of_m_match
  intro m
  simp

@[simp] theorem relabelMen_relabelMen_symm
    {M M' W : Type*} (e : M ≃ M') (mu : Assignment M' W) :
    (mu.relabelMen e.symm).relabelMen e = mu := by
  apply ext_of_m_match
  intro m'
  simp

/-- If man `m` is matched to woman `w`, then woman `w` is matched to `m`. -/
theorem w_match_eq_some_of_m_match_eq_some {M W : Type*} {mu : Assignment M W}
    {m : M} {w : W} (h : mu.m_match m = some w) :
    mu.w_match w = some m :=
  (mu.consistent_m m w).1 h

/-- If no man is matched to woman `w`, then woman `w` is unmatched. -/
theorem w_match_eq_none_of_forall_m_match_ne_some {M W : Type*} {mu : Assignment M W}
    {w : W} (h : ∀ m, mu.m_match m ≠ some w) :
    mu.w_match w = none := by
  cases hw : mu.w_match w with
  | none => rfl
  | some m =>
      have hm : mu.m_match m = some w := (mu.consistent_m m w).2 hw
      exact False.elim (h m hm)

/-- The matched men and matched women of an assignment are in bijection. -/
noncomputable def matchedMenEquivWomen
    {M W : Type*} [DecidableEq M] [DecidableEq W]
    (mu : Assignment M W) :
    {m : M // mu.m_match m ≠ none} ≃ {w : W // mu.w_match w ≠ none} := by
  let toWoman : {m : M // mu.m_match m ≠ none} →
      {w : W // mu.w_match w ≠ none} := fun m =>
    let w := Option.get (mu.m_match m) (Option.ne_none_iff_isSome.mp m.2)
    ⟨w, by
      have hm : mu.m_match m = some w := (Option.some_get _).symm
      have hw : mu.w_match w = some m := (mu.consistent_m m w).1 hm
      simp [hw]⟩
  let toMan : {w : W // mu.w_match w ≠ none} →
      {m : M // mu.m_match m ≠ none} := fun w =>
    let m := Option.get (mu.w_match w) (Option.ne_none_iff_isSome.mp w.2)
    ⟨m, by
      have hw : mu.w_match w = some m := (Option.some_get _).symm
      have hm : mu.m_match m = some w := (mu.consistent_m m w).2 hw
      simp [hm]⟩
  refine { toFun := toWoman, invFun := toMan, left_inv := ?_, right_inv := ?_ }
  · intro m
    apply Subtype.ext
    let w := Option.get (mu.m_match m) (Option.ne_none_iff_isSome.mp m.2)
    have hm : mu.m_match m = some w := (Option.some_get _).symm
    have hw : mu.w_match w = some m := (mu.consistent_m m w).1 hm
    dsimp [toWoman, toMan]
    change (mu.w_match w).get _ = m
    simp [hw]
  · intro w
    apply Subtype.ext
    let m := Option.get (mu.w_match w) (Option.ne_none_iff_isSome.mp w.2)
    have hw : mu.w_match w = some m := (Option.some_get _).symm
    have hm : mu.m_match m = some w := (mu.consistent_m m w).2 hw
    dsimp [toWoman, toMan]
    change (mu.m_match m).get _ = w
    simp [hm]

/--
For an assignment between equally sized finite sides, the numbers of unmatched
men and women agree.
-/
theorem card_unmatched_men_eq_card_unmatched_women
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (mu : Assignment M W) (hcard : Fintype.card M = Fintype.card W) :
    Fintype.card {m : M // mu.m_match m = none} =
      Fintype.card {w : W // mu.w_match w = none} := by
  classical
  have hmatched :
      Fintype.card {m : M // mu.m_match m ≠ none} =
        Fintype.card {w : W // mu.w_match w ≠ none} :=
    Fintype.card_congr (matchedMenEquivWomen mu)
  calc
    Fintype.card {m : M // mu.m_match m = none} =
        Fintype.card M - Fintype.card {m : M // mu.m_match m ≠ none} := by
          simpa only [not_not] using
            (Fintype.card_subtype_compl fun m : M => mu.m_match m ≠ none)
    _ = Fintype.card W - Fintype.card {w : W // mu.w_match w ≠ none} := by
          rw [hcard, hmatched]
    _ = Fintype.card {w : W // mu.w_match w = none} := by
          symm
          simpa only [not_not] using
            (Fintype.card_subtype_compl fun w : W => mu.w_match w ≠ none)

/--
For finite equal-size sides, if every woman is matched then every man is matched.
-/
theorem m_complete_of_w_complete_of_card_eq
    {M W : Type*} [Fintype M] [Fintype W] (mu : Assignment M W)
    (hcard : Fintype.card M = Fintype.card W)
    (hwComplete : ∀ w, ∃ m, mu.w_match w = some m) :
    ∀ m, ∃ w, mu.m_match m = some w := by
  classical
  let f : W → M := fun w => Classical.choose (hwComplete w)
  have hf_spec : ∀ w, mu.w_match w = some (f w) := by
    intro w
    exact Classical.choose_spec (hwComplete w)
  have hinj : Function.Injective f := by
    intro w₁ w₂ hfw
    have hmatch₁ : mu.m_match (f w₁) = some w₁ :=
      (mu.consistent_m (f w₁) w₁).2 (hf_spec w₁)
    have hmatch₂ : mu.m_match (f w₂) = some w₂ :=
      (mu.consistent_m (f w₂) w₂).2 (hf_spec w₂)
    rw [hfw] at hmatch₁
    exact Option.some.inj (hmatch₁.symm.trans hmatch₂)
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, hcard.symm⟩
  intro m
  rcases hbij.2 m with ⟨w, hfw⟩
  refine ⟨w, ?_⟩
  have hwMatch : mu.w_match w = some m := by
    simpa [f, hfw] using hf_spec w
  exact (mu.consistent_m m w).2 hwMatch

/--
For finite equal-size sides, if every man is matched then every woman is matched.
-/
theorem w_complete_of_m_complete_of_card_eq
    {M W : Type*} [Fintype M] [Fintype W] (mu : Assignment M W)
    (hcard : Fintype.card M = Fintype.card W)
    (hmComplete : ∀ m, ∃ w, mu.m_match m = some w) :
    ∀ w, ∃ m, mu.w_match w = some m := by
  simpa [Assignment.swap] using
    m_complete_of_w_complete_of_card_eq (mu := mu.swap) hcard.symm hmComplete

end Assignment

/-- The value of a match for a man. 0 if unmatched. -/
def valM {M W : Type*} (val : M → W → ℝ) (m : M) (w : Option W) : ℝ :=
  match w with
  | none => 0
  | some w' => val m w'

/-- The value of a match for a woman. 0 if unmatched. -/
def valW {M W : Type*} (val : W → M → ℝ) (w : W) (m : Option M) : ℝ :=
  match m with
  | none => 0
  | some m' => val w m'

@[simp] theorem valM_relabelWomen_option_map
    {M W W' : Type*} (e : W ≃ W') (val_m : M → W → ℝ)
    (m : M) (wopt : Option W) :
    valM (fun m w' => val_m m (e.symm w')) m (Option.map e wopt) =
      valM val_m m wopt := by
  cases wopt <;> simp [valM]

@[simp] theorem valW_relabelWomen_apply
    {M W W' : Type*} (e : W ≃ W') (val_w : W → M → ℝ)
    (w : W) (mopt : Option M) :
    valW (fun w' m => val_w (e.symm w') m) (e w) mopt =
      valW val_w w mopt := by
  cases mopt <;> simp [valW]

@[simp] theorem valW_relabelWomen_symm_apply
    {M W W' : Type*} (e : W ≃ W') (val_w : W → M → ℝ)
    (w' : W') (mopt : Option M) :
    valW (fun w' m => val_w (e.symm w') m) w' mopt =
      valW val_w (e.symm w') mopt := by
  cases mopt <;> simp [valW]

/-- A matching is stable if it is individually rational and admits no blocking pairs. -/
def IsStable {M W : Type*} (val_m : M → W → ℝ) (val_w : W → M → ℝ) (mu : Assignment M W) : Prop :=
  (∀ m, 0 ≤ valM val_m m (mu.m_match m)) ∧
  (∀ w, 0 ≤ valW val_w w (mu.w_match w)) ∧
  (∀ m w, valM val_m m (mu.m_match m) < val_m m w →
          valW val_w w (mu.w_match w) < val_w w m → False)

/-- Stability is invariant under relabeling the women side of the market. -/
theorem isStable_relabelWomen_iff {M W W' : Type*}
    (e : W ≃ W') (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (mu : Assignment M W) :
    IsStable
        (fun m w' => val_m m (e.symm w'))
        (fun w' m => val_w (e.symm w') m)
        (mu.relabelWomen e) ↔
      IsStable val_m val_w mu := by
  have hman_val :
      ∀ m,
        valM (fun m w' => val_m m (e.symm w')) m
            ((mu.relabelWomen e).m_match m) =
          valM val_m m (mu.m_match m) := by
    intro m
    cases h : mu.m_match m <;> simp [Assignment.relabelWomen, h, valM]
  have hwoman_val :
      ∀ w,
        valW (fun w' m => val_w (e.symm w') m) (e w)
            ((mu.relabelWomen e).w_match (e w)) =
          valW val_w w (mu.w_match w) := by
    intro w
    cases h : mu.w_match w <;> simp [Assignment.relabelWomen, h, valW]
  have hwoman_val_symm :
      ∀ w',
        valW (fun w' m => val_w (e.symm w') m) w'
            ((mu.relabelWomen e).w_match w') =
          valW val_w (e.symm w') (mu.w_match (e.symm w')) := by
    intro w'
    cases h : mu.w_match (e.symm w') <;> simp [Assignment.relabelWomen, h, valW]
  constructor
  · intro h
    rcases h with ⟨hm_ir, hw_ir, hblock⟩
    refine ⟨?_, ?_, ?_⟩
    · intro m
      have hval := hm_ir m
      rw [hman_val m] at hval
      exact hval
    · intro w
      have hval := hw_ir (e w)
      rw [hwoman_val w] at hval
      exact hval
    · intro m w hm hw
      have hm' := hm
      rw [← hman_val m] at hm'
      have hw' := hw
      rw [← hwoman_val w] at hw'
      exact hblock m (e w)
        (by simpa using hm')
        (by simpa using hw')
  · intro h
    rcases h with ⟨hm_ir, hw_ir, hblock⟩
    refine ⟨?_, ?_, ?_⟩
    · intro m
      have hval := hm_ir m
      rw [← hman_val m] at hval
      exact hval
    · intro w'
      have hval := hw_ir (e.symm w')
      rw [← hwoman_val_symm w'] at hval
      exact hval
    · intro m w' hm hw
      have hm' := hm
      rw [hman_val m] at hm'
      have hw' := hw
      rw [hwoman_val_symm w'] at hw'
      exact hblock m (e.symm w')
        (by simpa using hm')
        (by simpa using hw')

/-- Stability is invariant under swapping the two sides of the market. -/
theorem isStable_swap_iff {M W : Type*}
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) (mu : Assignment M W) :
    IsStable val_w val_m mu.swap ↔ IsStable val_m val_w mu := by
  constructor
  · intro h
    rcases h with ⟨hw_ir, hm_ir, hblock⟩
    refine ⟨?_, ?_, ?_⟩
    · intro m
      simpa [Assignment.swap, valM, valW] using hm_ir m
    · intro w
      simpa [Assignment.swap, valM, valW] using hw_ir w
    · intro m w hm hw
      exact hblock w m
        (by simpa [Assignment.swap, valM, valW] using hw)
        (by simpa [Assignment.swap, valM, valW] using hm)
  · intro h
    rcases h with ⟨hm_ir, hw_ir, hblock⟩
    refine ⟨?_, ?_, ?_⟩
    · intro w
      simpa [Assignment.swap, valM, valW] using hw_ir w
    · intro m
      simpa [Assignment.swap, valM, valW] using hm_ir m
    · intro w m hw hm
      exact hblock m w
        (by simpa [Assignment.swap, valM, valW] using hm)
        (by simpa [Assignment.swap, valM, valW] using hw)

/-- Stability is invariant under relabeling the men side of the market. -/
theorem isStable_relabelMen_iff {M M' W : Type*}
    (e : M ≃ M') (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (mu : Assignment M W) :
    IsStable
        (fun m' w => val_m (e.symm m') w)
        (fun w m' => val_w w (e.symm m'))
        (mu.relabelMen e) ↔
      IsStable val_m val_w mu := by
  calc
    IsStable
        (fun m' w => val_m (e.symm m') w)
        (fun w m' => val_w w (e.symm m'))
        (mu.relabelMen e) ↔
      IsStable
        (fun w m' => val_w w (e.symm m'))
        (fun m' w => val_m (e.symm m') w)
        ((mu.relabelMen e).swap) := by
          exact (isStable_swap_iff _ _ _).symm
    _ ↔ IsStable val_w val_m mu.swap := by
          simpa [Assignment.relabelMen] using
            (isStable_relabelWomen_iff e val_w val_m mu.swap)
    _ ↔ IsStable val_m val_w mu := isStable_swap_iff _ _ _

end Matching
end AppliedModelingLib
